#!/usr/bin/env python3

# Script to benchmark execution speed.

# Copyright (C) 2017, 2019 Embecosm Limited
#
# Contributor: Graham Markall <graham.markall@embecosm.com>
# Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>
#
# This file is part of Embench.

# SPDX-License-Identifier: GPL-3.0-or-later

"""
Benchmark speed.

This version is suitable when using a version of GDB which can launch a GDB
server to use as a target.
"""

import argparse
import importlib
import os
import subprocess
import sys
import threading
import queue
import time

from json import loads

sys.path.append(
    os.path.join(os.path.abspath(os.path.dirname(__file__)), 'pylib')
)

from embench_core import check_python_version
from embench_core import log
from embench_core import gp
from embench_core import setup_logging
from embench_core import log_args
from embench_core import find_benchmarks
from embench_core import log_benchmarks
from embench_core import embench_stats
from embench_core import output_format


def get_common_args():
    """Build a parser for all the arguments"""
    parser = argparse.ArgumentParser(description='Compute the size benchmark')

    parser.add_argument(
        '--builddir',
        type=str,
        default='bd',
        help='Directory holding all the binaries',
    )
    parser.add_argument(
        '--logdir',
        type=str,
        default='logs',
        help='Directory in which to store logs',
    )
    parser.add_argument(
        '--baselinedir',
        type=str,
        default='baseline-data',
        help='Directory which contains baseline data',
    )
    parser.add_argument(
        '--absolute',
        action='store_true',
        help='Specify to show absolute results',
    )
    parser.add_argument(
        '--relative',
        dest='absolute',
        action='store_false',
        help='Specify to show relative results (the default)',
    )
    parser.add_argument(
        '--json-output',
        dest='output_format',
        action='store_const',
        const=output_format.JSON,
        help='Specify to output in JSON format',
    )
    parser.add_argument(
        '--text-output',
        dest='output_format',
        action='store_const',
        const=output_format.TEXT,
        help='Specify to output as plain text (the default)',
    )
    parser.add_argument(
        '--baseline-output',
        dest='output_format',
        action='store_const',
        const=output_format.BASELINE,
        help='Specify to output in a format suitable for use as a baseline'
    )
    parser.add_argument(
        '--json-comma',
        action='store_true',
        help='Specify to append a comma to the JSON output',
    )
    parser.add_argument(
        '--no-json-comma',
        dest='json_comma',
        action='store_false',
        help='Specify to not append a comma to the JSON output',
    )
    parser.add_argument(
        '--target-module',
        type=str,
        required=True,
        help='Python module with routines to run benchmarks',
    )
    parser.add_argument(
        '--timeout',
        type=int,
        default=30,
        help='Timeout used for running each benchmark program'
    )
    parser.add_argument(
        '--sim-parallel',
        action='store_true',
        default=False,
        help='Launch all benchmarks in parallel'
    )
    parser.add_argument(
        '--sim-serial',
        dest='sim_parallel',
        action='store_false',
        help='Launch all benchmarks in series (the default)'
    )

    return parser.parse_known_args()


def validate_args(args):
    """Check that supplied args are all valid. By definition logging is
       working when we get here.

       Update the gp dictionary with all the useful info"""
    if os.path.isabs(args.builddir):
        gp['bd'] = args.builddir
    else:
        gp['bd'] = os.path.join(gp['rootdir'], args.builddir)

    if not os.path.isdir(gp['bd']):
        log.error(f'ERROR: build directory {gp["bd"]} not found: exiting')
        sys.exit(1)

    if not os.access(gp['bd'], os.R_OK):
        log.error(f'ERROR: Unable to read build directory {gp["bd"]}: exiting')
        sys.exit(1)

    if os.path.isabs(args.baselinedir):
        gp['baseline_dir'] = args.baselinedir
    else:
        gp['baseline_dir'] = os.path.join(gp['rootdir'], args.baselinedir)

    gp['absolute'] = args.absolute
    if args.output_format:
        gp['output_format'] = args.output_format
    else:
        gp['output_format'] = output_format.TEXT

    gp['timeout'] = args.timeout
    gp['sim_parallel'] = args.sim_parallel

    try:
        newmodule = importlib.import_module(args.target_module)
    except ImportError as error:
        log.error(
            f'ERROR: Target module import failure: {error}: exiting'
        )
        sys.exit(1)

    globals()['get_target_args'] = newmodule.get_target_args
    globals()['build_benchmark_cmd'] = newmodule.build_benchmark_cmd
    globals()['decode_results'] = newmodule.decode_results


def benchmark_speed(bench, target_args):
    """Time the benchmark.  "target_args" is a namespace of arguments
       specific to the target.  Result is a time in milliseconds, or zero on
       failure.

       For the parallel option, this method must be thread-safe."""
    succeeded = True
    appdir = os.path.join(gp['bd_benchdir'], bench)
    appexe = os.path.join(appdir, bench)

    if os.path.isfile(appexe):
        arglist = build_benchmark_cmd(bench, target_args)
        try:
            res = subprocess.run(
                arglist,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                cwd=appdir,
                timeout=gp['timeout'],
            )
            if res.returncode != 0:
                log.warning(f'Warning: Run of {bench} failed.')
                succeeded = False
        except subprocess.TimeoutExpired:
            log.warning(f'Warning: Run of {bench} timed out.')
            succeeded = False
    else:
        log.warning(f'Warning: {bench} executable not found.')
        succeeded = False

    # Process results
    if succeeded:
        exec_time = decode_results(
            res.stdout.decode('utf-8'), res.stderr.decode('utf-8')
        )
        succeeded = exec_time > 0

    if succeeded:
        return exec_time
    else:
        for arg in arglist:
            if arg == arglist[0]:
                comm = arg
            elif arg == '-ex':
                comm += ' ' + arg
            else:
                comm += " '" + arg + "'"

        log.debug('Args to subprocess:')
        log.debug(f'{comm}')
        if 'res' in locals():
            log.debug(res.stdout.decode('utf-8'))
            log.debug(res.stderr.decode('utf-8'))
        return 0.0

def run_threads(bench, target_args, data_collect_q):
    item = benchmark_speed(bench, target_args)
    data_collect_q.put_nowait([bench, item])
    
def collect_data(benchmarks, remnant):
    """Collect and log all the raw and optionally relative data associated with
       the list of benchmarks supplied in the "benchmarks" argument. "remant"
       is left over args from the command line, which may be useful to the
       benchmark running procs.

       Return the raw data and relative data as a list.  The raw data may be
       empty if there is a failure. The relative data will be empty if only
       absolute results have been requested."""

    # Baseline data is held external to the script. Import it here.
    speed_baseline = os.path.join(gp['baseline_dir'], 'speed.json')
    with open(speed_baseline) as fileh:
        baseline = loads(fileh.read())

    # Parse target specific args
    target_args = get_target_args(remnant)

    # Collect data
    successful = True
    raw_data = {}
    rel_data = {}

    # Run the benchmarks in parallel
    if gp['sim_parallel']:
        collect_data_q = queue.Queue()
        benchmark_threads = list()
        for bench in benchmarks:
            curr_thread = threading.Thread(target=run_threads, args=(bench, target_args, collect_data_q))
            benchmark_threads.append(curr_thread)
            curr_thread.start()
            time.sleep(30)
        # Join threads
        for thd in benchmark_threads:
            thd.join() 
        # All thread have returned
        # Go through Q and make sure all benchmarks returned
        while not collect_data_q.empty():
            [bench_id, raw_score] = collect_data_q.get()
            raw_data[bench_id] = raw_score
    # Run the benchmarks in serial
    else: 
        for bench in benchmarks:
            raw_data[bench] = benchmark_speed(bench, target_args)

    for bench in benchmarks:
        rel_data[bench] = 0.0
        if raw_data[bench] == 0.0:
            del raw_data[bench]
            del rel_data[bench]
            successful = False
        else:
            rel_data[bench] = baseline[bench] / raw_data[bench]

    # Output it
    if gp['output_format'] == output_format.JSON:
        log.info('  "speed results" :')
        log.info('  { "detailed speed results" :')
        for bench in benchmarks:
            output = ''
            if raw_data[bench] != 0.0:
                if gp['absolute']:
                    output = f'{round(raw_data[bench])}'
                else:
                    output = f'{rel_data[bench]:.2f}'

                if bench == benchmarks[0]:
                    log.info(f'    {{ ' + f'"{bench}" : {output},')
                elif bench == benchmarks[-1]:
                    log.info(f'      "{bench}" : {output}')
                else:
                    log.info(f'      "{bench}" : {output},')
        log.info('    },')
    elif gp['output_format'] == output_format.TEXT:
        log.info('Benchmark           Speed   Cycles')
        log.info('---------           -----   ------')
        for bench in benchmarks:
            output_rel = ''
            output_abs = ''
            if (bench in raw_data and raw_data[bench] != 0.0):
                output_rel = f'  {rel_data[bench]:6.2f}'
                output_abs = f'{round(raw_data[bench]):8,}'
            # Want relative results (the default). Only use non-zero values.
            log.info(f'{bench:15}  {output_rel:8} {output_abs:8}')
    elif gp['output_format'] == output_format.BASELINE:
        log.info('{')
        for bench in benchmarks:
            if bench == benchmarks[-1]:
                log.info(f'  "{bench}" : {raw_data[bench]}')
            else:
                log.info(f'  "{bench}" : {raw_data[bench]},')
        log.info('}')

    if successful:
        return raw_data, rel_data

    # Otherwise failure return
    return [], []


def main():
    """Main program driving measurement of benchmark size"""
    # Establish the root directory of the repository, since we know this file is
    # in that directory.
    gp['rootdir'] = os.path.abspath(os.path.dirname(__file__))

    # Parse arguments common to all speed testers, and get list of those
    # remaining.
    args, remnant = get_common_args()

    # Establish logging
    setup_logging(args.logdir, 'speed')
    log_args(args)

    # Check args are OK (have to have logging and build directory set up first)
    validate_args(args)

    # Find the benchmarks
    benchmarks = find_benchmarks()
    log_benchmarks(benchmarks)

    # Collect the speed data for the benchmarks. Pass any remaining args.
    raw_data, rel_data = collect_data(benchmarks, remnant)

    # We can't compute geometric SD on the fly, so we need to collect all the
    # data and then process it in two passes. We could do the first processing
    # as we collect the data, but it is clearer to do the three things
    # separately. Given the size of datasets with which we are concerned the
    # compute overhead is not significant.
    if raw_data:
        if gp['output_format'] != output_format.BASELINE:
            opt_comma = ',' if args.json_comma else ''
            embench_stats(benchmarks, raw_data, rel_data, 'speed', opt_comma)
            log.info('All benchmarks run successfully')
    else:
        log.info('ERROR: Failed to compute speed benchmarks')
        sys.exit(1)


# Make sure we have new enough Python and only run if this is the main package

check_python_version(3, 6)
if __name__ == '__main__':
    sys.exit(main())
