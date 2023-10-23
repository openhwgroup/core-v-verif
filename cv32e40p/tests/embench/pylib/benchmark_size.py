#!/usr/bin/env python3

# Script to benchmark size

# Copyright (C) 2017, 2019 Embecosm Limited
#
# Contributor: Graham Markall <graham.markall@embecosm.com>
# Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>
#
# This file is part of Embench.

# SPDX-License-Identifier: GPL-3.0-or-later

"""
Compute the size benchmark for a set of compiled Embench programs.
"""

import argparse
import codecs
import os
import sys

from json import loads
from elftools.elf.elffile import ELFFile

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


def build_parser():
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
    # List arguments are empty by default, a user specified value then takes
    # precedence. If the list is empty after parsing, then we can install a
    # default value.
    parser.add_argument(
        '--text',
        type=str,
        default=[],
        action='append',
        help='Section name(s) containing code'
    )
    parser.add_argument(
        '--data',
        type=str,
        default=[],
        action='append',
        help='Section name(s) containing non-zero initialized writable data'
    )
    parser.add_argument(
        '--rodata',
        type=str,
        default=[],
        action='append',
        help='Section name(s) containing read only data'
    )
    parser.add_argument(
        '--bss',
        type=str,
        default=[],
        action='append',
        help='Section name(s) containing zero initialized writable data'
    )
    parser.add_argument(
        '--metric',
        type=str,
        default=[],
        action='append',
        choices=['text', 'rodata', 'data', 'bss'],
        help='Sections to include in metric: one or more of "text", "rodata", '
        + '"data" or "bss". Default "text"',
    )

    return parser


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

    # Sort out the list of section names to use
    gp['secnames'] = dict()

    for argname in ['text', 'rodata', 'data', 'bss']:
        secnames = getattr(args, argname)
        if secnames:
            gp['secnames'][argname] = secnames
        else:
            gp['secnames'][argname] = ['.' + argname]

    # If no sections are specified, we just use .text
    if args.metric:
        gp['metric'] = args.metric
    else:
        gp['metric'] = ['text']

def get_section_group_by_name(elf, name):
    """ Get a group of sections matching with the provided name from the file.
        Return None if no such section exists.
    """
    # The first time this method is called, construct a name to number
    # mapping
    #
    if elf._section_name_map is None:
        elf._section_name_map = {}
        for i, sec in enumerate(elf.iter_sections()):
            elf._section_name_map[sec.name] = i

    sec_group = {}
    for i, sec in enumerate(elf.iter_sections()):
        if sec.name.startswith(name):
            secnum = elf._section_name_map.get(sec.name, None)
            sec_group[sec.name] = elf.get_section(secnum)

    return None if sec_group is None else sec_group

def benchmark_size(bench, metrics):
    """Compute the total size of the desired sections in a benchmark.  Returns
       the size in bytes, which may be zero if the section wasn't found."""
    appexe = os.path.join(gp['bd_benchdir'], bench, bench)
    sec_sizes = {}

    # If the benchmark failed to build, then return a 0 size instead of
    # crashing when failing to open the file.
    if not os.path.exists(appexe):
        return {}

    with open(appexe, 'rb') as fileh:
        elf = ELFFile(fileh)
        for metric in metrics:
            for secname in gp['secnames'][metric]:
                sec_sizes[secname] = 0
                sections = get_section_group_by_name(elf, secname)
                if sections:
                    for sec in sections:
                        sec_sizes[secname] += sections[sec]['sh_size']

    # Return the section (group) size
    return sec_sizes


def collect_data(benchmarks):
    """Collect and log all the raw and optionally relative data associated with
       the list of benchmarks supplied in the "benchmarks" argument. Return
       the raw data and relative data as a list.  The raw data may be empty if
       there is a failure. The relative data will be empty if only absolute
       results have been requested.

       Note that we manually generate the JSON output, rather than using the
       dumps method, because the result will be manually edited, and we want
       to guarantee the layout."""

    # Baseline data is held external to the script. Import it here.
    size_baseline = os.path.join(gp['baseline_dir'], 'size.json')
    with open(size_baseline) as fileh:
        baseline_all = loads(fileh.read())

    # Compute the baseline data we need
    baseline = {}

    for bench, data in baseline_all.items():
        baseline[bench] = 0
        for sec in gp['metric']:
            baseline[bench] += data[sec]

    successful = True
    raw_section_data = {}
    raw_totals = {}
    rel_data = {}

    # Collect data
    all_metrics = ['text', 'rodata', 'data', 'bss']
    for bench in benchmarks:
        if gp['output_format'] == output_format.BASELINE:
            raw_section_data[bench] = benchmark_size(bench, all_metrics)
        else:
            raw_section_data[bench] = benchmark_size(bench, gp['metric'])
        raw_totals[bench] = sum(raw_section_data[bench].values())

        # Want relative results (the default). If baseline is zero, just
        # use 0.0 as the value.  Note this is inverted compared to the
        # speed benchmark, so SMALL is good.
        if baseline[bench] > 0:
            rel_data[bench] = raw_totals[bench] / baseline[bench]
        else:
            rel_data[bench] = 0.0

    # Output it
    if gp['output_format'] == output_format.JSON:
        log.info('  "size results" :')
        log.info('  { "detailed size results" :')
        for bench in benchmarks:
            res_output = ''
            if gp['absolute']:
                res_output = f'{raw_totals[bench]}'
            else:
                res_output = f'{rel_data[bench]:.2f}'

            if bench == benchmarks[0]:
                log.info('    { ' + f'"{bench}" : {res_output},')
            elif bench == benchmarks[-1]:
                log.info(f'      "{bench}" : {res_output}')
            else:
                log.info(f'      "{bench}" : {res_output},')

        log.info('    },')
    elif gp['output_format'] == output_format.TEXT:
        log.info('Benchmark            Size    Bytes')
        log.info('---------           -----    -----')
        for bench in benchmarks:
            res_output_abs = ''
            res_output_rel = ''
            res_output_abs = f'{raw_totals[bench]:8,}'
            res_output_rel = f'  {rel_data[bench]:6.2f}'
            log.info(f'{bench:15}  {res_output_rel:8} {res_output_abs:8}')
    elif gp['output_format'] == output_format.BASELINE:
        log.info('{')
        for bench in benchmarks:
            res_output = ''
            for metric in all_metrics:
                if metric != all_metrics[0]:
                    res_output += ',\n'

                value = 0
                secname = '.' + metric
                if raw_section_data[bench].get(secname):
                    value = raw_section_data[bench][secname]
                res_output += f'    "{metric}" : {value}'

            if bench == benchmarks[-1]:
                log.info(f'  "{bench}" : {{\n{res_output}\n  }}')
            else:
                log.info(f'  "{bench}" : {{\n{res_output}\n  }},')
        log.info('}')

    if successful:
        return raw_totals, rel_data

    # Otherwise failure return
    return [], []


def main():
    """Main program driving measurement of benchmark size"""
    # Establish the root directory of the repository, since we know this file is
    # in that directory.
    gp['rootdir'] = os.path.abspath(os.path.dirname(__file__))

    # Parse arguments using standard technology
    parser = build_parser()
    args = parser.parse_args()

    # Establish logging
    setup_logging(args.logdir, 'size')
    log_args(args)

    # Check args are OK (have to have logging and build directory set up first)
    validate_args(args)

    # Find the benchmarks
    benchmarks = find_benchmarks()
    log_benchmarks(benchmarks)

    # Collect the size data for the benchmarks
    raw_data, rel_data = collect_data(benchmarks)

    # We can't compute geometric SD on the fly, so we need to collect all the
    # data and then process it in two passes. We could do the first processing
    # as we collect the data, but it is clearer to do the three things
    # separately. Given the size of datasets with which we are concerned the
    # compute overhead is not significant.
    if raw_data:
        if gp['output_format'] != output_format.BASELINE:
            opt_comma = ',' if args.json_comma else ''
            embench_stats(benchmarks, raw_data, rel_data, 'size', opt_comma)
            log.info('All benchmarks sized successfully')
    else:
        log.info('ERROR: Failed to compute size benchmarks')
        sys.exit(1)


# Make sure we have new enough Python and only run if this is the main package

check_python_version(3, 6)
if __name__ == '__main__':
    sys.exit(main())
