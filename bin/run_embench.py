#!/usr/bin/env python3

################################################################################
#
# Copyright 2020 OpenHW Group
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0
#
################################################################################
#
# run_embench : python script to fetch, set up, build and run EMBench
#               benchmarking suite on the present cores
#
# Author: Marton Teilgård
#  email: mateilga@silabs.com
#
# Written with Python 3.6.5 on RHEL 7.7.  Your python mileage may vary.
#
# Restriction:
#
#
################################################################################

import argparse
import logging
import os
import sys
import subprocess
import jinja2
import glob
import re


logging.basicConfig(level=logging.INFO)
logger = logging.getLogger('run_embench')

def main():

  check_python_version(3,6)

  parser = build_parser()
  args = parser.parse_args()

  if args.debug == 'YES':
    logger.setLevel(logging.DEBUG)

  if args.core == 'notset':
    logger.info('Must specify a core to benchmark')
    sys.exit(1)

  if args.cfg == 'default':
    core_config = 'corev32'
  elif args.cfg == 'pulp':
    core_config = 'corev32_pulp'
  elif args.cfg == 'pulp_fpu':
    core_config = 'corev32_pulp_fpu'
  elif args.cfg == 'pulp_fpu_zfinx':
    core_config = 'corev32_pulp_fpu_zfinx'
  else:
    logger.info(f"Invalid config selected: {args.cfg}, must be 'default', 'pulp', 'pulp_fpu' or 'pulp_fpu_zfinx'")
    sys.exit(1)

  if args.ccomp == 'notset':
    logger.info('Must specify a c compiler to benchmark')
    sys.exit(1)

  if args.type != 'speed' and args.type != 'size':
    logger.info(f"Invalid type selected: {args.type}, must be 'speed' or 'size'")
    sys.exit(1)

  if args.parallel == 'YES':
    parallel = True
  elif args.parallel == 'NO':
    parallel = False
  else:
    logger.info(f"Invalid 'parallel' option: {args.parallel}, must be 'YES' or 'NO'")
    sys.exit(1)

  if args.absolute == 'YES':
    absolute = True
  elif args.absolute == 'NO':
    absolute = False
  else:
    logger.info(f"Invalid 'absolute' option: {args.absolute}, must be 'YES' or 'NO'")
    sys.exit(1)

  if args.build_only == 'YES':
    build_only = True
  elif args.build_only == 'NO':
    build_only = False
  else:
    logger.info(f"Invalid 'build_only' option: {args.build_only}, must be 'YES' or 'NO'")
    sys.exit(1)

  paths = build_paths(args.core, core_config, args.logdir, args.builddir)

  logger.info("Starting EMBench for core-v-verif")
  logger.info(f"Benchmarking core: {args.core}")
  logger.info(f"Type of benchmark to run: {args.type}\n\n")

  # checking if there are existing configuration files
  if os.path.exists(paths['emcfg']):
    logger.info("EMBench repository checked out previously")
    logger.info("Cleaning results and skipping cfg copy")
    prebuilt = True
    # deleting existing build results
    try:
      subprocess.run(
        ['find', '.', '!', '-path', '.', '!', '-path', './README.md', '-delete'],
        cwd=paths['testsem']
      )
    except:
      logger.fatal('Failed to delete old build results')
  else:
    prebuilt = False

  # ----------------------------------------------------------------------------------------------
  # setup EMBench
  # ----------------------------------------------------------------------------------------------
  logger.info("Building Benchmark files")

  if not prebuilt:
    # copy core-native config
    logger.info(f"Copying EMBench config from {paths['libcfg']} to {paths['emcfg']}")
    try:
      subprocess.run(
        ['cp', '-R', paths['libcfg'], paths['emcfg']]
      )
    except:
      logger.fatal('EMBench config copy failed')

    # copy source files from bsp
    # Only done when testing speed, size benchmark is built without support
    # to matchEMBench baseline
    if args.type == 'speed':
      logger.info(f"Copying files from {paths['bsp']} to {paths['embrd']}")
      for file in os.listdir(paths['bsp']):
        if file.endswith('.S') or file.endswith('.c') or file.endswith('.h'):
          logger.info(f"Copying {file}")
          try:
            subprocess.run(['cp', paths['bsp']+'/'+file, paths['embrd']])
          except:
            logger.fatal(f"EMBench bsp copy of file {file} failed")

    # copy python module
    logger.info(f"Symlinking {paths['libpy']}/run_corev32.py to {paths['empy']}/run_corev32.py")
    try:
      subprocess.run(
        ['ln', '-s', f"{paths['libpy']}/run_corev32.py", f"{paths['empy']}/run_corev32.py"]
      )
    except:
      logger.fatal('EMBench python module copy failed')

    # copy python module
    logger.info(f"Copying {paths['libpy']}/benchmark_speed.py to {paths['embench']}/benchmark_speed.py")
    try:
      subprocess.run(
        ['cp', '-pf', f"{paths['libpy']}/benchmark_speed.py", f"{paths['embench']}/benchmark_speed.py"]
      )
    except:
      logger.fatal('EMBench benchmark_speed python script copy failed')

    logger.info(f"Copying {paths['libpy']}/benchmark_size.py to {paths['embench']}/benchmark_size.py")
    try:
      subprocess.run(
        ['cp', '-pf', f"{paths['libpy']}/benchmark_size.py", f"{paths['embench']}/benchmark_size.py"]
      )
    except:
      logger.fatal('EMBench benchmark_speed python script copy failed')

  # ----------------------------------------------------------------------------------------------
  # build benchmark object files (build_all.py)
  # ----------------------------------------------------------------------------------------------
  cmd = [f"{paths['embench']}/build_all.py",
         f'--arch={core_config}',
         f'--board={core_config}',
         f'--cflags=-I{paths["bsp"]}',
         f'--chip={args.type}',
         f'--cc={args.ccomp}',
         f'--warmup-heat=0',
         f'--cpu-mhz={args.cpu_mhz}',
         f'--ldflags=-T{paths["bsp"]}/link_gp_relax.ld',
         f'--builddir={args.builddir}',
         f'--logdir={args.logdir}',
         f'--timeout=15',
         '--clean']
  logger.info(f"Calling build script: {' '.join(cmd)}")
  try:
    res = subprocess.run(
      cmd,
      stdout=subprocess.PIPE,
      stderr=subprocess.PIPE,
      cwd=paths['embench']
    )
  except:
    logger.fatal('EMBench build failed')

  log_file = get_log_file(args.core, paths, 'build')
  fh = open(log_file, 'r')
  for line in fh.readlines():
    logger.info(line.rstrip())
  fh.close()

  if build_passed(res.stdout.decode('utf-8')):
    logger.info(f"EMBench for {args.type} built successfully")
  else:
    logger.fatal('EMBench build failed')
    sys.exit(1)

  # build test directory, copy and rename the executable test files, and generate yaml files
  # This is not done if the built files are for the size benchmark, as these are not able to run
  if args.type == 'speed':
    for folder in os.listdir(paths['emres']):
      # create test directory
      folder_ext = f"emb_{folder}"

      logger.debug(f"Creating folder {paths['testsem']}/{folder_ext}")
      try:
        subprocess.run(['mkdir', f"{paths['testsem']}/{folder_ext}"])
      except:
        logger.fatal(f"Failed to generate folder {paths['testsem']}/{folder_ext}")
        sys.exit(1)

      logger.debug(f"Creating folder {args.builddir}/{folder_ext}")
      try:
        subprocess.run(['mkdir', f"{args.builddir}/{folder_ext}"])
      except:
        logger.fatal(f"Failed to generate folder {args.builddir}/{folder_ext}")
        sys.exit(1)

      # copy test files into the tests/programs/embench directories
      for file in os.listdir(f"{paths['emres']}/{folder}"):
        if not file.endswith('.o'):
          logger.debug(f"Copying file {file}")
          try:
            subprocess.run(['cp', f"{paths['emres']}/{folder}/{file}", f"{args.builddir}/{folder_ext}/emb_{file}.elf"])
          except:
            logger.fatal(f"Copying file {file} to {args.builddir}/{folder_ext}/ failed")
            sys.exit(1)

          break

      # generate test.yaml
      logger.debug(f"Rendering template: test.yaml.j2 for test: {folder_ext}")
      generate_test_yaml(f"{paths['testsem']}/{folder_ext}", folder_ext)


  if build_only:
    logger.info("Build only selected, exiting")
    sys.exit()

  # ----------------------------------------------------------------------------------------------
  # run benchmark script (benchmark_speed.py or benchmark_size.py)
  # ----------------------------------------------------------------------------------------------
  logger.info(f"Starting benchmarking of {args.type}")

  if args.type == 'speed':
    arglist = [f"{paths['embench']}/benchmark_speed.py",
               f'--target-module=run_corev32',
               f'-cfg={args.cfg}',
               f'--cpu-mhz={args.cpu_mhz}',
               f'--make-path={paths["make"]}',
               f'--builddir={args.builddir}',
               f'--logdir={args.logdir}',
               f'--timeout={args.timeout}',
               f'--simulator={args.simulator}']
    if parallel:
      arglist.append(f'--sim-parallel')
  else:
    arglist = [f"{paths['embench']}/benchmark_size.py",
               f'--builddir={args.builddir}',
               f'--logdir={args.logdir}']

  if absolute:
    arglist.append(f'--absolute')

  try:
    logger.info(f"Running: {' '.join(arglist)}")
    res = subprocess.run(
      arglist,
      stdout=subprocess.PIPE,
      stderr=subprocess.STDOUT,
      cwd=paths['embench'],
      )

  except:
      logger.fatal(f"EMBench script benchmark_{args.type}.py failed")
      sys.exit(1)

  logger.info('Complete with benchmark run')

  # Check if benchmark run succeeded
  if not run_passed(res.stdout.decode('utf-8'), args.type):
    logger.fatal(f"EMBench benchmark run failed")
    log_file = get_log_file(args.core, paths, args.type)
    if log_file:
        logger.info('For more debug check EMBench log: {}'.format(log_file))
    sys.exit(1)

  # Benchmark run succeeded, print logfile
  log_file = get_log_file(args.core, paths, args.type)
  fh = open(log_file, 'r')
  for line in fh.readlines():
    logger.info(line.rstrip())
  fh.close()

  # Check results if a target was applied
  if check_result(res.stdout.decode('utf-8'), args.target, args.type) and args.target != 0:
    logger.info(f"Benchmark run met target")
  elif args.target != 0:
    logger.info(f"Benchmark run failed to meet the target: {args.target}")


###############################################################################
# End of Main

def build_parser():
  """Build a parser for all the arguments"""
  parser = argparse.ArgumentParser(description='Clone and run EMBench', formatter_class=argparse.RawTextHelpFormatter)

  parser.add_argument(
    '-c',
    '--core',
    default='notset',
    help='Core to benchmark'
  )

  parser.add_argument(
    '-cfg',
    default='default',
    help='Core configuration to benchmark'
  )

  parser.add_argument(
    '-cc',
    '--ccomp',
    default='notset',
    help='C compiler for benchmark'
  )

  parser.add_argument(
    '--absolute',
    default='NO',
    help=(
      'Set this option to "YES" to report absolute numbers\n'+
      'makefile alias: EMB_ABSOLUTE'
    )
  )

  parser.add_argument(
    '--parallel',
    default='NO',
    help=(
      'Set this option to "YES" to launch simulation in parallel\n'+
      'makefile alias: EMB_PARALLEL'
    )
  )

  parser.add_argument(
    '-t',
    '--type',
    default='speed',
    help=(
      'What benchmark to run. Valid options: speed, size\n'+
      'Default option: speed \n'+
      'NOTE: type affects build configuration!\n'+
      'makefile alias: EMB_TYPE'
    )
  )

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
    '-b',
    '--build-only',
    default='NO',
    help=(
      'Set this option to "YES" to only build the benchmarks.\n'+
      'Type option is still honored\n'+
      'makefile alias: EMB_BUILD_ONLY'
    )
  )

  parser.add_argument(
    '-tgt',
    '--target',
    type=float,
    default=0,
    help=(
      'Set a target for your EMBench score\n'+
      'Benchmark run will fail if target is not met\n'+
      'If no target is set, no checking is done\n'+
      'makefile alias: EMB_TARGET'
    )
  )

  parser.add_argument(
    '-f',
    '--cpu-mhz',
    default=1,
    help=(
      'Set the core frequency in MHz.\n'+
      'Default is 1 MHz\n'+
      'makefile alias: EMB_CPU_MHZ'
    )
  )

  parser.add_argument(
    '--timeout',
    default=3600,
    help = (
        'Timeout for each simulation run in seconds\n'+
        'makefile alias: EMB_TIMEOUT',
    )
  )

  parser.add_argument(
    '-sim',
    '--simulator',
    default='xrun',
    help=(
      'Simulator to run the benchmarks\n'+
      'makefile alias: SIMULATOR'
    )
  )

  parser.add_argument(
    '-d',
    '--debug',
    default='NO',
    help=(
      'Set this option to "YES" to increase verbosity of the script\n'+
      'makefile alias: EMB_DEBUG'
    )
  )

  return parser

def build_paths(core, core_config, logdir, builddir):
  """map out necessary paths"""
  paths = dict()
  paths['cver'] = os.path.abspath(os.path.join(os.path.dirname(__file__), os.pardir))
  paths['core'] = paths['cver'] + '/' + core
  paths['libcfg'] = paths['core'] + '/tests/embench/config/' + core_config
  paths['libpy'] = paths['core'] + '/tests/embench/pylib'
  paths['vlib'] = paths['core'] + '/vendor_lib'
  paths['emb_logs'] = logdir
  paths['make'] = paths['core'] + '/sim/uvmt'
  paths['embench'] = paths['vlib'] + '/embench'
  paths['emcfg'] = paths['embench'] + '/config/' + core_config
  paths['empy'] = paths['embench'] + '/pylib'
  paths['embrd'] = paths['emcfg'] + '/boards/' + core_config
  paths['emres'] = builddir + '/src'
  paths['bsp'] = paths['core'] + '/bsp'
  paths['testsem'] = paths['core'] + '/tests/programs/embench'

  return paths

def generate_test_yaml(folder, test_name):
  env = jinja2.Environment(loader=jinja2.FileSystemLoader(os.path.join(os.path.dirname(__file__),
                                                        'templates')), trim_blocks=True)
  template = env.get_template('embench_test.yaml.j2')

  out = open(f"{folder}/test.yaml", 'w')
  out.write(template.render(name=test_name))
  out.close()

def build_passed(stdout_str):
  if re.search('All benchmarks built successfully', stdout_str, re.S):
    return True
  else:
    return False

def run_passed(stdout_str, type):
  if type == 'speed':
    if re.search('All benchmarks run successfully', stdout_str, re.S):
      return True
    else:
      return False
  else: #size
    if re.search('All benchmarks sized successfully', stdout_str, re.S):
      return True
    else:
      return False

def check_result(stdout_str, tgt, type):
  #find result in numeric value and compare to target
  rcstr = re.search('Geometric mean *(\d+)[.](\d+)', stdout_str, re.S)
  result = int(rcstr.group(1)) + (int(rcstr.group(2)) * 0.01)

  if type == 'speed':
    if (tgt == 0) or (result >= tgt):
      return True
    else:
      return False
  else:
    if (tgt == 0) or (result <= tgt):
      return True
    else:
      return False


# Make sure we have new enough python
def check_python_version(major, minor):
    """Check the python version is at least {major}.{minor}."""
    if ((sys.version_info[0] < major)
        or ((sys.version_info[0] == major) and (sys.version_info[1] < minor))):
        log.error('ERROR: Requires Python {mjr}.{mnr} or later'.format(mjr=major, mnr=minor))
        sys.exit(1)

def get_log_file(core, paths, log_type):
    '''Find the log file from EMBench by looking for the latest touched file'''
    last_mtime = 0
    file = None
    for f in glob.glob(os.path.join(paths['emb_logs'], '{}-*.log'.format(log_type))):
        if last_mtime < os.stat(f).st_mtime:
            last_mtime = os.stat(f).st_mtime
            file = f

    return file

#run main
if __name__ == '__main__':
    sys.exit(main())
