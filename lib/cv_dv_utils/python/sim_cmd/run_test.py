## ----------------------------------------------------------------------------
##Copyright 2023 CEA*
##*Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
##
##Licensed under the Apache License, Version 2.0 (the "License");
##you may not use this file except in compliance with the License.
##You may obtain a copy of the License at
##
##    http://www.apache.org/licenses/LICENSE-2.0
##
##Unless required by applicable law or agreed to in writing, software
##distributed under the License is distributed on an "AS IS" BASIS,
##WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
##See the License for the specific language governing permissions and
##limitations under the License.
##[END OF HEADER]
## ----------------------------------------------------------------------------



import argparse
import os
import yaml

parser = argparse.ArgumentParser(description='compile options')
parser.add_argument('--yaml'     ,dest='yaml_file', type=str, help='Top YAML with compile and simulation options')
parser.add_argument('--test_name',dest='test_name', type=str, help='Name of the test')
parser.add_argument('--seed'     , dest='seed',      type=int, help='random seed ex: 3452363, default 1')
parser.add_argument('--debug'    , dest='debug',     type=str, help='UVM_LOW/MEDIUM/HIGH/FULL/DEBUG, default LOW')
parser.add_argument('--batch'    , dest='batch',     type=int, help='1: batch mode, 0:gui default, 1')
parser.add_argument('--dump'     , dest='dump',      type=int, help='1: all signals are logged, 0: nothing is looged, default 1') #FIXME
parser.add_argument('--coverage' , dest='coverage',   type=int, help='Activate coverage')
parser.add_argument('--stdout'   , dest='stdout', type=int, help='1: stdout 0: nostdout')
parser.add_argument('--outdir'   , dest='outdir', type=str, help='output dirctory de fault "output"')

args = parser.parse_args()

def get_cmd_opt(yaml_file):
  with open(yaml_file, 'r') as yaml_top:
     sim_yaml = yaml.safe_load(yaml_top)
  
  for entry in sim_yaml: 
      if entry['tool'] == "questa":
          cmd       = "vsim"
          tool      = "questa"
      elif entry['tool'] == "vcs":
          cmd       = "./vcs"
          tool      = "vcs"
      if 'sim' in entry:
        sim     = entry['sim']
      else: 
        sim = ""

      if 'sim_option' in sim:
        sim_opt = sim['sim_option']
      else:
        sim_opt = ""

  sim_cmd_opt = ""
  if tool == "questa":
    sim_cmd_opt = "{} {}".format(cmd, sim_opt)
    return sim_cmd_opt

def run_test(test_name, seed, debug, batch, dump, coverage, stdout, outdir, vsim_opt):

   if outdir == None: 
      outdir = "output"

   
   if seed == None: 
      seed = 1
   
   if debug == None: 
      debug = "UVM_LOW"
  
   if batch == None: 
      batch = 1 
   
   if dump == None: 
      dump = 1 
   
   if batch == 1:
     batchstr = "-c"
   else:
     batchstr = "-visualizer"
   
   if dump == 1:
     wlfstr  = "-wlf {}/{}_{}.wlf".format(outdir, test_name, seed)
     dumpstr = ""
   else:
     dumpt = ""
     wlfstr  = ""

   if stdout == None:
       stdout = 1

   if stdout == 0:
       stdoutstr = ">"
   else:
       stdoutstr = "-l"
  
   if os.path.isdir("{}".format(outdir)) == False:
     os.system("mkdir {}".format(outdir))
   
   if coverage == 1:
     ucdbfile    = "\"coverage save -onexit {}/{}_{}.ucdb\"".format(outdir, test_name, seed)
     coveragestr = "-do {}".format(ucdbfile)
     coverageopt = "-coverage -assertdebug"
   else:
     coveragestr = ""
     coverageopt = ""

   os.system("{} {} {} {} -sv_seed {} +UVM_VERBOSITY={} +UVM_TESTNAME={} {} {}/{}_{}.log {}".format(vsim_opt,  batchstr, dumpstr, coverageopt, seed, debug, test_name, stdoutstr, outdir, test_name, seed, wlfstr))

option_ok = 1
if args.yaml_file == None:
   print("Please specify the YAML")
   option_ok = 0
else:
   cmd_opt = get_cmd_opt(args.yaml_file)
if args.test_name == None: 
   print("Please specify the testname")
   option_ok = 0

if option_ok == 1:
  run_test(args.test_name, args.seed, args.debug, args.batch, args.dump, args.coverage, args.stdout, args.outdir, cmd_opt )

