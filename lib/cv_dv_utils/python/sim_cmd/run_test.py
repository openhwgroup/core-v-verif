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
import get_cmd as sim

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


option_ok = 1
if args.yaml_file == None:
   print("Please specify the YAML")
   option_ok = 0
else:
   cmd_opt = sim.get_cmd_opt(args.yaml_file)
if args.test_name == None: 
   print("Please specify the testname")
   option_ok = 0

if option_ok == 1:
  sim.run_test(args.test_name, args.seed, args.debug, args.batch, args.dump, args.coverage, args.stdout, args.outdir, cmd_opt )

