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
import re
import get_cmd as cmp

parser = argparse.ArgumentParser(description='compile options')
parser.add_argument('--yaml'     ,dest='yaml_file', type=str, help='Top YAML with compile and simulation options')
parser.add_argument('--outdir'   ,dest='outdir', type=str, help='Logs are directed to outdir: default output')
args = parser.parse_args()

   

if args.outdir==None:
    outdir = "output"
else:
    outdir = args.outdir
  

if args.yaml_file == None: 
   print("Please provide a Top YAML file")
else:
   if os.path.isdir("{}".format(outdir)) == False:
     os.system("mkdir {}".format(outdir))
   vopt_cmd = cmp.cmp_cmd(args.yaml_file, outdir, '', '', '')
   if vopt_cmd != "":
     os.system(vopt_cmd)
