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
##   Copyright 2013 Verilab, Inc.
##   All Rights Reserved Worldwide
##
##   Licensed under the Apache License, Version 2.0 (the
##   "License"); you may not use this file except in
##   compliance with the License.  You may obtain a copy of
##   the License at
##
##       http://www.apache.org/licenses/LICENSE-2.0
##
##   Unless required by applicable law or agreed to in
##   writing, software distributed under the License is
##   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
##   CONDITIONS OF ANY KIND, either express or implied.  See
##   the License for the specific language governing
##   permissions and limitations under the License.
##----------------------------------------------------------------------

import argparse
import os
import yaml

#import compile_cmd as cmp

parser = argparse.ArgumentParser(description='compile options')
parser.add_argument('--yaml'     ,dest='yaml_file', type=str, help='Top YAML with compile and simulation options')
parser.add_argument('--outdir'   ,dest='outdir', type=str, help='Logs are directed to outdir: default output')
args = parser.parse_args()

   
def get_cmd(yaml_file, outdir, opt, vopt_option, work):
  with open(yaml_file, 'r') as yaml_top:
     sim_yaml = yaml.safe_load(yaml_top)
  
  
  for entry in sim_yaml: 
      if entry['tool'] == "questa":
          cmd       = "vlog -sv"
          vopt_cmd  = "vopt"
          tool      = "questa"
      elif entry['tool'] == "vcs":
          cmd       = "vcs -sverilog"
          vopt_cmd  = ""
          tool      = "vcs"
      if 'compile' in entry:
        comp      = entry['compile']
      else: 
        comp = ""
      ########################
      ## get compile options ##
      ########################
      if 'work_lib' in comp:
        work_lib  = comp['work_lib']
      elif work != '':
        work_lib = work
      else:
        work_lib = "work"
      ########################
      ## get SV log options ##
      ########################
      if 'svlog_option' in comp:
        opt       += " "
        opt       += comp["svlog_option"]
      else: 
        opt += " "
      ########################
      ## get SV log sources ##
      ## *.sv               ##
      ########################
      if 'svlog_source' in comp:
        src_list  = comp["svlog_source"]
        srcs      = src_list.split()
      else: 
        src_list  = ""
      ########################
      ## get file list ##
      ########################
      if 'svlog_flist' in comp:
        file_list = comp["svlog_flist"]
        files     = file_list.split()
      else: 
        file_list = ""
        files     = ""
      ########################
      ## get vopt options ##
      ########################
      if 'top_entity' in entry:
        top_entity  = comp['top_entity']
      else: 
        top_entity = "top"
      if 'vopt_option' in comp:
        vopt_option  += " "
        vopt_option  += comp['vopt_option']
      else: 
        vopt_option += " "
      ########################
      ## run other YAML   ####
      ########################
      if 'yaml_lists' in comp:
        yaml_list = comp["yaml_lists"]
        yamls     = yaml_list.split()
        for y in yamls:
            get_cmd(y, outdir, opt, vopt_option, work_lib)
  

  file_cmd = ""
  for f in files:
    file_cmd += " -f " + f

  if tool == "questa":
    compile_cmd = "{} {} {} {} -work {} -l {}/{}.log".format(cmd, opt, file_cmd, src_list, work_lib, outdir, yaml_file)
    vopt_cmd    = "{} {} -work {} {} -o opt".format(vopt_cmd, vopt_option, work_lib, top_entity)
  elif tool == "vcs":
    compile_cmd = "{} {} {} {} -l {}/{}.log".format(cmd, opt, file_cmd, src_list, outdir, yaml_file)
    vopt_cmd = ""

  print(compile_cmd)
  os.system(compile_cmd)
  return vopt_cmd
## get_cmd 

if args.outdir==None:
    outdir = "output"
else:
    outdir = args.outdir
  

if args.yaml_file == None: 
   print("Please provide a Top YAML file")
else:
   if os.path.isdir("{}".format(outdir)) == False:
     os.system("mkdir {}".format(outdir))
   vopt_cmd = get_cmd(args.yaml_file, outdir, '', '', '')
   if vopt_cmd != "":
     os.system(vopt_cmd)
