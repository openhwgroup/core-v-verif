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


import os
import yaml
import re

def cmp_cmd(yaml_file, outdir, opt, vopt_option, work):
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
        srcs      = ""
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
            var   = y.split('{', 1)[1].split('}')[0]
            path  = os.environ[var];
            y = re.sub('\${.*}', path, y)
            print(y)
            cmp_cmd(y, outdir, opt, vopt_option, work_lib)
  

  #####################################
  ## extract file from file list   ####
  #####################################
  file_cmd = ""
  for f in files:
    file_cmd += " -f " + f
  #####################################
  ## extract src from src list   ####
  #####################################
  src_cmd = ""
  for s in srcs:
    src_cmd += " -sv " + s

  if tool == "questa":
    compile_cmd = "{} {} {} {} -work {} -l {}/{}.log".format(cmd, opt, file_cmd, src_cmd, work_lib, outdir, "log")
    vopt_cmd    = "{} {} -work {} {} -o opt".format(vopt_cmd, vopt_option, work_lib, top_entity)
  elif tool == "vcs":
    compile_cmd = "{} {} {} {} -l {}/{}.log".format(cmd, opt, file_cmd, src_list, outdir, yaml_file)
    vopt_cmd = ""

  print(yaml_file)
  if src_list == "" and file_cmd == "" and src_cmd == "":
   return vopt_cmd
  else:
   print(compile_cmd)
   os.system(compile_cmd)
   return vopt_cmd
## cmp_cmd

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
     batchstr = "-c -do \"run -all\""
   else:
     batchstr = "-visualizer"
   
   if dump == 1:
     wlfstr  = "-wlf {}/{}_{}.wlf".format(outdir, test_name, seed)
     dumpstr = ""
   else:
     dumpstr = ""
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
