import argparse
import os
import yaml

parser = argparse.ArgumentParser(description='compile and simulation options')
parser.add_argument('--yaml'     ,dest='yaml_file', type=str, help='Top YAML with compile and simulation options')
parser.add_argument('--test_name',dest='test_name', type=str, help='Name of the test, default: test_hpdcache_multiple_random_requests')
parser.add_argument('--seed'     , dest='seed',      type=int, help='random seed ex: 3452363, default 1')
parser.add_argument('--debug'    , dest='debug',     type=str, help='UVM_LOW/MEDIUM/HIGH/FULL/DEBUG, default LOW')
parser.add_argument('--batch'    , dest='batch',     type=int, help='1: batch mode, 0:gui default, 1')
parser.add_argument('--stdout' , dest='stdout', type=int, help='1: stdout 0: nostdout')
parser.add_argument('--outdir'   , dest='outdir', type=str, help='output dirctory de fault "output"')
##
args = parser.parse_args()

def run_test(cmd, test_name, seed, debug, batch, stdout, outdir, work_lib, opt, tool):
   ## get arguments
   if outdir == None: 
      outdir = "output"

   
   if seed == None: 
      seed = 1
   
   if debug == None: 
      debug = "UVM_LOW"
  
   if batch == None: 
      batch = 1 
   
   if batch == 1:
     if tool == "questa":
       batchstr = "-c"
     else:
       batchstr = ""
   else:
     if tool == "vcs":
       batchstr = "-gui"
     else:
       batchstr = ""
   
   if stdout == None:
       stdout = 1

   if stdout == 0:
       stdoutstr = ">"
   else:
       stdoutstr = "-l"
  
   if os.path.isdir("{}".format(outdir)) == False:
     os.system("mkdir {}".format(outdir))
   
   if test_name == None: 
       print("ERROR: Please provide a valid test name") 
   else:
     if tool == "questa":
       run_cmd = "{} {} -sv_seed {} +UVM_VERBOSITY={} -wlf {}/{}_{}.wlf +UVM_TESTNAME={} {} -lib {} opt {} {}/{}_{}.log".format(cmd, batchstr, seed, debug, outdir, test_name, seed, test_name, opt, work_lib, stdoutstr, outdir, test_name, seed )
     elif tool == "vcs":
       run_cmd = "{} {} +ntb_random_seed={} +UVM_VERBOSITY={} -grw {}/{}_{}.wlf +UVM_TESTNAME={} {} {}/{}_{}.log".format(cmd, batchstr, seed, debug, outdir, test_name, seed, test_name, stdoutstr, outdir, test_name, seed )

   print(run_cmd)
   os.system("{}".format(run_cmd))

def get_cmd(yaml_file, opt):
  with open(yaml_file, 'r') as yaml_top:
     sim_yaml = yaml.safe_load(yaml_top)
  
  
  for entry in sim_yaml: 
      if entry['tool'] == "questa":
          cmd       = "vsim"
          tool      = "quest"
          if 'sim' in entry:
            sim      = entry['sim']
          else: 
            sim = ""
      elif entry['tool'] == "vcs":
          cmd       = "./simv"
          tool      = "vcs"
          if 'sim' in entry:
            sim      = entry['sim']
          else: 
            sim = ""
      ########################
      ## get compile options ##
      ########################
      if tool == "questa":
        if 'work_lib' in sim:
          work_lib  = sim['work_lib']
        elif work != '':
          work_lib = work
        else:
          work_lib = "work"
      else:
        work_lib = ""
      ########################
      ## get SV log options ##
      ########################
      if 'sim_option' in sim:
        opt       += " "
        opt       += sim["sim_option"]
      else: 
        opt += " "
  return cmd, work_lib, opt, tool

if args.yaml_file == None: 
   print("Please provide a Top YAML file")
else:
   cmd, work_lib, opt, tool = get_cmd(args.yaml_file, '')
   run_test(cmd, args.test_name, args.seed, args.debug, args.batch, args.stdout, args.outdir, work_lib, opt, tool )



