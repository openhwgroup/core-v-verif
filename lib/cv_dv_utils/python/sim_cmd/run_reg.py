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
import random 
import threading
import queue
import yaml

# Import the 'datetime' module to work with date and time
import datetime


#get_cmd_gen.compile
parser = argparse.ArgumentParser(description='Run Regression')
parser.add_argument('--yaml'       ,dest='yaml_file', type=str, help='Top YAML with compile and simulation options')
parser.add_argument('--reg_list'   ,dest='reglist'   , type=str, help='file that contains the regression list, the number of seeds and a default seed')
parser.add_argument('--nthreads'   ,dest='nthreads'  , type=int, help='Number of test run at the same time: default 2')
parser.add_argument('--cover'    , dest='cover',     type=int, help='1: generate coverage file, 0: nothing is done, cover option are passed from yaml file ') #FIXME
parser.add_argument('--outdir'     , dest='outdir'    , type=str, help='output directory: default regression')
args = parser.parse_args()

#save the environment variables
project_dir = os.environ["PROJECT_DIR"]
scripts_dir = os.environ["SCRIPTS_DIR"]

# Check arguments 
if args.outdir == None:
    outdir = "regression"
else:
    outdir = args.outdir

if args.nthreads == None:
    args.nthreads = 1


def rtest(yaml_file, test, seed):
    run_cmd = f"python3 {scripts_dir}/run_test.py --yaml {yaml_file} --test_name {test} --seed {seed} --debug UVM_LOW --dump 1 --stdout 0 --outdir {outdir}"
    print("[INFO] Simulation command:\n{}".format(run_cmd))
    os.system(run_cmd)
    log = "{}/{}_{}.log".format(outdir, test, seed) 
    pattern = "{}/scripts/patterns/sim_patterns.pat".format(project_dir)
    cmd = "scan_logs.pl -silent -nopreresetwarn {}  -pat {} ".format(log, pattern)
    ret = os.system(cmd)
    et = datetime.datetime.now()
    if ret == 0: 
        print ("passing", test, "seed", seed,  "end time", et.strftime("%Y-%m-%d %H:%M:%S"))
    else:
        print(f"RET={ret}")
        print ("failing", test, "seed", seed,  "end time", et.strftime("%Y-%m-%d %H:%M:%S"))

print("[INFO] Starting compilation and elaboration...")
#check the insertion of the top yaml file
if args.yaml_file == None: 
   print("[ERROR] Please provide a Top YAML file")
else:
   if os.path.isdir("{}".format(outdir)) == False:
     os.system("mkdir {}".format(outdir))

   #call the compilation and elaboration command
   comp_el_cmd = f"python3 {scripts_dir}/compile.py --yaml {args.yaml_file}"
   print("[INFO] Compilation and elaboration command:\n{}".format(comp_el_cmd))
   #vopt_cmd = get_cmd.cmp_cmd(args.yaml_file, outdir, '', '', '')
   if comp_el_cmd != "":
     os.system(comp_el_cmd)

#queues for test and seed
if args.reglist == None:
    print("Please provide a Regression List")
else:
  tq = queue.Queue()
  sq = queue.Queue()
  
  f = open(args.reglist, "r")
  for x in f:
    line = x.split(" ")
    for y in range(0, int(line[1])):
        seed = random.getrandbits(31)
        sq.put(seed)
        tq.put(line[0])
  
  while (not tq.empty()):
      if threading.active_count() <= args.nthreads:
        seed = sq.get()
        test = tq.get()
        st = datetime.datetime.now()
        print("running", test, "seed", seed, "start time", st.strftime("%Y-%m-%d %H:%M:%S"))
        t = threading.Thread(target=rtest, args=(args.yaml_file, test, seed))
        t.start()
      # os.system("scan_logs.pl -nopreresetwarn {}/{}_{}.log".format(args.outdir, line[0], seed)) 
        
