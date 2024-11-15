import argparse
import os
import random 
import compile_cmd as cmp
import run
import threading
import queue 

#sim_cmd_gen.compile
parser = argparse.ArgumentParser(description='Run Regression')
parser.add_argument('--yaml'     ,dest='yaml_file', type=str, help='Top YAML with compile and simulation options')
parser.add_argument('--reg_list'   , dest='reglist'   , type=str, help='file that contains the regression list, the number of seeds and a default seed')
parser.add_argument('--nthreads'   , dest='nthreads'  , type=int, help='Number of test run at the same time: default 2')
parser.add_argument('--outdir'     , dest='outdir'    , type=str, help='output directory: default regression')
args = parser.parse_args()

# Check arguments 
if args.reglist == None:
    args.reglist = "hpdcache_nightly_test_list"
if args.outdir == None:
    args.outdir = "regression"
if args.nthreads == None:
    args.nthreads = 2
if args.ntxns == None:
    args.ntxns = 5000


print("compiling rtl and testbench")
cmp.compile_cmd(args.cfg, args.outdir, 0)

def rtest(test, seed):
    run.run_test(test, seed, "UVM_NONE", 1, 0, args.ntxns, 0,args.outdir)
    log = "{}/{}_{}.log".format(args.outdir, test, seed) 
    pattern = "{}/scripts/patterns/sim_patterns.pat".format(project_dir)
    cmd = "scan_logs.pl -silent -nopreresetwarn {}  -pat {} ".format(log, pattern)
    ret = os.system(cmd)
    if ret == 0: 
        print ("passing", test, "seed", seed)
    else:
        print ("failing", test, "see", seed)

## queues for test and seed
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
      print("running", test, "seed", seed)
      t = threading.Thread(target=rtest, args=(test, seed))
      t.start()
    # os.system("scan_logs.pl -nopreresetwarn {}/{}_{}.log".format(args.outdir, line[0], seed)) 
    
