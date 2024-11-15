# SIM CMD
## Introduction
These are pyhton scripts, they allow to compile and run a test. 

# Usage
To compile a a code in system verilog
python3 compile.py --yaml simulator_vcs.yaml --outdir out

To run a test 
python3 run_test.py --yaml simulator_vcs.yaml --test_name bursty_test_c

The templates of yaml files are providede with the script, which can be used to copile and run the test
