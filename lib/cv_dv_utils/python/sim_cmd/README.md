<!--- 
  // Copyright 2024 CEA 
  // SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1 
--->

# SIM CMD
## Introduction
These are python scripts, they allow to compile and run a test. 

# Usage
To compile a code in system verilog
python3 compile.py --yaml simulator_vcs.yaml --outdir out

To run a test 
python3 run_test.py --yaml simulator_vcs.yaml --test_name bursty_test_c

The templates of yaml files are provided with the script, which can be used to compile and run the test
