<!--- 
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
