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
To compile a code in system verilog:
```
python3 compile.py --yaml_file.yaml
```

To run a UVM test:
```
python3 run_test.py --yaml_file.yaml --test_name name_of_the_test --seed n_seed --debug UVM_verbosity --dump 0/1 --batch 0/1
```

There is also the possibility to run a set of regression tests reported in a specified reg_list_file:
```
python3 run_reg.py --yaml_file.yaml --nthreads n --reg_list reg_list_file
```
where the nthreads option specifies the occurences of the simulation tool that run in parallel.

The user can also use post_proc.py after batch mode simulations with dumping option enabled for inspecting the DUT waveforms:
```
python3 ${SCRIPTS_DIR}/post_proc.py --tool user_tool --db_file ./path/to/db/file 
```

The templates of yaml files are provided with the script, which can be used to compile and run the test with Questasim, Xcelium and VCS
