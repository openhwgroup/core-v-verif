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
Python scripts to compile, elaborate, and run UVM tests. Supports waveform dumping and coverage collection. Compatible with Questasim, Xcelium, and VCS.

# Usage

## Compilation

To compile and elaborate a design:
```
python3 compile.py --yaml yaml_file.yaml [--outdir output_dir] [--cover 0/1]
```

| Option | Description | Default |
|--------|-------------|---------|
| `--yaml` | Top YAML file with compile and simulation options | required |
| `--outdir` | Directory for compilation logs | `output` |
| `--cover` | `1`: To pass coverage option during elab; `0`: no coverage | `0` |

## Running a single test

```
python3 run_test.py --yaml yaml_file.yaml --test_name name_of_the_test --seed n_seed [options]
```

| Option | Description | Default |
|--------|-------------|---------|
| `--yaml` | Top YAML file with compile and simulation options | required |
| `--test_name` | Name of the UVM test to run | required |
| `--seed` | Random seed | `1` |
| `--debug` | UVM verbosity: `UVM_NONE/LOW/MEDIUM/HIGH/DEBUG` | `UVM_LOW` |
| `--batch` | `1`: batch mode; `0`: GUI mode | `1` |
| `--dump` | `1`: log all signals to waveform database; `0`: no dump | `0` |
| `--cover` | `1`: enable coverage collection; `0`: disabled | `0` |
| `--stdout` | `1`: print log to stdout; `0`: redirect to log file | `1` |
| `--outdir` | Output directory for logs and databases | `output` |
| `--run_time` | Simulation run time (e.g. `100ns`) | `-all` |
| `--verbose` | Print informational messages | `False` |

## Running a regression

```
python3 run_reg.py --yaml yaml_file.yaml --reg_list reg_list_file [--nthreads n] [--cover 0/1] [--outdir output_dir]
```

| Option | Description | Default |
|--------|-------------|---------|
| `--yaml` | Top YAML file with compile and simulation options | required |
| `--reg_list` | File listing tests and number of seeds | required |
| `--nthreads` | Number of parallel simulation instances | `1` |
| `--cover` | `1`: enable coverage for all tests; `0`: disabled | `0` |
| `--outdir` | Output directory | `regression` |
| `--verbose` | Print informational messages | `False` |

## Coverage (Questasim only)

To enable coverage, pass `--cover 1` to `compile.py` and `run_test.py` (or `run_reg.py` for regressions). Each test saves its UCDB file to `{outdir}/coverage/{test_name}_{seed}.ucdb`.

## Waveform inspection

The user can also use post_proc.py after batch mode simulations with dumping option enabled for inspecting the DUT waveforms:
```
python3 ${SCRIPTS_DIR}/post_proc.py --tool user_tool --db_file ./path/to/db/file
```

The templates of yaml files are provided with the script, which can be used to compile and run the test with Questasim, Xcelium and VCS.
