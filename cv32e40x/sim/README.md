## SIM directory
The directories from which you should launch your interactive simulations and
regressions are the `core` and `uvmt_cv32` directories located here.

### Cloning the RTL
The Makefiles will automatically clone the required RTL to `../../core-v-cores/cv32e40x`,
unless the CV_CORE_PATH parameter is set.
If the CV_CORE_PATH is set, a symlink to this path will be created in `../../core-v-cores/` instead of cloning the repo.
This allows for working on the RTL in a separate environment.
<br><br>
There are user variables
in `./Common.mk` that control the URL, branch and hash of the cloned code - see
the comment header for examples.  The defaults for these variables will clone the
most up-to-date and stable version of the RTL.  Note that this is not always the
head of the master branch.

### Simulation Directories
There is a sub-dir for each supported CV32 verification environment.
Each sub-dir has its specific Makefile and both include `Common.mk` from this
directory.

#### core
The Makefile will run the SystemVerilog testbench found in `../tb/core` and
its associated tests from `../tests/core`.  This testbench and tests were
inherited from the PULP-Platform team and have been modified only slightly.

#### uvmt_cv32
The Makefile will run the SystemVerilog/UVM verification environment found in
`../tb/uvmt_cv32` and the associated tests from `../tests/uvmt_cv32`.

#### tools
Tool specific sub-dirs for some of the tools used in the CV32.  For example,
Tcl control files for waveform viewing support.
