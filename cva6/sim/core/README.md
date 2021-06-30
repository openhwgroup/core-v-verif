### Simulation directory for CVA6 CORE testbench
**Note:** This is in active development.  It will _probably_ work for you, but at this point cannot do much.
Watch this space for updates.
<br><br>
This is the directory from which you can run simulations of individual testcases on the CORE testbench.  This testbench currently
supports Verilator and Metrics dsim.  Support for other SystemVerilog simulators is pending.  Try this:
```
$ make help
```
<br><br>
Simulation output files are written to a <simulator>\_results directory and testcase generated logs and waves are written to
<simulator>\_results/<test-program>.  For example, the following command will clone a working copy of the CVA6 RTL, compile
it with the CORE testbench using Verilator:
```
$ make verilator_all TEST_PROGRAM=test1
```
With the code compiled, a second test can be run, skipping the cloning and compiling steps as follows:
```
$ make verilator_run TEST_PROGRAM=test2
```
This will produce the following directory tree:
```
├── Makefile
├── README.md
└── verilator_results/
    ├── test1/
    │   ├── test1.log
    │   ├── trace_hart_00.dasm
    │   └── Vcva6_testharness
    ├── test2/
    │   ├── test2.log
    │   ├── trace_hart_00.dasm
    │   └── Vcva6_testharness
    └── verilator_work/
        ├── Vcva6_testharness
        ├── ...verilator objs, etc...
        ├── verilator_compl.log
        └── verilator_trans.log
```
Similar dsim targets will produce the following directory and file structure:
```
.
├── Makefile
├── README.md
└── dsim_results/
    ├── dsim.env
    ├── dsim.log
    ├── dsim_work
    │   ├── debug
    │   ├── dsim.out.so
    │   ├── obj
    │   │   ├── ...many objs...
    │   │   └── objfiles
    │   ├── sfe
    │   └── sir
    │       └── ..many sirs...
    ├── test1/
    │   ├── ..dsim files...
    │   ├── test1.log
    │   ├── trace_hart_0_commit.log
    │   └── trace_hart_0.log
    └── test2/
        ├── ..dsim files...
        ├── test2.log
        ├── trace_hart_0_commit.log
        └── trace_hart_0.log
```

