Simulation Makefile Directory for CV32E40P UVM Verification Environment
==================================
This is the directory in which you should run all tests of the UVM environment.
All results (compile logs, waveforms, run logs, simulation databases, etc.)
will be placed in this directory under $(SIMULATOR)\_results in a directory tree that follows this structure:
<br><br>
```
$(SIMULATOR)\_results/
└── $(CFG)
    ├── $(SIMULATOR)\_work
    │   └── $(SIMULATOR)\_specific_objs_etc
    └── ($TEST)
        └── $(RUN_INDEX)
            ├── $(TEST).log
            ├── <optional_coverage_files>
            ├── test_program
            │   ├── bsp
            │   │   ├── crt0.o
            │   │   ├── handlers.o
            │   │   ├── libcv-verif.a
            │   │   ├── Makefile
            │   │   ├── syscalls.o
            │   │   └── vectors.o
            │   ├── $(TEST).elf
            │   ├── $(TEST).hex
            │   ├── $(TEST).itb
            │   ├── $(TEST).objdump
            │   └── $(TEST).readelf
            └── <UVM_Agent_Logs>.log
```
<br><br>
All the variables above (e.g. $(TEST)), can be set as shell environment variables or on the `make` command-line.
If these variables are not specified, defaults will be used.
For more information regarding the use of these variables, see the [README in the mk/uvmt directory](../../../mk/uvmt)_<br>.
For directory indepedent execution, please see the makeuvmt utility in the [bin](../../../bin) directory_<br>

