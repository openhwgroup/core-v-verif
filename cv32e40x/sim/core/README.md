Simulation Directory for CV32E Core Testbench
==================================
This is the directory in which you should run all tests of the Core Testbench.
The testbench itself is located at `cv32e40*/tb/core` and the test-programs are at
`cv32e40*/tests/programs`.  See the README in those directories for more information.

To run the core testbench you will need a SystemVerilog simulator and RISC-V GCC compiler.

Supported SystemVerilog Simulators
----------------------------------
The core testbench and associated test-programs were only tested with 
 **_Verilator_** and Mentor's **_Questa_**. But the Makefile also provides simuation commands for the Metrics
**_dsim_**,  Cadence **_Xcelium_**, Synopsys **_vcs_** and Aldec **_Riviera-PRO_**
simulators. Note that **_Icarus_** verilog cannot compile the RTL and there are no plans
to support Icarus in the future.

RISC-V GCC Compiler "Toolchain"
-------------------------------
See the `TOOLCHAIN.md` in `core-v-verif/mk/` to choose the recommended toolchain for CV32E40X .

Running your own C programs
---------------------
A hello world program is available and you can run it in the CV32E Core testbench.
Invoke the `make questa-custom TEST=hello-world` or `make veri-test TEST=hello-world` makefile rules to run it with
`vsim` or `verilator` respectively.

The hello world program is located in the `cv32e40x/tests/programs/custom` folder. The `hello-world.c` is compiled and then linked with the BSP objects to generate the ELF file.  You can reset the default values of `TEST_PROGRAM_PATH` and `TEST` in the command line to point to your own C programs. Make sure you have a working C compiler (see above) and keep in
mind that you are running on a very basic machine.

Running the testbench with [verilator](https://www.veripool.org/wiki/verilator)
----------------------
Point your environment variable `RISCV` to your RISC-V toolchain. If you have a C or assembly program in `cv32e40*/tests/programs/custom/`
then the following will work with Verilator:<br>
```
make veri-test TEST=hello-world
make veri-test TEST=csr_instructions
make veri-test TEST=misalign
...
```

Running the testbench with Questa (vsim)
---------------------------------------------------------
Point your environment variable `RISCV` to your RISC-V toolchain. Call the following commands to work with Vsim:<br>
```
make questa-custom TEST=hello-world
make questa-custom TEST=csr_instructions
make questa-custom TEST=misalign
...
```

Run `make firmware-vsim-run` to build the testbench and the firmware. Use
`VSIM_FLAGS` to configure the simulator e.g. `make firmware-vsim-run
VSIM_FLAGS="-gui -debugdb"`.
<br>The Makefile also supports running individual assembler tests from either
the riscv_tests or riscv_compliance_tests directories using vsim. For example,
to run the ADD IMMEDIATE test from riscv_tests:
* `make questa-unit-test addi`
<br>To run I-LBU-01.S from the riscv_compliance_tests:
* `make questa-unit-test I_LBU_01`

Running the testbench with Metrics [dsim](https://metrics.ca)
----------------------
Point your environment variable `RISCV` to your RISC-V toolchain. Call
`make dsim-hello_world` to build and run the testbench with the hello_world
test in the custom directory. Other rules of interest:
* `make dsim-cv32_riscv_tests` to build and run the testbench with all the testcases in the riscv_tests directory.
* `make dsim-cv32_riscv_compliance_tests` to build and run the tests in riscv_compliance_tests.
* `make dsim-firmware` to build and run the testbench with all the testcases in the riscv_tests and riscv_compliance_tests directories.
<br><br>The Makefile now supports running individual assembler tests from either
the riscv_tests or riscv_compliance_tests directories. For example, to run the ADD IMMEDIATE test from riscv_tests:
* `make dsim-unit-test addi`
<br>To run I-LBU-01.S from the riscv_compliance_tests:
* `make dsim-unit-test I_LBU_01`
<br>You can clean up the mess you made with `make dsim-clean`.

Running the testbench with Cadence Xcelium [xrun](https://www.cadence.com/en_US/home/tools/system-design-and-verification/simulation-and-testbench-verification/xcelium-parallel-simulator.html)
----------------------
**Note:** This testbench is known to require Xcelium 19.09 or later.  See [Issue 11](https://github.com/openhwgroup/core-v-verif/issues/11) for more info.
Point your environment variable `RISCV` to your RISC-V toolchain. Call
`make xrun-hello_world` to build and run the testbench with the hello_world
test in the custom directory. Other rules of interest:
* `make xrun-firmware` to build and run the testbench with all the testcases in the riscv_tests/ and riscv_compliance_tests/ directories.
* Clean up your mess: `make xsim-clean` (deletes xsim intermediate files) and `xrun-clean-all` (deletes xsim intermedaites and all testcase object files).

Running the testbench with VCS (vcs)
----------------------
Point your environment variable `RISCV` to your RISC-V toolchain.
Call `make firmware-vcs-run` to build the testbench and the firmware, and run it.
Use `SIMV_FLAGS` or `VCS_FLAGS` to configure the simulator and build respectively e.g.
`make firmware-vcs-run VCS_FLAGS+="-cm line+cond+fsm+tgl+branch" SIMV_FLAGS+="-cm line+cond+fsm+tgl+branch"`

Running the testbench with Riviera-PRO (riviera)
----------------------
Point you environment variable `RISCV` to your RISC-V toolchain. Call `make
riviera-hello-world` to build the testbench and the firmware, and run it. Use
`ASIM_FLAGS` to configure the simulator e.g. `make custom-asim-run
ASIM_FLAGS="-gui"`.

Options
-------
A few plusarg options are supported:
* `+verbose` to show all memory read and writes and other miscellaneous information.

* `+vcd` to produce a vcd file called `riscy_tb.vcd`. Verilator always produces
  a vcd file called `verilator_tb.vcd`.

Examples
--------
Run all riscv_tests to completion with **dsim**:
`make dsim-cv32_riscv_tests`

