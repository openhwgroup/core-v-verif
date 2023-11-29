<!--
Copyright 2022 OpenHW Group
SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
-->
# Verification Environment for the CV32E20 CORE-V processor core.
This directory hosts the CV32E20-specific SystemVerilog sources plus C and assembly test-program sources for the CV32E20 verification environment.
Non-CV32E20-specific verification components (e.g. OBI Agent) used in this verification environment are in `../lib` and `../vendor_lib`.

## Directories:
- **bsp**:        the "board support package" for test-programs compiled/assembled/linked for the CV32E20.  This BSP is used by both the `core` testbench and the `uvmt_cv32` UVM verification environment.
- **env**:        the UVM environment class and its associated infrastrucutre.
- **sim**:        directory where you run the simulations.
- **tb**:         the Testbench module that instanitates the core.
- **tests**:      this is where all the testcases are.
- **vendor_lib**: Third party vendor libraries and extensions to same.

There are README files in each directory with additional information.

## Getting Started
Check out the Quick Start Guide in the [CORE-V-VERIF Verification Strategy](https://docs.openhwgroup.org/projects/core-v-verif/en/latest/quick_start.html).
<br>
You may also find it useful to review the [Common Makefile for the CORE-V-VERIF UVM Verification Environment](https://github.com/openhwgroup/core-v-verif/blob/master/mk/README.md).
