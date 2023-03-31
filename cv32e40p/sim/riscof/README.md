# CV32E40P: RISCOF Compliance Arch-Test-Suite Setup and Flow

Read the Documentation for Latest Requirements at [RISCOF Docs](https://riscof.readthedocs.io/en/stable/).

## Requirements:
- **TOOLCHAIN**: riscv-gcc-toolchain or any other toolchain for riscv. This needs to be installed and Path added to PATH env variable. Also the riscof/config.ini file needs to be updated with toolchain prefix for example: unknown or corev as part of riscv32-unknown-elf-gcc or riscv32-corev-elf-gcc respectively.
- **RISCOF**: Riscof tool needs to be installed on the machines and Path variable set for use of riscof command. Please refer to `Quickstart --> Install` RISCOF section of the documentation above.
- **Sail Reference Model**: Please refer to `Quickstart --> Install` Plugin Models for SAIL Reference Model installation guide in documentation above.
- **DUT Simulation Setup**: The simulation can be triggered from this sim/riscof dir in same way as sim/uvmt dir and would create a directory structure similar to other uvmt simulations. for example `vsim_results/default/` in sim/riscof directory. We need to setup the $SIMULATOR based on tool that we want to use for DUT simulation.
The riscof work directory path will be available here `riscof_work`.  

## Steps:
- cd core-v-verif/cv32e40p/sim/riscof
- make setup_riscof-compliance : `RUN preferably only once to avoid doing git clone everytime` This Step will CLONE the riscv-arch-test suite in vendor_lib/riscof/riscof_arch_test_suite dir and do the RTL and TB compilation.
- make riscof_get_testlist RISCOF_SIM=YES : This is just a validation step to ensure the make scripts, flow and all riscof setup files are validated before running.
- make riscof_run_all RISCOF_SIM=YES : RUN command to trigger the Compilance Run with RISCOF, please ensure config.ini is setup correctly before triggering this.

For any following runs where we just want to re-compile the RTL and Testbench without doing the git clone for any RISCOF related repos, please use the step mentioned below.
Please Note this step is not needed if running `make setup_riscof-compliance` just prior to this.
- make comp_rtl_riscof-compliance : Only Compile RTL for riscof DUT simulations
