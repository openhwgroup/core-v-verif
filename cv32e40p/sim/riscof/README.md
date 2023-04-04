# CV32E40P: RISCOF Compliance Arch-Test-Suite Setup and Flow

Read the Documentation for Latest Requirements at [RISCOF Documentation](https://riscof.readthedocs.io/en/stable/).

## Requirements:
- **TOOLCHAIN**: riscv-gcc-toolchain or any other toolchain for riscv. This needs to be installed and path added to PATH env variable. Also the riscof/config.ini file needs to be updated with toolchain prefix for example: "unknown" or "corev" as part of riscv32-unknown-elf-gcc or riscv32-corev-elf-gcc respectively.
- **RISCOF**: Riscof tool needs to be installed on the machines and Path variable set for use of riscof command. Please refer to `Quickstart --> Install` RISCOF section of the documentation above.
- **Sail Reference Model**: Please refer to `Quickstart --> Install` Plugin Models for SAIL Reference Model installation guide in documentation above.
- **DUT Simulation Setup**: The simulation can be triggered from this sim/riscof dir in same way as sim/uvmt dir and would create a directory structure similar to other uvmt simulations. for example `vsim_results/default/` in sim/riscof directory. We need to setup the $SIMULATOR based on tool that we want to use for DUT simulation.
The riscof work directory path will be available here `riscof_work`.  

## Steps:
- `cd core-v-verif/cv32e40p/sim/riscof`
- `make setup_riscof-compliance CFG=<cfg_name>` : RUN this step preferably only once to avoid doing git clone everytime. This step will do git clone for the compilance test suite - `riscv-arch-test` in vendor_lib/riscof/riscof_arch_test_suite directory and also do a sanity RTL compilation. 
`CFG` option here is to ensure relevant SIM RUN directory based on CFG is created, else `default` CFG will be selected to create directory path similar to uvmt simulations.

- `make riscof_get_testlist RISCOF_SIM=YES CFG=<cfg_name>` : This is optional step. This is basically a sanity check to validate the make scripts, flow and all riscof setup files are validated before running.

- `make riscof_run_all RISCOF_SIM=YES CFG=<cfg_name> ` :  Final RUN command to trigger the complete Compilance Run with RISCOF. Prior to starting this this please ensure "config.ini" file in sim/riscof/ is setup correctly before triggering this.
Example : make riscof_run_all RISCOF_SIM=YES CFG=pulp_fpu :
RISCOF_SIM=YES Must be given for make. It is added in riscof make at the time of initial flow update for this, to keep riscof related make targets from creating any unexpected issues for usual tb simulations
CFG : this is same as CFG argument for makefile as used in usual core-v-verif testbench for simulations to select required CORE configuration.
 
##config.ini:
- This file is configuration file given as input to riscof.
- Some important things to consider for anyone using this setup, is to ensure to modify/update the config.ini file as per the individual core/setup requirements.
Some common configs to consider here:
**jobs** : To select number of parallel make targets to execute, or number of parallel jobs running.
**dut_cfg** : At this time this is the **Actual** `CFG` value that will create correct DUT compile options passed for each individual simulation's make command. And it is expected to be kept same as `CFG` argument passed for the riscof RUN make command from shell. As an example: the expectation is CFG is same at both places, which means:

In config.ini file: dut_cfg=pulp_fpu
Shell MAKE command: make riscof_run_all RISCOF_SIM=YES CFG=pulp_fpu

This together same CFG argument is needed at both the places.

**sw_toolchain_prefix** : to provide chosen riscv toolchain's prefix. Example: `unknown` for riscv32-unknown-elf-gcc

##NOTES:
- For any following runs where we just want to re-compile the RTL and Testbench without doing the git clone for any RISCOF related repos, please use the step mentioned below.
Please Note this step is not needed if running `make setup_riscof-compliance` just prior to this.
`make comp_rtl_riscof-compliance` : Only Compile RTL for riscof DUT simulations

- This setup for CV32E40P has been validated to work for all the implemented standard ISA extentions supported by this CORE : RV32IMFCZicsr_Zifencei

Example Run:
  dut_cfg=pulp_fpu
  jobs = 8
  Used same RISCV toolchain for both: riscv32-unknown-gcc-elf
  SAIL Ref model run with docker. The sail reference model plugin supports both docker and normal execution methods.
