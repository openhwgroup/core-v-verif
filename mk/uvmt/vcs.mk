###############################################################################
#
# Copyright 2020 OpenHW Group
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
###############################################################################
#
# VCS-specific Makefile for the Core-V-Verif "uvmt" testbench.
#
###############################################################################

#
# Synopsys do not (officially) support Ubuntu, so suppress the nonzero return code from VCS
#
OS_IS_UBUNTU = $(findstring Ubuntu,$(shell lsb_release -d))
ifeq ($(OS_IS_UBUNTU),Ubuntu)
    .IGNORE: hello-world comp test compliance comp_corev-dv corev-dv gen_corev-dv
endif

# Executables
VCS              = $(CV_SIM_PREFIX) vcs
#SIMV             = $(CV_TOOL_PREFIX) simv -licwait 20
SIMV             = simv -licwait 20
DVE              = $(CV_TOOL_PREFIX) dve
#VERDI            = $(CV_TOOL_PREFIX)verdi
URG               = $(CV_SIM_PREFIX) urg

# Paths
VCS_DIR         ?= $(SIM_CFG_RESULTS)/vcs.d
VCS_ELAB_COV     = -cm line+cond+tgl+fsm+branch+assert  -cm_dir $(MAKECMDGOALS)/$(MAKECMDGOALS).vdb

# Modifications to already defined variables to take into account that VCS
# does not require the ".so" extension for shared objects.
VCS_OVP_MODEL_DPI = $(OVP_MODEL_DPI:.so=)
VCS_DPI_DASM_LIB  = $(DPI_DASM_LIB:.so=)
VCS_SVLIB_LIB     = $(SVLIB_LIB:.so=)

VCS_TIMESCALE = $(shell echo "$(TIMESCALE)" | tr ' ' '=')    # -timescale=1ns/1ps

VCS_UVM_VERBOSITY ?= UVM_MEDIUM

# Flags
VCS_VERSION     ?= S-2021.09-SP1
VCS_UVMHOME_ARG ?= /synopsys/vcs/$(VCS_VERSION)/etc/uvm-1.2
VCS_UVM_ARGS    ?= +incdir+$(VCS_UVMHOME_ARG)/src $(VCS_UVMHOME_ARG)/src/uvm_pkg.sv +UVM_VERBOSITY=$(VCS_UVM_VERBOSITY) -ntb_opts uvm-1.2

VCS_COMP_FLAGS  ?= -lca -sverilog \
                   $(SV_CMP_FLAGS) $(VCS_UVM_ARGS) $(VCS_TIMESCALE) \
                   +define+CV32E20_RVFI+RVFI \
                   -assert svaext -ignore unique_checks -full64 -licwait 20
VCS_GUI         ?=
VCS_RUN_COV      = -cm line+cond+tgl+fsm+branch+assert -cm_dir $(MAKECMDGOALS).vdb

# Necessary libraries for the PMA generator class
VCS_PMA_INC += +incdir+$(TBSRC_HOME)/uvmt \
               +incdir+$(CV_CORE_PKG)/rtl/include \
               +incdir+$(CV_CORE_COREVDV_PKG)/ldgen \
               +incdir+$(abspath $(MAKE_PATH)/../../../lib/mem_region_gen)

###############################################################################
# Common QUIET flag defaults to -quiet unless VERBOSE is set
ifeq ($(call IS_YES,$(VERBOSE)),YES)
QUIET=
else
QUIET=-q
endif

################################################################################
# GUI interactive simulation
# GUI=YES enables interactive mode
# ADV_DEBUG=YES currently not supported
ifeq ($(call IS_YES,$(GUI)),YES)
VCS_GUI += -gui
VCS_USER_COMPILE_ARGS += -debug_access+r
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
$(error ADV_DEBUG not yet supported by VCS )
endif
endif

################################################################################
# Waveform generation
# WAVES=YES enables waveform generation for entire testbench
# ADV_DEBUG=YES currently not supported
# FSDB=YES enables FSDB waveform file generation for entire testbench
ifeq ($(call IS_YES,$(WAVES)),YES)
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
$(error ADV_DEBUG not yet supported by VCS )
VCS_USER_COMPILE_ARGS += +vcs+vcdpluson
else
ifeq ($(call IS_YES,$(FSDB)),YES)
VCS_USER_COMPILE_ARGS += -debug_access+all +vcs+fsdbon -kdb
VCS_RUN_WAVES_FLAGS  ?= -ucli -i $(abspath $(MAKE_PATH)/../tools/vcs/vcs_wave.tcl)
else
VCS_USER_COMPILE_ARGS += +vcs+vcdpluson
endif
endif
endif

################################################################################
# Waveform (post-process) command line
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
$(error ADV_DEBUG not yet supported by VCS )
WAVES_CMD = cd $(SIM_RUN_RESULTS) && $(DVE) -vpd vcdplus.vpd
else
WAVES_CMD = cd $(SIM_RUN_RESULTS) && $(DVE) -vpd vcdplus.vpd
endif

################################################################################
# Coverage options
# COV=YES generates coverage database, must be specified for comp and run
URG_MERGE_ARGS = -dbname merged.vdb -group lrm_bin_name -flex_merge union
MERGED_COV_DIR ?= merged_cov

ifeq ($(call IS_YES,$(COV)),YES)
VCS_USER_COMPILE_ARGS += $(VCS_ELAB_COV)
VCS_RUN_COV_FLAGS += $(VCS_RUN_COV)
endif

# list all vbd files
COV_RESULTS_LIST = $(wildcard $(SIM_RESULTS)/*/*.vdb)

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_MERGE = cov_merge
TEST = $(MERGED_COV_DIR)
else
COV_MERGE =
endif

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_ARGS = -dir cov_work/scope/merged
else
COV_ARGS = -dir $(TEST_RUN_NAME).vdb
endif


ifeq ($(call IS_YES,$(CHECK_SIM_RESULT)),YES)
CHECK_SIM_LOG ?= $(abspath $(SIM_RUN_RESULTS))/vcs-$(TEST_RUN_NAME).log
POST_TEST = \
	@if grep -q "SIMULATION FAILED" $(CHECK_SIM_LOG); then \
		exit 1; \
	fi
endif

################################################################################

VCS_FILE_LIST ?= -f $(DV_UVMT_PATH)/uvmt_$(CV_CORE_LC).flist
VCS_USER_COMPILE_ARGS += +define+$(CV_CORE_UC)_TRACE_EXECUTION+UNSUPPORTED_WITH
ifeq ($(call IS_YES,$(USE_ISS)),YES)
    VCS_USER_COMPILE_ARGS += +define+USE_ISS
    VCS_USER_COMPILE_ARGS += +define+USE_IMPERASDV
    VCS_FILE_LIST_IDV ?= -f $(DV_UVMT_PATH)/imperas_dv.flist
    VCS_PLUSARGS += +USE_ISS
    VCS_PLUSARGS += +USE_IMPERASDV
    VCS_PLUSARGS += -sv_lib $(basename $(IMPERAS_DV_MODEL))
    ifeq ($(call IS_YES,$(COV)),YES)
        VCS_USER_COMPILE_ARGS += +define+IMPERAS_COV
        VCS_PLUSARGS += +IDV_TRACE2COV=1
    endif
else
	VCS_PLUSARGS += +DISABLE_OVPSIM
	VCS_FILE_LIST_IDV ?=
endif

# TODO: determine impact of removing VCS_OVP_MODEL_DPI with USE_ISS=YES
#                        -sv_lib $(VCS_OVP_MODEL_DPI) \
# TODO: removing VCS_DPIDASM_LIB effectively disables ISACOV
#                        -sv_lib $(VCS_DPI_DASM_LIB) \

VCS_RUN_BASE_FLAGS   ?= $(VCS_GUI) \
                        $(VCS_PLUSARGS) \
                        +ntb_random_seed=$(RNDSEED) \
                        -assert nopostproc \
                        -sv_lib $(abspath $(VCS_SVLIB_LIB))

VCS_RUN_BASE_FLAGS   += -sv_lib $(basename $(ELFLOADER_LIB))

# Simulate using latest elab
VCS_RUN_FLAGS        ?=
VCS_RUN_FLAGS        += $(VCS_RUN_BASE_FLAGS)
VCS_RUN_FLAGS        += $(VCS_RUN_WAVES_FLAGS)
VCS_RUN_FLAGS        += $(VCS_RUN_COV_FLAGS)

# Special var to point to tool and installation dependent path of DPI headers.
# Used to recompile dpi_dasm_spike if needed (by default, not needed).
DPI_INCLUDE          ?= $(shell dirname $(shell which vcs))/../lib

###############################################################################
# Targets

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=vcs sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'

help:
	vcs -help

.PHONY: comp test waves cov

mk_vcs_dir:
	$(MKDIR_P) $(VCS_DIR)

# This special target is to support the special sanity target in the Common Makefile
hello-world:
	$(MAKE) test TEST=hello-world

VCS_COMP = $(VCS_COMP_FLAGS) \
		$(CFG_COMPILE_FLAGS) \
		$(QUIET) \
		$(VCS_UVM_ARGS) \
		$(VCS_USER_COMPILE_ARGS) \
		+incdir+$(DV_UVME_PATH) \
		+incdir+$(DV_UVMT_PATH) \
		-f $(CV_CORE_MANIFEST) \
		$(VCS_FILE_LIST_IDV) \
		$(VCS_FILE_LIST) \
		$(UVM_PLUSARGS)

comp: mk_vcs_dir $(CV_CORE_PKG) $(SVLIB_PKG)
	cd $(VCS_DIR) && $(VCS) $(VCS_COMP) -top uvmt_$(CV_CORE_LC)_tb
	@echo "$(BANNER)"
	@echo "* $(SIMULATOR) compile complete"
	@echo "* Log: $(SIM_CFG_RESULTS)/vcs.log"
	@echo "$(BANNER)"

ifneq ($(call IS_NO,$(COMP)),NO)
VCS_SIM_PREREQ = comp
endif

ifeq ($(call IS_YES,$(VCS_SINGLE_STEP)), YES)
	VCS_SIM_PREREQ = mk_vcs_dir $(CV_CORE_PKG) $(OVP_MODEL_DPI)
	VCS_COMP_RUN = $(VCS_COMP) $(VCS_RUN_BASE_FLAGS)
endif

################################################################################
# If the configuration specified OVPSIM arguments, generate an ovpsim.ic file and
# set IMPERAS_TOOLS to point to it
gen_ovpsim_ic:
	@rm -f $(SIM_RUN_RESULTS)/ovpsim.ic
	@mkdir -p $(SIM_RUN_RESULTS)
	@touch $(SIM_RUN_RESULTS)/ovpsim.ic
	@if [ ! -z "$(CFG_OVPSIM)" ]; then \
		echo "$(CFG_OVPSIM)" > $(SIM_RUN_RESULTS)/ovpsim.ic; \
	fi

################################################################################
# The new general test target

test: $(VCS_SIM_PREREQ) hex gen_ovpsim_ic
	@echo "$(BANNER)"
	@echo "* Running simulation"
	@echo "* with VCS_RUN_FLAGS = $(VCS_RUN_FLAGS)"
	@echo "$(BANNER)"
	mkdir -p $(SIM_RUN_RESULTS)
	cd $(SIM_RUN_RESULTS) && \
	export IMPERAS_TOOLS=$(SIM_RUN_RESULTS)/ovpsim.ic && \
	export IMPERAS_QUEUE_LICENSE=1 && \
		$(VCS_DIR)/$(SIMV) \
                -l vcs-$(TEST)_$(GEN_START_INDEX)_$(GEN_NUM_TESTS).log \
		-cm_name $(TEST_RUN_NAME) \
		$(VCS_RUN_FLAGS) \
		$(CFG_PLUSARGS) \
		$(TEST_PLUSARGS) \
		$(TEST_CFG_FILE_PLUSARGS) \
		+UVM_TESTNAME=$(TEST_UVM_TEST) \
		+UVM_VERBOSITY=$(VCS_UVM_VERBOSITY) \
		+elf_file=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).elf \
		+firmware=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).hex \
		+itb_file=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).itb
	@echo "* Log: $(SIM_RUN_RESULTS)/vcs-$(TEST)_$(GEN_START_INDEX)_$(GEN_NUM_TESTS).log"
	$(POST_TEST)

###############################################################################
# Run a single test-program from the RISC-V Compliance Test-suite. The parent
# Makefile of this <sim>.mk implements "all_compliance", the target that
# compiles the test-programs.
#
# There is a dependancy between RISCV_ISA and COMPLIANCE_PROG which *you* are
# required to know.  For example, the I-ADD-01 test-program is part of the rv32i
# testsuite.
# So this works:
#                make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-ADD-01
# But this does not:
#                make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=I-ADD-01
#
RISCV_ISA       ?= rv32i
COMPLIANCE_PROG ?= I-ADD-01

SIG_ROOT      ?= $(SIM_CFG_RESULTS)/$(RISCV_ISA)
SIG           ?= $(SIM_CFG_RESULTS)/$(RISCV_ISA)/$(COMPLIANCE_PROG)_$(RUN_INDEX)/$(COMPLIANCE_PROG).signature_output
REF           ?= $(COMPLIANCE_PKG)/riscv-test-suite/$(RISCV_ISA)/references/$(COMPLIANCE_PROG).reference_output
TEST_PLUSARGS ?= +signature=$(COMPLIANCE_PROG).signature_output

ifneq ($(call IS_NO,$(COMP)),NO)
VCS_COMPLIANCE_PREREQ = comp build_compliance
endif

compliance: $(VCS_COMPLIANCE_PREREQ)
	mkdir -p $(SIM_RESULTS)/$(COMPLIANCE_PROG)_$(RUN_INDEX) && cd $(SIM_RESULTS)/$(COMPLIANCE_PROG)_$(RUN_INDEX)  && \
	export IMPERAS_TOOLS=$(CORE_V_VERIF)/$(CV_CORE_LC)/tests/cfg/ovpsim_no_pulp.ic && \
	$(SIM_RESULTS)/$(SIMV) -l vcs-$(COMPLIANCE_PROG).log -cm_test riscv-compliance $(VCS_COMP_RUN) $(TEST_PLUSARGS) \
		+UVM_TESTNAME=uvmt_$(CV_CORE_LC)_firmware_test_c \
		+firmware=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).hex \
		+elf_file=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).elf

################################################################################
# RISCOF RISCV-ARCH-TEST DUT simulation targets
VCS_RISCOF_SIM_PREREQ = $(RISCOF_TEST_RUN_DIR)/$(TEST).elf

comp_dut_riscof_sim:
	@echo "$(BANNER)"
	@echo "* Compiling vcs in $(SIM_RISCOF_ARCH_TESTS_RESULTS)"
	@echo "* Log: $(SIM_RISCOF_ARCH_TESTS_RESULTS)/vcs.log"
	@echo "$(BANNER)"
	mkdir -p $(SIM_RISCOF_ARCH_TESTS_RESULTS) && \
	cd $(SIM_RISCOF_ARCH_TESTS_RESULTS) && \
		$(VCS) $(VCS_COMP) -top uvmt_$(CV_CORE_LC)_tb

comp_dut_rtl_riscof_sim: $(CV_CORE_PKG) $(SVLIB_PKG) comp_dut_riscof_sim

setup_riscof_sim: clean_riscof_arch_test_suite clone_riscof_arch_test_suite comp_dut_rtl_riscof_sim

gen_riscof_ovpsim_ic:
	@touch $(RISCOF_TEST_RUN_DIR)/ovpsim.ic
	@if [ ! -z "$(CFG_OVPSIM)" ]; then \
		echo "$(CFG_OVPSIM)" > $(RISCOF_TEST_RUN_DIR)/ovpsim.ic; \
	fi

# Target to run RISCOF DUT sim with VCS
riscof_sim_run: $(VCS_RISCOF_SIM_PREREQ) comp_dut_rtl_riscof_sim gen_riscof_ovpsim_ic
	@echo "$(BANNER)"
	@echo "* Running vcs in $(RISCOF_TEST_RUN_DIR)"
	@echo "* Log: $(RISCOF_TEST_RUN_DIR)/vcs-$(TEST).log"
	@echo "$(BANNER)"
	cd $(RISCOF_TEST_RUN_DIR) && \
	export IMPERAS_TOOLS=$(RISCOF_TEST_RUN_DIR)/ovpsim.ic && \
	export IMPERAS_QUEUE_LICENSE=1 && \
		$(RISCOF_TEST_RUN_DIR)/$(SIMV) \
			-l vcs-$(TEST).log \
			-cm_name $(TEST) \
			$(VCS_RUN_FLAGS) \
			$(CFG_PLUSARGS) \
			$(RISCOF_TEST_PLUSARGS) \
			+UVM_TESTNAME=uvmt_cv32e40p_riscof_firmware_test_c \
			+UVM_VERBOSITY=$(VCS_UVM_VERBOSITY) \
			+firmware=$(TEST).hex \
			+elf_file=$(TEST).elf \
			+itb_file=$(TEST).itb
	@echo "* Log: $(RISCOF_TEST_RUN_DIR)/vcs-$(TEST).log"


###############################################################################
# Use Google instruction stream generator (RISCV-DV) to create new test-programs
comp_corev-dv: $(RISCVDV_PKG) $(CV_CORE_PKG)
	mkdir -p $(SIM_COREVDV_RESULTS)
	cd $(SIM_COREVDV_RESULTS) && \
	$(VCS) $(VCS_COMP_FLAGS) \
		$(QUIET) \
		$(VCS_UVM_ARGS) \
		$(VCS_USER_COMPILE_ARGS) \
		$(VCS_PMA_INC) \
		+incdir+$(CV_CORE_COREVDV_PKG)/target/$(CV_CORE_LC) \
		+incdir+$(RISCVDV_PKG)/user_extension \
		+incdir+$(COREVDV_PKG) \
		+incdir+$(CV_CORE_COREVDV_PKG) \
		-f $(CV_CORE_MANIFEST) \
		$(CFG_COMPILE_FLAGS) \
		-f $(COREVDV_PKG)/manifest.f \
		-l vcs.log

corev-dv: clean_riscv-dv clone_riscv-dv comp_corev-dv

gen_corev-dv: comp_corev-dv
	@echo "$(BANNER)"
	@echo "* Generating $(TEST) with corev-dv..."
	@echo "* with VCS_RUN_FLAGS = $(VCS_RUN_FLAGS) "
	@echo "$(BANNER)"
	mkdir -p $(SIM_COREVDV_RESULTS)/$(TEST)
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		mkdir -p $(SIM_TEST_RESULTS)/$$idx/test_program; \
	done
	cd  $(SIM_COREVDV_RESULTS)/$(TEST) && \
		../$(SIMV) -R $(VCS_RUN_FLAGS) \
			-l $(TEST)_$(GEN_START_INDEX)_$(GEN_NUM_TESTS).log \
			+start_idx=$(GEN_START_INDEX) \
			+num_of_tests=$(GEN_NUM_TESTS) \
			+UVM_TESTNAME=$(GEN_UVM_TEST) \
			+asm_file_name_opts=$(TEST) \
			+ldgen_cp_test_path=$(SIM_TEST_RESULTS) \
			$(CFG_PLUSARGS) \
			$(TEST_CFG_FILE_PLUSARGS) \
			$(GEN_PLUSARGS)
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		cp -f ${BSP}/link_corev-dv.ld ${SIM_TEST_RESULTS}/$$idx/test_program/link.ld; \
		cp ${SIM_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S ${SIM_TEST_RESULTS}/$$idx/test_program; \
	done

################################################################################
# Invoke post-process waveform viewer
waves:
	$(WAVES_CMD)

################################################################################
# Invoke post-process coverage viewer
cov_merge:
	$(MKDIR_P) $(SIM_CFG_RESULTS)/$(MERGED_COV_DIR)
	rm -rf $(SIM_CFG_RESULTS)/$(MERGED_COV_DIR)/*
	cd $(SIM_CFG_RESULTS)/$(MERGED_COV_DIR)

ifeq ($(call IS_YES,$(MERGE)),YES)
  COVERAGE_TARGET_DIR=$(SIM_CFG_RESULTS)/$(MERGED_COV_DIR)
else
  COVERAGE_TARGET_DIR=$(SIM_RUN_RESULTS)
endif

# the report is in html format: use a browser to access it when GUI mode is selected
ifeq ($(call IS_YES,$(GUI)),YES)
cov: $(COV_MERGE)
	cd $(COVERAGE_TARGET_DIR) && browse urgReport/dashboard.html
else
cov: $(COV_MERGE)
	cd $(COVERAGE_TARGET_DIR) && $(URG) $(COV_ARGS)
endif

###############################################################################
# Clean up your mess!

clean:
	@echo "$(MAKEFILE_LIST)"
	rm -rf $(SIM_RESULTS)

clean_test:
	@echo "Cleaning $(SIM_RUN_RESULTS)..."
	rm -rf $(SIM_RUN_RESULTS)

# Files created by Eclipse when using the Imperas ISS + debugger
clean_eclipse:
	rm  -f eguieclipse.log
	rm  -f idebug.log
	rm  -f stdout.txt
	rm  -rf workspace

clean_rtl:
	rm -rf $(CV_CORE_PKG)

# All generated files plus the clone of the RTL
clean_all: clean clean_test clean_rtl clean_eclipse clean_riscv-dv clean_test_programs clean_bsp clean_compliance clean_embench clean_dpi_dasm_spike clean_svlib
