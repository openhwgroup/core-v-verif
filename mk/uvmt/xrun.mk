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
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
###############################################################################
#
# XRUN-specific Makefile for any uvmt testbench.
# XRUN is the Cadence Xcelium SystemVerilog simulator (https://cadence.com/)
#
###############################################################################

#
# Cadence do not (officially) support Ubuntu, so suppress the nonzero return code from XRUN
#
OS_IS_UBUNTU = $(findstring Ubuntu,$(shell lsb_release -d))
ifeq ($(OS_IS_UBUNTU),Ubuntu)
    .IGNORE: hello-world comp test comp_corev-dv corev-dv gen_corev-dv
endif

# Executables
XRUN              = $(CV_SIM_PREFIX) xrun
SIMVISION         = $(CV_TOOL_PREFIX) simvision
INDAGO            = $(CV_TOOL_PREFIX) indago
IMC               = $(CV_SIM_PREFIX) imc

XRUN_UVMHOME_ARG     ?= CDNS-1.2-ML

# Flags
XRUN_COMP_FLAGS  ?= -64bit \
					-disable_sem2009 \
					-access +rwc \
                    -nowarn UEXPSC \
					-lwdgen \
                    -sv \
					-uvm \
					-uvmhome $(XRUN_UVMHOME_ARG) \
                    $(TIMESCALE) \
					$(SV_CMP_FLAGS)

XRUN_LDGEN_COMP_FLAGS ?= -64bit -disable_sem2009 -access +rwc \
												 -nowarn UEXPSC \
												 -nowarn DLCPTH \
												 -sv \
												 $(TIMESCALE) $(SV_CMP_FLAGS)

XRUN_RUN_BASE_FLAGS ?= -64bit $(XRUN_GUI) -licqueue +UVM_VERBOSITY=$(XRUN_UVM_VERBOSITY) \
                       $(XRUN_PLUSARGS) -svseed $(RNDSEED)
XRUN_GUI         ?=
XRUN_SINGLE_STEP ?=
XRUN_ELAB_COV     = -covdut uvmt_$(CV_CORE_LC)_tb -coverage b:e:f:u
XRUN_ELAB_COVFILE = -covfile $(abspath $(MAKE_PATH)/../tools/xrun/covfile.tcl)
XRUN_RUN_COV      = -covscope uvmt_$(CV_CORE_LC)_tb \
					-nowarn CGDEFN \
					+uvm_set_config_int=uvm_test_top,cov_model_enabled,1
XRUN_RUN_BASE_FLAGS += -sv_lib $(DPI_DASM_LIB)
XRUN_RUN_BASE_FLAGS += -sv_lib $(abspath $(SVLIB_LIB))

XRUN_UVM_VERBOSITY ?= UVM_MEDIUM

# Special var to point to tool and installation dependent path of DPI headers.
# Used to recompile dpi_dasm_spike if needed (by default, not needed).
DPI_INCLUDE        ?= $(shell dirname $(shell which xrun))/../include

# Necessary libraries for the PMA generator class
XRUN_PMA_INC += +incdir+$(TBSRC_HOME)/uvmt \
                +incdir+$(CV_CORE_PKG)/rtl/include \
                +incdir+$(CV_CORE_COREVDV_PKG)/ldgen \
                +incdir+$(abspath $(MAKE_PATH)/../../../lib/mem_region_gen)

###############################################################################
# Common QUIET flag defaults to -quiet unless VERBOSE is set
ifeq ($(call IS_YES,$(VERBOSE)),YES)
QUIET=
else
QUIET=-quiet
endif

################################################################################
# GUI interactive simulation
# GUI=YES enables interactive mode
# ADV_DEBUG=YES will enable Indago, default is to use SimVision
ifeq ($(call IS_YES,$(GUI)),YES)
XRUN_GUI += -gui
XRUN_USER_COMPILE_ARGS += -linedebug
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
XRUN_GUI += -indago
endif
endif

################################################################################
# Waveform generation
# WAVES=YES enables waveform generation for entire testbench
# WAVES_MEM=YES enables tracing memories and large vectors
# ADV_DEBUG=YES will enable Indago waves, default is to generate SimVision waves
ifeq ($(call IS_YES,$(WAVES_MEM)),YES)
  ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
    XRUN_RUN_WAVES_FLAGS = -input $(abspath $(MAKE_PATH)/../tools/xrun/indago_mem.tcl)
  else
    XRUN_RUN_WAVES_FLAGS = -input $(abspath $(MAKE_PATH)/../tools/xrun/probe_mem.tcl)
  endif
else
  ifeq ($(call IS_YES,$(WAVES)),YES)
    ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
      XRUN_RUN_WAVES_FLAGS = -input $(abspath $(MAKE_PATH)/../tools/xrun/indago.tcl)
    else
      XRUN_RUN_WAVES_FLAGS = -input $(abspath $(MAKE_PATH)/../tools/xrun/probe.tcl)
    endif
  endif
endif

################################################################################
# Waveform (post-process) command line
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
WAVES_CMD = cd $(SIM_RUN_RESULTS) && $(INDAGO) -db ida.db &
else
WAVES_CMD = cd $(SIM_RUN_RESULTS) && $(SIMVISION) waves.shm &
endif

XRUN_USER_COMPILE_ARGS += $(USER_COMPILE_FLAGS)

################################################################################
# Coverage options
# COV=YES generates coverage database, must be specified for comp and run
IMC_MERGE_ARGS = merge -initial_model union_all -overwrite -message 1
IMC_REPORT_ARGS = -exec $(CORE_V_VERIF)/$(CV_CORE)/sim/tools/xrun/cov_report.tcl
MERGED_COV_DIR ?= merged_cov

ifeq ($(call IS_YES,$(COV)),YES)
XRUN_ELAB_COV_FLAGS += $(XRUN_ELAB_COV)
XRUN_ELAB_COV_FLAGS += $(XRUN_ELAB_COVFILE)
XRUN_RUN_COV_FLAGS += $(XRUN_RUN_COV)
endif

# Find command to gather ucd files
COV_MERGE_FIND = find "$(SIM_CFG_RESULTS)" -type f -name "*.ucd" | grep -v d_cov | xargs dirname

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_MERGE = cov_merge
TEST = $(MERGED_COV_DIR)
else
COV_MERGE =
endif

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_DIR ?= $(XRUN_RESULTS)/$(CFG)/$(MERGED_COV_DIR)/cov_work/scope/merged
else
COV_DIR ?= cov_work/uvmt_$(CV_CORE_LC)_tb/$(TEST_RUN_NAME)
endif

ifeq ($(call IS_YES,$(GUI)),YES)
COV_ARGS += -gui
else
COV_ARGS += $(IMC_REPORT_ARGS)
endif


ifeq ($(call IS_YES,$(CHECK_SIM_RESULT)),YES)
CHECK_SIM_LOG ?= $(abspath $(SIM_RUN_RESULTS))/xrun-$(TEST_RUN_NAME).log
POST_TEST = \
	@if grep -q "SIMULATION FAILED" $(CHECK_SIM_LOG); then \
		exit 1; \
	fi
endif

################################################################################

# File to `include "uvm_macros.svh" since Xcelium automatic UVM compilation
# does not source the macros file.
XRUN_UVM_MACROS_INC_FILE = $(DV_UVMT_PATH)/uvmt_$(CV_CORE_LC)_uvm_macros_inc.sv

XRUN_FILE_LIST ?= -f $(DV_UVMT_PATH)/uvmt_$(CV_CORE_LC).flist
XRUN_USER_COMPILE_ARGS += +define+$(CV_CORE_UC)_RVFI +define+$(CV_CORE_UC)_RVVI

ifeq ($(call IS_YES,$(ENABLE_TRACE_LOG)),YES)
    XRUN_USER_COMPILE_ARGS += +define+$(CV_CORE_UC)_TRACE_EXECUTION
    XRUN_USER_COMPILE_ARGS += +define+$(CV_CORE_UC)_RVFI_TRACE_EXECUTION
endif

XRUN_USER_COMPILE_ARGS += +define+$(CV_CORE_UC)_CORE_LOG
XRUN_USER_COMPILE_ARGS += +define+UVM
ifeq ($(call IS_YES,$(USE_ISS)),YES)
	XRUN_PLUSARGS += +USE_ISS
	XRUN_PLUSARGS += +USE_IMPERASDV
	XRUN_RUN_BASE_FLAGS += -sv_lib $(IMPERAS_DV_MODEL)
	XRUN_FILE_LIST_IDV ?= -f $(DV_UVMT_PATH)/imperas_dv.flist
	XRUN_USER_COMPILE_ARGS += +define+USE_IMPERASDV
	XRUN_USER_COMPILE_ARGS += +define+USE_ISS
ifeq ($(call IS_YES,$(COV)),YES)
	XRUN_USER_COMPILE_ARGS += +define+IMPERAS_COV
	XRUN_PLUSARGS += +IDV_TRACE2COV=1
endif
else
    XRUN_PLUSARGS += +DISABLE_OVPSIM
	XRUN_FILE_LIST_IDV ?=
endif
ifeq ($(call IS_YES,$(USE_RVVI)),YES)
    XRUN_PLUSARGS +="+USE_RVVI"
endif
ifeq ($(call IS_YES,$(TEST_DISABLE_ALL_CSR_CHECKS)),YES)
    XRUN_PLUSARGS +="+DISABLE_ALL_CSR_CHECKS"
endif
ifneq ($(TEST_DISABLE_CSR_CHECK),)
	XRUN_PLUSARGS += +DISABLE_CSR_CHECK=$(TEST_DISABLE_CSR_CHECK)
endif

# Simulate using latest elab
XRUN_RUN_FLAGS        ?=
XRUN_RUN_FLAGS        += -covoverwrite
XRUN_RUN_FLAGS        += $(XRUN_RUN_BASE_FLAGS)
XRUN_RUN_FLAGS        += $(XRUN_RUN_COV_FLAGS)
XRUN_RUN_FLAGS        += $(XRUN_USER_RUN_FLAGS)
XRUN_RUN_FLAGS        += $(USER_RUN_FLAGS)

###############################################################################
# Xcelium warning suppression

# Xcelium constraint solver
XRUN_RUN_FLAGS  += -nowarn XCLGNOPTM
XRUN_RUN_FLAGS  += -nowarn RNDNOXCEL

# Probes
XRUN_RUN_FLAGS  += -nowarn PRLDYN

# Physical repository related to logical library in a cds.lib does not exist
XRUN_COMP_FLAGS += -nowarn DLCPTH

# Allow extra semicolons
XRUN_COMP_FLAGS += -nowarn UEXPSC

# SOP expression evaluates to a constant - remove from coverage calculation
XRUN_COMP_FLAGS += -nowarn COVSEC

# Warning that no timescale defined for package, this is by design as no
# core-v-verif code should contain its own timescale
XRUN_COMP_FLAGS += -nowarn TSNSPK

# Warning on expression coverage speedup (only counts always blocks in expression if output changes)
XRUN_COMP_FLAGS += -nowarn COVVPO
XRUN_RUN_COV    += -nowarn COVVPO

# Warning on adding _T suffix to named block scoped assertion coverage
XRUN_RUN_FLAGS  += -nowarn COVNBT

# Warning about new style struct expression scoring
XRUN_COMP_FLAGS += -nowarn COVEOS

# +incdir in -f file not used
XRUN_COMP_FLAGS += -nowarn SPDUSD

# scoring events not included in expression coverage
XRUN_COMP_FLAGS += -nowarn COVNSO

# instance reporting warings for covergroups
XRUN_COMP_FLAGS += -nowarn COVCGN
XRUN_COMP_FLAGS += -nowarn CGPIZE

# per_instance option is 0
XRUN_COMP_FLAGS += -nowarn CGPIDF

# deselect_coverage -all warnings
XRUN_COMP_FLAGS += -nowarn CGNSWA

# deselect_coverage -all warnings
XRUN_COMP_COREV_DV_FLAGS += -nowarn BNDWRN
XRUN_COMP_COREV_DV_FLAGS += $(CFG_COMPILE_FLAGS)
XRUN_COMP_COREV_DV_FLAGS += $(GEN_COMPILE_FLAGS)

# instance reporting warings for covergroups
XRUN_RUN_COV    += -nowarn COVCGN
XRUN_RUN_COV    += -nowarn CGPIZE

# Empty overgroup warnings (we purposely empty covergroups as part of filtering w/ configuration variables)
XRUN_RUN_COV    += -nowarn WCRTUP
XRUN_RUN_COV    += -nowarn WCOVPT
XRUN_RUN_COV    += -nowarn WCROSS

# Un-named covergroup instances
XRUN_RUN_COV    += -nowarn CGDEFN

###############################################################################
# Targets

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=xrun sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'

help:
	xrun -help

.PHONY: comp test waves cov ldgen

mk_xrun_dir:
	$(MKDIR_P) $(SIM_CFG_RESULTS)

# This special target is to support the special sanity target in the Common Makefile
hello-world:
	$(MAKE) test TEST=hello-world

XRUN_COMP = $(XRUN_COMP_FLAGS) \
		$(QUIET) \
		$(CFG_COMPILE_FLAGS) \
		$(XRUN_USER_COMPILE_ARGS) \
		+incdir+$(DV_UVME_PATH) \
		+incdir+$(DV_UVMT_PATH) \
		$(XRUN_UVM_MACROS_INC_FILE) \
		-f $(CV_CORE_MANIFEST) \
		$(XRUN_FILE_LIST_IDV) \
		$(XRUN_FILE_LIST) \
		$(UVM_PLUSARGS)

comp: mk_xrun_dir $(CV_CORE_PKG) $(SVLIB_PKG)
	@echo "$(BANNER)"
	@echo "* Compiling xrun in $(SIM_CFG_RESULTS)"
	@echo "* Log: $(SIM_CFG_RESULTS)/xrun.log"
	@echo "$(BANNER)"
	cd $(SIM_CFG_RESULTS) && $(XRUN) \
		$(XRUN_COMP) \
		$(XRUN_ELAB_COV_FLAGS) \
		-top $(RTLSRC_VLOG_TB_TOP) \
		-l xrun.log \
		-elaborate

ifneq ($(call IS_NO,$(COMP)),NO)
XRUN_SIM_PREREQ = comp
endif

XRUN_COMP_RUN = $(XRUN_RUN_FLAGS)

ifeq ($(call IS_YES,$(XRUN_SINGLE_STEP)), YES)
  XRUN_SIM_PREREQ = mk_xrun_dir $(CV_CORE_PKG)
  XRUN_COMP_RUN = $(XRUN_COMP) $(XRUN_RUN_BASE_FLAGS)
endif

################################################################################
# Linker script generator targets
#
# Standalone tb that generates appropriate linker files based on a given pma
# configuration. Uses same code as the generator embedded in corev-dv.

ldgen: $(CV_CORE_PKG)
	@echo "$(BANNER)"
	@echo "* Generating linker scripts in $(SIM_LDGEN_RESULTS)"
	@echo "* Log: $(SIM_LDGEN_RESULTS)/xrun-ldgen.log"
	@echo "$(BANNER)"
	$(MKDIR_P) $(SIM_LDGEN_RESULTS)/xcelium.d && \
	cd $(SIM_LDGEN_RESULTS)/xcelium.d && \
	$(XRUN) \
		-l xrun-ldgen.log \
		$(XRUN_LDGEN_COMP_FLAGS)\
		$(XRUN_PMA_INC) \
		$(CFG_PLUSARGS) \
		$(CFG_COMPILE_FLAGS) \
		+ldgen_cp_test_path=$(SIM_LDGEN_RESULTS) \
		$(TBSRC_HOME)/ldgen/ldgen_tb.sv \
		-top $(basename $(notdir $(TBSRC_HOME)/ldgen/ldgen_tb.sv))
	cp $(BSP)/link_pma.ld $(SIM_LDGEN_RESULTS)/link.ld

################################################################################
# If the configuration specified OVPSIM arguments, generate an ovpsim.ic file and
# set IMPERAS_TOOLS to point to it
gen_ovpsim_ic:
	@rm -f $(SIM_RUN_RESULTS)/ovpsim.ic
	@mkdir -p $(SIM_RUN_RESULTS);
	@touch -f $(SIM_RUN_RESULTS)/ovpsim.ic
	@if [ ! -z "$(CFG_OVPSIM)" ]; then \
		echo "$(CFG_OVPSIM)" > $(SIM_RUN_RESULTS)/ovpsim.ic; \
	fi
	# add glossing of registers
	#@echo "--override cpu/wfi_is_nop=T" >> $(SIM_CFG_RESULTS)/$(TEST_NAME)/$(RUN_INDEX)/ovpsim.ic
	#@echo "--override cpu/sub_Extensions=X" >> $(SIM_CFG_RESULTS)/$(TEST_NAME)/$(RUN_INDEX)/ovpsim.ic
	#@echo "--showoverrides --trace --tracechange --traceshowicount --monitornetschange --tracemode --tracemem XSA" >> $(SIM_CFG_RESULTS)/$(TEST_NAME)/$(RUN_INDEX)/ovpsim.ic
	#@echo "--extlib refRoot/cpu/cat=imperas.com/intercept/cpuContextAwareTracer/1.0"  >> $(SIM_CFG_RESULTS)/$(TEST_NAME)/$(RUN_INDEX)/ovpsim.ic
	#@echo "--override refRoot/cpu/cat/show_changes=T" >> $(SIM_CFG_RESULTS)/$(TEST_NAME)/$(RUN_INDEX)/ovpsim.ic
	#@echo "--override refRoot/cpu/cat/definitions_file=${IMPERAS_HOME}/lib/$(IMPERAS_ARCH)/ImperasLib/riscv.ovpworld.org/processor/riscv/1.0/csr_context_info.lis" >> $(SIM_CFG_RESULTS)/$(TEST_NAME)/$(RUN_INDEX)/ovpsim.ic

################################################################################
# The new general test target

test: $(XRUN_SIM_PREREQ) hex gen_ovpsim_ic
	@echo "$(BANNER)"
	@echo "* Running xrun in $(SIM_RUN_RESULTS)"
	@echo "* Log: $(SIM_RUN_RESULTS)/xrun-$(TEST_NAME).log"
	@echo "$(BANNER)"
	mkdir -p $(SIM_RUN_RESULTS)/test_program && \
	cd $(SIM_RUN_RESULTS) && \
	export IMPERAS_TOOLS=$(SIM_RUN_RESULTS)/ovpsim.ic && \
	export IMPERAS_QUEUE_LICENSE=1 && \
	$(XRUN) \
		-R -xmlibdirname $(SIM_CFG_RESULTS)/xcelium.d \
		-l xrun-$(TEST_RUN_NAME).log \
		$(XRUN_COMP_RUN) \
		$(XRUN_RUN_WAVES_FLAGS) \
		-covtest $(TEST_RUN_NAME) \
		$(CFG_PLUSARGS) \
		$(TEST_PLUSARGS) \
		$(TEST_CFG_FILE_PLUSARGS) \
		+UVM_TESTNAME=$(TEST_UVM_TEST) \
		+elf_file=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).elf \
		+firmware=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).hex \
		+itb_file=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).itb \
		+nm_file=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).nm
	@echo "* Log: $(SIM_RUN_RESULTS)/xrun-$(TEST_NAME).log"
	$(POST_TEST)


################################################################################
# RISCOF RISCV-ARCH-TEST DUT simulation targets
XRUN_RISCOF_SIM_PREREQ = $(RISCOF_TEST_RUN_DIR)/$(TEST).elf

comp_dut_riscof_sim:
	@echo "$(BANNER)"
	@echo "* Compiling xrun in $(SIM_RISCOF_ARCH_TESTS_RESULTS)"
	@echo "* Log: $(SIM_RISCOF_ARCH_TESTS_RESULTS)/xrun.log"
	@echo "$(BANNER)"
	mkdir -p $(SIM_RISCOF_ARCH_TESTS_RESULTS) && \
	cd $(SIM_RISCOF_ARCH_TESTS_RESULTS) && $(XRUN) \
		$(XRUN_COMP) \
		$(XRUN_ELAB_COV_FLAGS) \
		-top $(RTLSRC_VLOG_TB_TOP) \
		-l xrun.log \
		-elaborate

comp_dut_rtl_riscof_sim: $(CV_CORE_PKG) $(SVLIB_PKG) comp_dut_riscof_sim

setup_riscof_sim: clean_riscof_arch_test_suite clone_riscof_arch_test_suite comp_dut_rtl_riscof_sim

gen_riscof_ovpsim_ic:
	@touch -f $(RISCOF_TEST_RUN_DIR)/ovpsim.ic
	@if [ ! -z "$(CFG_OVPSIM)" ]; then \
		echo "$(CFG_OVPSIM)" > $(RISCOF_TEST_RUN_DIR)/ovpsim.ic; \
	fi

# Target to run RISCOF DUT sim with XRUN
riscof_sim_run: $(XRUN_RISCOF_SIM_PREREQ) comp_dut_rtl_riscof_sim gen_riscof_ovpsim_ic
	@echo "$(BANNER)"
	@echo "* Running xrun in $(RISCOF_TEST_RUN_DIR)"
	@echo "* Log: $(RISCOF_TEST_RUN_DIR)/xrun-$(TEST).log"
	@echo "$(BANNER)"
	cd $(RISCOF_TEST_RUN_DIR) && \
	export IMPERAS_TOOLS=$(RISCOF_TEST_RUN_DIR)/ovpsim.ic && \
	export IMPERAS_QUEUE_LICENSE=1 && \
	$(XRUN) \
		-R -xmlibdirname xcelium.d \
		-l xrun-$(TEST).log \
		$(XRUN_COMP_RUN) \
		$(XRUN_RUN_WAVES_FLAGS) \
		-covtest $(TEST) \
		+UVM_TESTNAME=uvmt_cv32e40p_riscof_firmware_test_c \
		$(CFG_PLUSARGS) \
		$(RISCOF_TEST_PLUSARGS) \
		+firmware=$(TEST).hex \
		+elf_file=$(TEST).elf \
		+itb_file=$(TEST).itb
	@echo "* Log: $(RISCOF_TEST_RUN_DIR)/xrun-$(TEST).log"


###############################################################################
# Use Google instruction stream generator (RISCV-DV) to create new test-programs
comp_corev-dv: $(RISCVDV_PKG) $(CV_CORE_PKG)
	mkdir -p $(SIM_COREVDV_RESULTS)
	cd $(SIM_COREVDV_RESULTS) && \
	$(XRUN) $(XRUN_COMP_FLAGS) \
		-xmlibdirname ./xcelium.d \
		$(QUIET) \
		$(XRUN_USER_COMPILE_ARGS) \
		$(XRUN_PMA_INC) \
		$(XRUN_COMP_COREV_DV_FLAGS) \
		$(XRUN_UVM_MACROS_INC_FILE) \
		-f $(CV_CORE_MANIFEST) \
		-top $(CV_CORE_LC)_instr_gen_tb_top \
		-elaborate \
		+incdir+$(CV_CORE_COREVDV_PKG)/target/$(CV_CORE_LC) \
		+incdir+$(RISCVDV_PKG)/user_extension \
		+incdir+$(COREVDV_PKG) \
		+incdir+$(CV_CORE_COREVDV_PKG) \
		-f $(COREVDV_PKG)/manifest.f \
		-l xrun.log

corev-dv: clean_riscv-dv \
          clone_riscv-dv \
	      comp_corev-dv

# Copy (with cleanout) out final assembler files to test directory
# This includes the generated linker script files if they are present in the
# generated tests folder
gen_corev-dv: comp_corev-dv
	mkdir -p $(SIM_COREVDV_RESULTS)/$(TEST)
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		mkdir -p $(SIM_TEST_RESULTS)/$$idx/test_program; \
	done
	cd $(SIM_COREVDV_RESULTS)/$(TEST) && \
		$(XRUN) -R -xmlibdirname ../xcelium.d \
			$(XRUN_RUN_FLAGS) \
			-xceligen rand_struct \
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
	$(COV_MERGE_FIND) > $(SIM_CFG_RESULTS)/$(MERGED_COV_DIR)/ucd.list
	cd $(SIM_CFG_RESULTS)/$(MERGED_COV_DIR) && \
	$(IMC) -execcmd "$(IMC_MERGE_ARGS) -runfile ucd.list -out merged; exit"

ifeq ($(call IS_YES,$(MERGE)),YES)
  COVERAGE_TARGET_DIR=$(SIM_CFG_RESULTS)/$(MERGED_COV_DIR)
else
  COVERAGE_TARGET_DIR=$(SIM_RUN_RESULTS)
endif

cov: $(COV_MERGE)
	cd $(COVERAGE_TARGET_DIR) && \
		IMC_PAGE_VIEWS_DIR=$(CORE_V_VERIF)/$(CV_CORE)/sim/tools/xrun \
			$(IMC) -load $(COV_DIR) $(COV_ARGS)

###############################################################################
# Clean up your mess!

clean:
	@echo "$(MAKEFILE_LIST)"
	rm -rf $(SIM_RESULTS)

clean_test:
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
clean_all: clean clean_rtl clean_eclipse clean_riscv-dv clean_test_programs clean_bsp clean_embench clean_dpi_dasm_spike clean_svlib clean_riscof_arch_test_suite
