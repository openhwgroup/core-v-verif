###############################################################################
#
# Copyright 2026 PlanV GmbH
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
# Verilator-specific Makefile for the Core-V-Verif "uvmt" testbench.
#
###############################################################################

# -------------------------------------
# Testbench setup
# -------------------------------------
VERILATOR := verilator
ifdef VERILATOR_ROOT
VERILATOR := $(VERILATOR_ROOT)/bin/verilator
endif

# UVM Tests and libraries
UVM_TEST ?= $(TEST_UVM_TEST)

ifndef UVM_ROOT
$(error UVM_ROOT is not set. Please export UVM_ROOT pointing to a UVM library root containing src/uvm.sv)
endif

# g++ >= 10 required for -fcoroutines (--timing support)
GXX_VER := $(shell g++ -dumpversion 2>/dev/null | cut -d. -f1)
ifeq ($(shell test $(GXX_VER) -lt 10 2>/dev/null && echo yes),yes)
$(error g++ >= 10 required for -fcoroutines support (found: g++ $(GXX_VER)))
endif
VERILOG_DEFINE_FILES ?=
UVM_FILES += ${UVM_ROOT}/src/uvm.sv
VERILOG_INCLUDE_DIRS = ${UVM_ROOT}/src $(DV_UVME_PATH) $(DV_UVMT_PATH)

# -------------------------------------
# Compilation/simulation configuration
# -------------------------------------
SIM_NAME ?= $(RTLSRC_VLOG_TB_TOP)
SIM_DIR := $(SIM_NAME)-sim
COMPILE_ARGS += -DUVM_NO_DPI +define+UVM_ENABLE_DEPRECATED_API
COMPILE_ARGS += --prefix $(SIM_NAME) -o $(SIM_NAME)

INC_ARGS += $(addprefix +incdir+, $(VERILOG_INCLUDE_DIRS))
SRC_ARGS += $(UVM_FILES)
UVMT_FLIST     := $(DV_UVMT_PATH)/uvmt_$(CV_CORE_LC).flist
UVMT_FLIST_VLT := $(SIM_DIR)/uvmt_$(CV_CORE_LC)_verilator.flist
SRC_ARGS +=  -F $(CV_CORE_MANIFEST) -F $(UVMT_FLIST_VLT)
SRC_ARGS += $(addprefix -f , $(VERILOG_DEFINE_FILES))

EXTRA_ARGS += --timescale 1ns/1ps --error-limit 10000 +define+VERILATOR_SIM
WARNING_ARGS += -Wno-lint \
	-Wno-style \
	-Wno-SYMRSVDWORD \
	-Wno-IGNOREDRETURN \
	-Wno-COVERIGN \
	-Wno-ZERODLY \
	-Wno-COMBDLY \
	-Wno-UNOPTFLAT \
	-Wno-BADSTDPRAGMA \
	-Wwarn-CONSTRAINTIGN

# -------------------------------------
# Some Useful args for debugging
# -------------------------------------
ifeq ($(json_dump),1)
	EXTRA_ARGS += -dump-tree-json
else
endif
ifeq ($(debug),1)
	EXTRA_ARGS += --debug --gdbbt -CFLAGS -DVL_DEBUG=1
else
endif

# -------------------------------------
# Make UVM test with Verilator
# -------------------------------------

.PHONY: verilate comp run simulate clean test

test: VERI_SIM_FLAGS += +firmware=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).hex
# test: VERI_SIM_FLAGS += +elf_file=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).elf
test: hex run

verilate:
	echo "UVM_TEST = $(UVM_TEST)"
	mkdir -p veri_results $(SIM_DIR)
	sed -e '\|svlib_pkg\.flist$$|d' \
	    -e '\|uvmt_cv32e40p_interrupt_assert\.sv$$|d' \
	    -e '\|uvmt_cv32e40p_debug_assert\.sv$$|d' \
	    $(UVMT_FLIST) > $(UVMT_FLIST_VLT)
	$(VERILATOR) --cc --exe --main --trace --trace-structs --timing -Mdir $(SIM_DIR) \
	${COMPILE_ARGS} ${EXTRA_ARGS} \
	${INC_ARGS} \
	${SRC_ARGS} \
	${WARNING_ARGS} > veri_results/verilate.log 2>&1

comp: verilate
	$(MAKE) -j${NPROC} -C $(SIM_DIR) $(BUILD_ARGS) -f $(SIM_NAME).mk

run: comp
	$(SIM_DIR)/$(SIM_NAME) +UVM_TESTNAME=$(UVM_TEST) $(VERI_SIM_FLAGS) +UVM_VERBOSITY=UVM_LOW

clean:
	rm -rf simv*.daidir csrc
	rm -rf csrc* simv*
	rm -rf $(SIM_DIR)
	rm -rf dump.vcd
