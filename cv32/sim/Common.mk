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
# Common code for simulation Makefiles.  Intended to be included by the
# Makefiles in the "core" and "uvmt_cv32" dirs.
#
###############################################################################
# 
# Copyright 2019 Clifford Wolf
# Copyright 2019 Robert Balas
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
# REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
# AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
# INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
# LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
# OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
# PERFORMANCE OF THIS SOFTWARE.
#
# Original Author: Robert Balas (balasr@iis.ee.ethz.ch)
#
###############################################################################

###############################################################################
# Variables to determine the the command to clone external repositories.
# For each repo there are a set of variables:
#      *_REPO:   URL to the repository in GitHub.
#      *_BRANCH: Name of the branch you wish to clone;
#                Set to 'master' to pull the master branch.
#      *_HASH:   Value of the specific hash you wish to clone;
#                Set to 'head' to pull the head of the branch you want.
#      *_TAG:    Not yet supported (coming soon).
#                
#CV32E40P_REPO   ?= https://github.com/openhwgroup/cv32e40p
#CV32E40P_BRANCH ?= master
#CV32E40P_HASH   ?= head
CV32E40P_REPO   ?= https://github.com/openhwgroup/cv32e40p
CV32E40P_BRANCH ?= master
CV32E40P_HASH   ?= 62073bb3c8c5073203b16a24df9f6cef8958cba6 

FPNEW_REPO      ?= https://github.com/pulp-platform/fpnew
FPNEW_BRANCH    ?= master
FPNEW_HASH      ?= c15c54887b3bc6d0965606c487e9f1bf43237e45

RISCVDV_REPO    ?= https://github.com/google/riscv-dv
RISCVDV_BRANCH  ?= master
RISCVDV_HASH    ?= head

# Generate command to clone the CV32E40P RTL
ifeq ($(CV32E40P_BRANCH), master)
  TMP = git clone $(CV32E40P_REPO) --recurse $(CV32E40P_PKG)
else
  TMP = git clone -b $(CV32E40P_BRANCH) --single-branch $(CV32E40P_REPO) --recurse $(CV32E40P_PKG)
endif

ifeq ($(CV32E40P_HASH), head)
  CLONE_CV32E40P_CMD = $(TMP)
else
  CLONE_CV32E40P_CMD = $(TMP); cd $(CV32E40P_PKG); git checkout $(CV32E40P_HASH)
endif

# Generate command to clone the FPNEW RTL
ifeq ($(FPNEW_BRANCH), master)
  TMP2 = git clone $(FPNEW_REPO) --recurse $(FPNEW_PKG)
else
  TMP2 = git clone -b $(FPNEW_BRANCH) --single-branch $(FPNEW_REPO) --recurse $(FPNEW_PKG)
endif

ifeq ($(FPNEW_HASH), head)
  CLONE_FPNEW_CMD = $(TMP2)
else
  CLONE_FPNEW_CMD = $(TMP2); cd $(FPNEW_PKG); git checkout $(FPNEW_HASH)
endif
# RTL repo vars end

# Generate command to clone RISCV-DV (Google's random instruction generator)
ifeq ($(RISCVDV_BRANCH), master)
  TMP3 = git clone $(RISCVDV_REPO) --recurse $(RISCVDV_PKG)
else
  TMP3 = git clone -b $(RISCVDV_BRANCH) --single-branch $(RISCVDV_REPO) --recurse $(RISCVDV_PKG)
endif

ifeq ($(RISCVDV_HASH), head)
  CLONE_RISCVDV_CMD = $(TMP3)
else
  CLONE_RISCVDV_CMD = $(TMP3); cd $(RISCVDV_PKG); git checkout $(RISCVDV_HASH)
endif
# RISCV-DV repo var end

###############################################################################
# Build "firmware" for the CV32E40P "core" testbench and "uvmt_cv32"
# verification environment.  Substantially modified from the original from the
# Makefile first developed for the PULP-Platform RI5CY testbench.
#
# riscv toolchain install path
RISCV                   ?= /opt/riscv
RISCV_EXE_PREFIX         = $(RISCV)/bin/riscv32-unknown-elf-

# CORE FIRMWARE vars. All of the C and assembler programs under CORE_TEST_DIR
# are collectively known as "Core Firmware".  Yes, this is confusing because
# one of sub-directories of CORE_TEST_DIR is called "firmware".
#
# Note that the DSIM targets allow for writing the log-files to arbitrary
# locations, so all of these paths are absolute, except those used by Verilator.
# TODO: clean this mess up!
CORE_TEST_DIR                        = $(PROJ_ROOT_DIR)/cv32/tests/core
FIRMWARE                             = $(CORE_TEST_DIR)/firmware
VERI_FIRMWARE                        = ../../tests/core/firmware
CUSTOM                               = $(CORE_TEST_DIR)/custom
CUSTOM_DIR                          ?= $(CUSTOM)
CUSTOM_PROG                         ?= my_hello_world
VERI_CUSTOM                          = ../../tests/core/custom
CV32_RISCV_TESTS_FIRMWARE            = $(CORE_TEST_DIR)/cv32_riscv_tests_firmware
CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE = $(CORE_TEST_DIR)/cv32_riscv_compliance_tests_firmware
RISCV_TESTS                          = $(CORE_TEST_DIR)/riscv_tests
RISCV_TEST_INCLUDES                  = -I$(CORE_TEST_DIR)/riscv_tests/ \
                                       -I$(CORE_TEST_DIR)/riscv_tests/macros/scalar \
                                       -I$(CORE_TEST_DIR)/riscv_tests/rv64ui \
                                       -I$(CORE_TEST_DIR)/riscv_tests/rv64um
CV32_RISCV_TESTS_FIRMWARE_OBJS       = $(addprefix $(CV32_RISCV_TESTS_FIRMWARE)/, \
                                         start.o print.o sieve.o multest.o stats.o)
RISCV_TESTS_OBJS         = $(addsuffix .o, \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32ui/*.S)) \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32um/*.S)) \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32uc/*.S)))
FIRMWARE_OBJS            = $(addprefix $(FIRMWARE)/, \
                             start.o print.o sieve.o multest.o stats.o)
FIRMWARE_TEST_OBJS       = $(addsuffix .o, \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32ui/*.S)) \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32um/*.S)) \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32uc/*.S)))
FIRMWARE_SHORT_TEST_OBJS = $(addsuffix .o, \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32ui/*.S)) \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32um/*.S)))

# Thales verilator testbench compilation start

SUPPORTED_COMMANDS := vsim-firmware-unit-test questa-unit-test questa-unit-test-gui dsim-unit-test 
SUPPORTS_MAKE_ARGS := $(findstring $(firstword $(MAKECMDGOALS)), $(SUPPORTED_COMMANDS))

ifneq "$(SUPPORTS_MAKE_ARGS)" ""
  UNIT_TEST := $(wordlist 2,$(words $(MAKECMDGOALS)),$(MAKECMDGOALS))
  $(eval $(UNIT_TEST):;@:)
  UNIT_TEST_CMD := 1
else 
 UNIT_TEST_CMD := 0
endif

COMPLIANCE_UNIT_TEST = $(subst _,-,$(UNIT_TEST))

FIRMWARE_UNIT_TEST_OBJS   =  	$(addsuffix .o, \
				$(basename $(wildcard $(RISCV_TESTS)/rv32*/$(UNIT_TEST).S)) \
				$(basename $(wildcard $(RISCV_COMPLIANCE_TESTS)*/$(COMPLIANCE_UNIT_TEST).S)))

# Thales verilator testbench compilation end

###############################################################################
#Compliance test parameters

CV32_ISA_ALL           = rv32i rv32im rv32imc rv32Zicsr rv32Zifencei

CV32_ISA               = rv32i

RV_COMPLIANCE_DIR      = $(abspath $(CORE_TEST_DIR)/riscv-compliance)
RV_COMPLIANCE_TEST     = $(RV_COMPLIANCE_DIR)/riscv-test-suite/$(CV32_ISA)
RV_COMPLIANCE_SRC      = $(wildcard $(RV_COMPLIANCE_TEST)/src/*.S)
RV_COMPLIANCE_BUILD    = $(abspath $(CORE_TEST_DIR)/build/riscv-compliance/$(CV32_ISA))

RV_COMPLIANCE_ELF     := $(patsubst $(RV_COMPLIANCE_TEST)/src/%.S, $(RV_COMPLIANCE_BUILD)/%.elf, $(RV_COMPLIANCE_SRC))

RV_COMPLIANCE_HEX     := $(RV_COMPLIANCE_ELF:.elf=.hex)
RV_COMPLIANCE_HEX     := $(filter-out $(RV_COMPLIANCE_BUILD)/I-ECALL-01.hex , $(RV_COMPLIANCE_HEX))
RV_COMPLIANCE_HEX     := $(filter-out $(RV_COMPLIANCE_BUILD)/I-EBREAK-01.hex , $(RV_COMPLIANCE_HEX))
RV_COMPLIANCE_HEX     := $(filter-out $(RV_COMPLIANCE_BUILD)/I-MISALIGN_JMP-01.hex , $(RV_COMPLIANCE_HEX))
RV_COMPLIANCE_HEX     := $(filter-out $(RV_COMPLIANCE_BUILD)/I-MISALIGN_LDST-01.hex , $(RV_COMPLIANCE_HEX))

RV_COMPLIANCE_UNIT_TEST = $(wildcard $(RV_COMPLIANCE_TEST)/src/$(TESTNAME).S)
RV_COMPLIANCE_UNIT_HEX  = $(patsubst $(RV_COMPLIANCE_TEST)/src/%.S,$(RV_COMPLIANCE_BUILD)/%.hex,$(RV_COMPLIANCE_UNIT_TEST))

OUTDIRS               += $(sort $(dir $(RV_COMPLIANCE_HEX)))

RV_COMPLIANCE_INCLUDE := riscv-test-env riscv-test-env/p riscv-target/ri5cy
RV_COMPLIANCE_INCLUDE := $(addprefix -I$(RV_COMPLIANCE_DIR)/, $(RV_COMPLIANCE_INCLUDE))

RV_COMPLIANCE_FLAGS    = -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles
ifeq ($(filter $(CV32_ISA),rv32Zicsr rv32Zifencei),)
RV_COMPLIANCE_FLAGS   += -march=$(CV32_ISA) -mabi=ilp32
endif
RV_COMPLIANCE_FLAGS   += $(RV_COMPLIANCE_INCLUDE) -DPRIV_MISA_S=0 -DPRIV_MISA_U=0
RV_COMPLIANCE_FLAGS   += -DTRAPHANDLER="\"$(RV_COMPLIANCE_DIR)/riscv-target/ri5cy/device/rv32imc/handler.S\"" 

RV_COMPLIANCE_LSCRIPT  = $(RV_COMPLIANCE_DIR)/riscv-target/ri5cy/device/rv32imc/link.ld

vpath %.S $(RV_COMPLIANCE_TEST)/src/

###############################################################################
# Build parameters

CC = $(RISCV_EXE_PREFIX)gcc
AS = $(RISCV_EXE_PREFIX)gcc

CFLAGS += -g -Os 
CFLAGS += $(RISCV_TEST_INCLUDES)
CFLAGS += -ffreestanding -nostdlib

LDFLAGS = -lc -lm -lgcc

###############################################################################
# Help me!!!

help:
	@echo "make SIMULATOR={my_simulator} cv32_riscv_compliance_all"
	@echo " -->  run all the RISC-V compliance tests"
	@echo "make SIMULATOR={my_simulator} {test_suite}.cv32_riscv_compliance"
	@echo " -->  run the test suite <test_suite> of the RISC-V compliance tests"
	@echo "make SIMULATOR={my_simulator} cv32_riscv_compliance_unit CV32_ISA={test_suite} TESTNAME={test_name}"
	@echo " -->  run the test <test_name> of the test suite <test_suite> of the RISC-V compliance tests"

###############################################################################
# Implicit rules

# rules to generate hex (loadable by simulators) from elf
%.hex: %.elf
	$(RISCV_EXE_PREFIX)objcopy -O verilog $< $@

###############################################################################
# The sanity rule runs whatever is currently deemed to be the minimal test that
# must be able to run (and pass!) prior to generating a pull-request.
sanity: hello-world
# HELLO WORLD: custom/hello_world.elf: ../../tests/core/custom/hello_world.c

# Running custom programs:
# We link with our custom crt0.s and syscalls.c against newlib so that we can
# use the c standard library
$(CUSTOM_DIR)/%.elf: $(CUSTOM_DIR)/%.c
	$(CC) -o $@ -w -Os -g -nostdlib -T $(CUSTOM)/link.ld -static \
		$^ $(CUSTOM)/crt0.S $(CUSTOM)/syscalls.c $(CUSTOM)/vectors.S \
		$(LDFLAGS)

custom-clean:
	rm -rf $(CUSTOM_DIR)/*.elf $(CUSTOM_DIR)/*.hex

###############################################################################

# compile and dump RISCV_TESTS only
$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf: $(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) \
							$(CV32_RISCV_TESTS_FIRMWARE)/link.ld
	$(CC) $(CFLAGS) -march=rv32imc -o $@ \
		-Wl,-Bstatic,-T,$(CV32_RISCV_TESTS_FIRMWARE)/link.ld,-Map,$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.map,--strip-debug \
		$(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) -lgcc

$(CV32_RISCV_TESTS_FIRMWARE)/start.o: $(CV32_RISCV_TESTS_FIRMWARE)/start.S
	$(AS) -c -march=rv32imc -g -o $@ $<

###############################################################################
# Run compliance tests
# 
# Note: make use of a simulator specific target called '%.${SIMULATOR}-run'
#        that runs a simulation using the firmware passed as implicit argument

cv32_riscv_compliance_all: $(CV32_ISA_ALL:%=%.cv32_riscv_compliance)

%.cv32_riscv_compliance:
	$(MAKE) --no-print-directory cv32_riscv_compliance_test CV32_ISA=$*

cv32_riscv_compliance_test: $(RV_COMPLIANCE_HEX) $(RV_COMPLIANCE_HEX:%=%.run_cv32_compliance_test)

cv32_riscv_compliance_unit: $(RV_COMPLIANCE_UNIT_HEX) $(RV_COMPLIANCE_UNIT_HEX).run_cv32_compliance_test

%.run_cv32_compliance_test: %.${SIMULATOR}-run
	diff --strip-trailing-cr -q dump_sign.txt \
		$(patsubst $(RV_COMPLIANCE_BUILD)/%.hex,$(RV_COMPLIANCE_TEST)/references/%.reference_output,$*)

$(RV_COMPLIANCE_BUILD)/%.elf: %.S | $(OUTDIRS)
	$(CC) $(RV_COMPLIANCE_FLAGS) -T$(RV_COMPLIANCE_LSCRIPT) $< -o $@

###############################################################################
# Implicit rules

%.o: %.c
	$(CC) -c $(CFLAGS) --std=c99 -Wall -o $@ $<

###############################################################################

# compile and dump picorv firmware

# Thales start
$(FIRMWARE)/firmware_unit_test.elf: $(FIRMWARE_OBJS) $(FIRMWARE_UNIT_TEST_OBJS) $(FIRMWARE)/link.ld
	$(CC) $(CFLAGS) -march=rv32imc -o $@ \
		-D RUN_COMPLIANCE \
		-Wl,-Bstatic,-T,$(FIRMWARE)/link.ld,-Map,$(FIRMWARE)/firmware.map,--strip-debug \
		$(FIRMWARE_OBJS) $(FIRMWARE_UNIT_TEST_OBJS) -lgcc
# Thales end

$(FIRMWARE)/firmware.elf: $(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS) $(FIRMWARE)/link.ld
	$(CC) $(CFLAGS) -march=rv32imc -o $@ \
		-D RUN_COMPLIANCE \
		-Wl,-Bstatic,-T,$(FIRMWARE)/link.ld,-Map,$(FIRMWARE)/firmware.map,--strip-debug \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS) -lgcc

#$(FIRMWARE)/start.o: $(FIRMWARE)/start.S
#	$(CC) -c -march=rv32imc -g -D RUN_COMPLIANCE -o $@ $<

# Thales start
$(FIRMWARE)/start.o: $(FIRMWARE)/start.S
ifeq ($(UNIT_TEST_CMD),1)
ifeq ($(FIRMWARE_UNIT_TEST_OBJS),)
$(error no existing unit test in argument )
else
	$(CC) -c -march=rv32imc -g -D RUN_COMPLIANCE  -DUNIT_TEST_CMD=$(UNIT_TEST_CMD) -DUNIT_TEST=$(UNIT_TEST) -DUNIT_TEST_RET=$(UNIT_TEST)_ret -o $@ $<
endif
else
	$(CC) -c -march=rv32imc -g -D RUN_COMPLIANCE  -DUNIT_TEST_CMD=$(UNIT_TEST_CMD) -o $@ $<
endif
# Thales end

$(FIRMWARE)/%.o: $(FIRMWARE)/%.c
	$(CC) -c -march=rv32ic $(CFLAGS) -o $@ $<

$(RISCV_TESTS)/rv32ui/%.o: $(RISCV_TESTS)/rv32ui/%.S $(RISCV_TESTS)/riscv_test.h \
			$(RISCV_TESTS)/macros/scalar/test_macros.h
	$(CC) -c -march=rv32im -g -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

$(RISCV_TESTS)/rv32um/%.o: $(RISCV_TESTS)/rv32um/%.S $(RISCV_TESTS)/riscv_test.h \
			$(RISCV_TESTS)/macros/scalar/test_macros.h
	$(CC) -c -march=rv32im -g -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

$(RISCV_TESTS)/rv32uc/%.o: $(RISCV_TESTS)/rv32uc/%.S $(RISCV_TESTS)/riscv_test.h \
			$(RISCV_TESTS)/macros/scalar/test_macros.h
	$(CC) -c -march=rv32im -g -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

# in dsim
.PHONY: dsim-unit-test 
dsim-unit-test:  firmware-unit-test-clean 
dsim-unit-test:  $(FIRMWARE)/firmware_unit_test.hex 
dsim-unit-test: ALL_VSIM_FLAGS += "+firmware=$(FIRMWARE)/firmware_unit_test.hex"
dsim-unit-test: dsim-firmware-unit-test

# in vcs
.PHONY: firmware-vcs-run
firmware-vcs-run: vcsify $(FIRMWARE)/firmware.hex
	./simv $(SIMV_FLAGS) "+firmware=$(FIRMWARE)/firmware.hex"

.PHONY: firmware-vcs-run-gui
firmware-vcs-run-gui: VCS_FLAGS+=-debug_all
firmware-vcs-run-gui: vcsify $(FIRMWARE)/firmware.hex
	./simv $(SIMV_FLAGS) -gui "+firmware=$(FIRMWARE)/firmware.hex"

###############################################################################
# house-cleaning for unit-testing
.PHONY: firmware-clean
firmware-clean:
	rm -vrf $(addprefix $(FIRMWARE)/firmware., elf bin hex map) \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS)

.PHONY: firmware-unit-test-clean
firmware-unit-test-clean:
	rm -vrf $(addprefix $(FIRMWARE)/firmware_unit_test., elf bin hex map) \
		$(FIRMWARE_OBJS) $(FIRMWARE_UNIT_TEST_OBJS)

#endend

# All generated files plus the clone of the RTL
clean_all: $(SIMULATOR)-clean clean_core_tests clean_riscvdv clean_test_programs
	rm -rf $(CV32E40P_PKG) $(CORE_TEST_DIR)/build

###############################################################################
# Utility rules

$(OUTDIRS):
	@mkdir -p $@
