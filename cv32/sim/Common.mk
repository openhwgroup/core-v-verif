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
# Common code for simulation Makefiles.  Intended to be included by the
# Makefiles in the "core" and "uvmt_cv32" dirs.
#
###############################################################################
# 
# Copyright 2019 Claire Wolf
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
# Common functions

# Map multiple flag values to "YES" or NO
# Use like this, to test variable MYVAR
# ifeq ($(call IS_YES($(MYVAR)),YES)
YES_VALS=Y YES 1 y yes TRUE true
IS_YES=$(if $(filter $(YES_VALS),$(1)),YES,NO)
NO_VALS=N NO 0 n no FALSE false
IS_NO=$(if $(filter $(NO_VALS),$(1)),NO,YES)

###############################################################################
# Common variables
BANNER=*******************************************************************************************

###############################################################################
# Variables to determine the the command to clone external repositories.
# For each repo there are a set of variables:
#      *_REPO:   URL to the repository in GitHub.
#      *_BRANCH: Name of the branch you wish to clone;
#                Set to 'master' to pull the master branch.
#      *_HASH:   Value of the specific hash you wish to clone;
#                Set to 'head' to pull the head of the branch you want.
# THe CV32E40P repo also has a variable to clone a specific tag:
#      *_TAG:    Value of the specific tag you wish to clone;
#                Will override the HASH unless set to "none".
#                

export SHELL = /bin/bash

CV32E40P_REPO   ?= https://github.com/openhwgroup/cv32e40p
CV32E40P_BRANCH ?= master
CV32E40P_HASH   ?= 120ac3e
CV32E40P_TAG    ?= cv32e40p_v1.0.0
#CV32E40P_TAG    ?= none

RISCVDV_REPO    ?= https://github.com/google/riscv-dv
RISCVDV_BRANCH  ?= master
RISCVDV_HASH    ?= 10fd4fa8b7d0808732ecf656c213866cae37045a

COMPLIANCE_REPO   ?= https://github.com/riscv/riscv-compliance
COMPLIANCE_BRANCH ?= master
# 2020-08-19
COMPLIANCE_HASH   ?= c21a2e86afa3f7d4292a2dd26b759f3f29cde497

# Generate command to clone the CV32E40P RTL.

ifeq ($(CV32E40P_BRANCH), master)
  TMP = git clone $(CV32E40P_REPO) $(CV32E40P_PKG)
else
  TMP = git clone -b $(CV32E40P_BRANCH) --single-branch $(CV32E40P_REPO) $(CV32E40P_PKG)
endif

# If a TAG is specified, the HASH is not considered
ifeq ($(CV32E40P_TAG), none)
  ifeq ($(CV32E40P_HASH), head)
    CLONE_CV32E40P_CMD = $(TMP)
  else
    CLONE_CV32E40P_CMD = $(TMP); cd $(CV32E40P_PKG); git checkout $(CV32E40P_HASH)
  endif
else
  CLONE_CV32E40P_CMD = $(TMP); cd $(CV32E40P_PKG); git checkout tags/$(CV32E40P_TAG)
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

# Generate command to clone the RISCV Compliance Test-suite
ifeq ($(COMPLIANCE_BRANCH), master)
  TMP4 = git clone $(COMPLIANCE_REPO) --recurse $(COMPLIANCE_PKG)
else
  TMP4 = git clone -b $(COMPLIANCE_BRANCH) --single-branch $(COMPLIANCE_REPO) --recurse $(COMPLIANCE_PKG)
endif

ifeq ($(COMPLIANCE_HASH), head)
  CLONE_COMPLIANCE_CMD = $(TMP4)
else
  CLONE_COMPLIANCE_CMD = $(TMP4); cd $(COMPLIANCE_PKG); git checkout $(COMPLIANCE_HASH)
endif
# RISCV Compliance repo var end

###############################################################################
# Imperas Instruction Set Simulator

DV_OVPM_HOME    = $(PROJ_ROOT_DIR)/vendor_lib/imperas
DV_OVPM_MODEL   = $(DV_OVPM_HOME)/riscv_CV32E40P_OVPsim
DV_OVPM_DESIGN  = $(DV_OVPM_HOME)/design
OVP_MODEL_DPI   = $(DV_OVPM_MODEL)/bin/Linux64/riscv_CV32E40P.dpi.so
#OVP_CTRL_FILE   = $(DV_OVPM_DESIGN)/riscv_CV32E40P.ic

###############################################################################
# "Toolchain" to compile 'test-programs' (either C or RISC-V Assember) for the
# CV32E40P.   This toolchain is used by both the core testbench and UVM
# environment.  The assumption here is that you have installed at least one of
# the following toolchains:
#     1. GNU:   https://github.com/riscv/riscv-gnu-toolchain
#               Assumed to be installed at /opt/gnu.
#
#     2. COREV: https://www.embecosm.com/resources/tool-chain-downloads/#corev 
#               Assumed to be installed at /opt/corev.
#
#     3. PULP:  https://github.com/pulp-platform/pulp-riscv-gnu-toolchain 
#               Assumed to be installed at /opt/pulp.
#
# If you do not select one of the above options, compilation will be attempted
# using whatever is found at /opt/riscv using arch=unknown.
#
GNU_SW_TOOLCHAIN    ?= /opt/gnu
GNU_MARCH           ?= unknown
COREV_SW_TOOLCHAIN  ?= /opt/corev
COREV_MARCH         ?= corev
PULP_SW_TOOLCHAIN   ?= /opt/pulp
PULP_MARCH          ?= unknown

CV_SW_TOOLCHAIN  ?= /opt/riscv
CV_SW_MARCH      ?= unknown
RISCV            ?= $(CV_SW_TOOLCHAIN)
RISCV_PREFIX     ?= riscv32-$(CV_SW_MARCH)-elf-
RISCV_EXE_PREFIX ?= $(RISCV)/bin/$(RISCV_PREFIX)

ifeq ($(call IS_YES,$(GNU)),YES)
RISCV            = $(GNU_SW_TOOLCHAIN)
RISCV_PREFIX     = riscv32-$(GNU_MARCH)-elf-
RISCV_EXE_PREFIX = $(RISCV)/bin/$(RISCV_PREFIX)
endif

ifeq ($(call IS_YES,$(COREV)),YES)
RISCV            = $(COREV_SW_TOOLCHAIN)
RISCV_PREFIX     = riscv32-$(COREV_MARCH)-elf-
RISCV_EXE_PREFIX = $(RISCV)/bin/$(RISCV_PREFIX)
endif

ifeq ($(call IS_YES,$(PULP)),YES)
RISCV            = $(PULP_SW_TOOLCHAIN)
RISCV_PREFIX     = riscv32-$(PULP_MARCH)-elf-
RISCV_EXE_PREFIX = $(RISCV)/bin/$(RISCV_PREFIX)
endif

CFLAGS ?= -Os -g -static -mabi=ilp32 -march=rv32imc -Wall -pedantic

# FIXME:strichmo:Repeating this code until we fully deprecate CUSTOM_PROG, hopefully next PR
ifeq ($(firstword $(subst _, ,$(CUSTOM_PROG))),pulp)
  CFLAGS = -Os -g -D__riscv__=1 -D__LITTLE_ENDIAN__=1 -march=rv32imcxpulpv2 -Wa,-march=rv32imcxpulpv2 -fdata-sections -ffunction-sections -fdiagnostics-color=always
endif

ifeq ($(firstword $(subst _, ,$(TEST))),pulp)
  CFLAGS = -Os -g -D__riscv__=1 -D__LITTLE_ENDIAN__=1 -march=rv32imcxpulpv2 -Wa,-march=rv32imcxpulpv2 -fdata-sections -ffunction-sections -fdiagnostics-color=always
endif

ASM       ?= ../../tests/asm
ASM_DIR   ?= $(ASM)

# CORE FIRMWARE vars. All of the C and assembler programs under CORE_TEST_DIR
# are collectively known as "Core Firmware".  Yes, this is confusing because
# one of sub-directories of CORE_TEST_DIR is called "firmware".
#
# Note that the DSIM targets allow for writing the log-files to arbitrary
# locations, so all of these paths are absolute, except those used by Verilator.
# TODO: clean this mess up!
CORE_TEST_DIR                        = $(PROJ_ROOT_DIR)/cv32/tests/programs
BSP                                  = $(PROJ_ROOT_DIR)/cv32/bsp
FIRMWARE                             = $(CORE_TEST_DIR)/firmware
VERI_FIRMWARE                        = ../../tests/core/firmware
CUSTOM                               = $(CORE_TEST_DIR)/custom
CUSTOM_DIR                          ?= $(CUSTOM)
CUSTOM_PROG                         ?= my_hello_world
VERI_CUSTOM                          = ../../tests/programs/custom
ASM_PROG                            ?= my_hello_world
CV32_RISCV_TESTS_FIRMWARE            = $(CORE_TEST_DIR)/cv32_riscv_tests_firmware
CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE = $(CORE_TEST_DIR)/cv32_riscv_compliance_tests_firmware
RISCV_TESTS                          = $(CORE_TEST_DIR)/riscv_tests
RISCV_COMPLIANCE_TESTS               = $(CORE_TEST_DIR)/riscv_compliance_tests
RISCV_TEST_INCLUDES                  = -I$(CORE_TEST_DIR)/riscv_tests/ \
                                       -I$(CORE_TEST_DIR)/riscv_tests/macros/scalar \
                                       -I$(CORE_TEST_DIR)/riscv_tests/rv64ui \
                                       -I$(CORE_TEST_DIR)/riscv_tests/rv64um
CV32_RISCV_TESTS_FIRMWARE_OBJS       = $(addprefix $(CV32_RISCV_TESTS_FIRMWARE)/, \
                                         start.o print.o sieve.o multest.o stats.o)
CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE_OBJS = $(addprefix $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/, \
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
COMPLIANCE_TEST_OBJS     = $(addsuffix .o, \
                             $(basename $(wildcard $(RISCV_COMPLIANCE_TESTS)/*.S)))


# Thales verilator testbench compilation start

SUPPORTED_COMMANDS := vsim-firmware-unit-test questa-unit-test questa-unit-test-gui dsim-unit-test vcs-unit-test
SUPPORTS_MAKE_ARGS := $(filter $(firstword $(MAKECMDGOALS)), $(SUPPORTED_COMMANDS))

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
# The sanity rule runs whatever is currently deemed to be the minimal test that
# must be able to run (and pass!) prior to generating a pull-request.
sanity: hello-world

###############################################################################
# Read YAML test specifications

# If the gen_corev-dv target is defined then read in a test specification file
YAML2MAKE = $(PROJ_ROOT_DIR)/bin/yaml2make
ifneq ($(filter gen_corev-dv,$(MAKECMDGOALS)),)
ifeq ($(TEST),)
$(error ERROR must specify a TEST variable with gen_corev-dv target)
endif
GEN_FLAGS_MAKE := $(shell $(YAML2MAKE) --test=$(TEST) --yaml=corev-dv.yaml --debug --prefix=GEN)
ifeq ($(GEN_FLAGS_MAKE),)
$(error ERROR Could not find corev-dv.yaml for test: $(TEST))
endif
include $(GEN_FLAGS_MAKE)
endif

# If the test target is defined then read in a test specification file
TEST_YAML_PARSE_TARGETS=test waves cov
ifneq ($(filter $(TEST_YAML_PARSE_TARGETS),$(MAKECMDGOALS)),)
ifeq ($(TEST),)
$(error ERROR must specify a TEST variable)
endif
TEST_FLAGS_MAKE := $(shell $(YAML2MAKE) --test=$(TEST) --yaml=test.yaml --debug --run-index=$(RUN_INDEX) --prefix=TEST)
ifeq ($(TEST_FLAGS_MAKE),)
$(error ERROR Could not find test.yaml for test: $(TEST))
endif
include $(TEST_FLAGS_MAKE)
endif

# If a test target is defined and a CFG is defined that read in build configuration file
# CFG is optional
CFGYAML2MAKE = $(PROJ_ROOT_DIR)/bin/cfgyaml2make
CFG_YAML_PARSE_TARGETS=comp test
ifneq ($(filter $(CFG_YAML_PARSE_TARGETS),$(MAKECMDGOALS)),)
ifneq ($(CFG),)
CFG_FLAGS_MAKE := $(shell $(CFGYAML2MAKE) --yaml=$(CFG).yaml --debug --prefix=CFG)
ifeq ($(CFG_FLAGS_MAKE),)
$(error ERROR Error finding or parsing configuration: $(CFG).yaml)
endif
include $(CFG_FLAGS_MAKE)
endif
endif

###############################################################################
# Rule to generate hex (loadable by simulators) from elf
# Relocate debugger to last 16KB of mm_ram
#    $@ is the file being generated.
#    $< is first prerequiste.
#    $^ is all prerequistes.
#    $* is file_name (w/o extension) of target
%.hex: %.elf
	@echo "$(BANNER)"
	@echo "* Generating hexfile, readelf and objdump files"
	@echo "$(BANNER)"
	$(RISCV_EXE_PREFIX)objcopy -O verilog \
		$< \
		$@ \
		--change-section-address  .debugger=0x3FC000 \
		--change-section-address  .debugger_exception=0x3FC800
	@echo ""
	$(RISCV_EXE_PREFIX)readelf -a $< > $*.readelf
	@echo ""
	$(RISCV_EXE_PREFIX)objdump -D -S $*.elf > $*.objdump

bsp:
	@echo "$(BANNER)"
	@echo "* Compiling BSP"
	@echo "$(BANNER)"
	make -C $(BSP) RISCV=$(RISCV) RISCV_PREFIX=$(RISCV_PREFIX) RISCV_EXE_PREFIX=$(RISCV_EXE_PREFIX)

vars-bsp:
	make vars -C $(BSP) RISCV=$(RISCV) RISCV_PREFIX=$(RISCV_PREFIX) RISCV_EXE_PREFIX=$(RISCV_EXE_PREFIX)

clean-bsp:
	make clean -C $(BSP)

##############################################################################
# Special debug_test build
# keep raw elf files to generate helpful debugging files such as dissambler
.PRECIOUS : %debug_test.elf
.PRECIOUS : %debug_test_reset.elf
.PRECIOUS : %debug_test_trigger.elf
.PRECIOUS : %debug_test_known_miscompares.elf
	
# Prepare file list for .elf
# Get the source file names from the BSP directory
PREREQ_BSP_FILES  = $(filter %.c %.S %.ld,$(wildcard $(BSP)/*))
BSP_SOURCE_FILES  = $(notdir $(filter %.c %.S ,$(PREREQ_BSP_FILES)))

# Let the user override BSP files
# The following will build a list of BSP files that are not in test directory
BSP_FILES = $(foreach BSP_FILE, $(BSP_SOURCE_FILES), \
	       $(if $(wildcard  $(addprefix $(dir $*), $(BSP_FILE))),,\
	          $(wildcard $(addprefix $(BSP)/, $(BSP_FILE))) ) \
	     )

# Get Test Files
#  Note, the prerequisite uses '%', while the recipe uses '$*'
PREREQ_TEST_FILES = $(filter %.c %.S,$(wildcard $(dir %)*))
TEST_FILES        = $(filter %.c %.S,$(wildcard $(dir $*)*))

%debug_test.elf:
	$(RISCV_EXE_PREFIX)gcc -mabi=ilp32 -march=rv32imc -o $@ \
		-Wall -pedantic -Os -g -nostartfiles -static \
		$(BSP_FILES) \
		$(TEST_FILES) \
		-T $(BSP)/link.ld
%debug_test_reset.elf:
	$(RISCV_EXE_PREFIX)gcc -mabi=ilp32 -march=rv32imc -o $@ \
		-Wall -pedantic -Os -g -nostartfiles -static \
		$(BSP_FILES) \
		$(TEST_FILES) \
		-T $(BSP)/link.ld
%debug_test_trigger.elf:
	$(RISCV_EXE_PREFIX)gcc -mabi=ilp32 -march=rv32imc -o $@ \
		-Wall -pedantic -Os -g -nostartfiles -static \
		$(BSP_FILES) \
		$(TEST_FILES) \
		-T $(BSP)/link.ld
%debug_test_known_miscompares.elf:
	$(RISCV_EXE_PREFIX)gcc -mabi=ilp32 -march=rv32imc -o $@ \
		-Wall -pedantic -Os -g -nostartfiles -static \
		$(BSP_FILES) \
		$(TEST_FILES) \
		-T $(BSP)/link.ld

# Patterned targets to generate ELF.  Used only if explicit targets do not match.
#
.PRECIOUS : %.elf
# This target selected if both %.c and %.S exist
# Note that this target will pass both sources to gcc
%.elf: %.c %.S
	make bsp
	@echo "$(BANNER)"
	@echo "* Compiling test-program $^"
	@echo "$(BANNER)"
	$(RISCV_EXE_PREFIX)gcc $(CFG_CFLAGS) \
		$(TEST_CFLAGS) \
		$(CFLAGS) \
		-o $@ \
		-nostartfiles \
		$^ \
		-T $(BSP)/link.ld \
		-L $(BSP) \
		-lcv-verif

# This target selected if only %.c
%.elf: %.c
	make bsp
	@echo "$(BANNER)"
	@echo "* Compiling test-program $^"
	@echo "$(BANNER)"
	$(RISCV_EXE_PREFIX)gcc $(CFG_CFLAGS) \
		$(TEST_CFLAGS) \
		$(CFLAGS) \
		-o $@ \
		-nostartfiles \
		$^ \
		-T $(BSP)/link.ld \
		-L $(BSP) \
		-lcv-verif

# This target selected if only %.S exists
%.elf: %.S
	make bsp
	$(RISCV_EXE_PREFIX)gcc $(CFG_CFLAGS) $(TEST_CFLAGS) $(CFLAGS) -v -o $@ \
		-nostartfiles \
		-I $(ASM) \
		$^ -T $(BSP)/link.ld -L $(BSP) -lcv-verif

# compile and dump RISCV_TESTS only
#$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf: $(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) \
#							$(CV32_RISCV_TESTS_FIRMWARE)/link.ld
#	$(RISCV_EXE_PREFIX)gcc -g -Os -mabi=ilp32 -march=rv32imc -ffreestanding -nostdlib -o $@ \
#		$(RISCV_TEST_INCLUDES) \
#		-Wl,-Bstatic,-T,$(CV32_RISCV_TESTS_FIRMWARE)/link.ld,-Map,$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.map,--strip-debug \
#		$(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) -lgcc

#$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf: $(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) \
#							$(CV32_RISCV_TESTS_FIRMWARE)/link.ld
../../tests/core/cv32_riscv_tests_firmware/cv32_riscv_tests_firmware.elf: $(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS)
	$(RISCV_EXE_PREFIX)gcc $(CFLAGS) -ffreestanding -nostdlib -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-Wl,-Bstatic,-T,$(CV32_RISCV_TESTS_FIRMWARE)/link.ld,-Map,$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.map,--strip-debug \
		$(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) -lgcc

$(CV32_RISCV_TESTS_FIRMWARE)/start.o: $(CV32_RISCV_TESTS_FIRMWARE)/start.S
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -o $@ $<

$(CV32_RISCV_TESTS_FIRMWARE)/%.o: $(CV32_RISCV_TESTS_FIRMWARE)/%.c
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) --std=c99 -Wall \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

# compile and dump RISCV_COMPLIANCE_TESTS only
$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.elf: $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE_OBJS) $(COMPLIANCE_TEST_OBJS) \
							$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/link.ld
	$(RISCV_EXE_PREFIX)gcc $(CFLAGS) -ffreestanding -nostdlib -o $@ \
		-D RUN_COMPLIANCE \
		$(RISCV_TEST_INCLUDES) \
		-Wl,-Bstatic,-T,$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/link.ld,-Map,$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.map,--strip-debug \
		$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE_OBJS) $(COMPLIANCE_TEST_OBJS) -lgcc

$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/start.o: $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/start.S
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -D RUN_COMPLIANCE -o $@ $<

$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/%.o: $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/%.c
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) --std=c99 -Wall \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

# compile and dump picorv firmware

# Thales start
$(FIRMWARE)/firmware_unit_test.elf: $(FIRMWARE_OBJS) $(FIRMWARE_UNIT_TEST_OBJS) $(FIRMWARE)/link.ld
	$(RISCV_EXE_PREFIX)gcc $(CFLAGS) -ffreestanding -nostdlib -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-D RUN_COMPLIANCE \
		-Wl,-Bstatic,-T,$(FIRMWARE)/link.ld,-Map,$(FIRMWARE)/firmware.map,--strip-debug \
		$(FIRMWARE_OBJS) $(FIRMWARE_UNIT_TEST_OBJS) -lgcc
# Thales end

$(FIRMWARE)/firmware.elf: $(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS) $(FIRMWARE)/link.ld
	$(RISCV_EXE_PREFIX)gcc $(CFLAGS) -ffreestanding -nostdlib -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-D RUN_COMPLIANCE \
		-Wl,-Bstatic,-T,$(FIRMWARE)/link.ld,-Map,$(FIRMWARE)/firmware.map,--strip-debug \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS) -lgcc

#$(FIRMWARE)/start.o: $(FIRMWARE)/start.S
#	$(RISCV_EXE_PREFIX)gcc -c -march=rv32imc -g -D RUN_COMPLIANCE -o $@ $<

# Thales start
$(FIRMWARE)/start.o: $(FIRMWARE)/start.S
ifeq ($(UNIT_TEST_CMD),1)
ifeq ($(FIRMWARE_UNIT_TEST_OBJS),)
$(error no existing unit test in argument )
else
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -D RUN_COMPLIANCE  -DUNIT_TEST_CMD=$(UNIT_TEST_CMD) -DUNIT_TEST=$(UNIT_TEST) -DUNIT_TEST_RET=$(UNIT_TEST)_ret -o $@ $<
endif
else
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -D RUN_COMPLIANCE  -DUNIT_TEST_CMD=$(UNIT_TEST_CMD) -o $@ $<
endif
# Thales end

$(FIRMWARE)/%.o: $(FIRMWARE)/%.c
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) --std=c99 \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

$(RISCV_TESTS)/rv32ui/%.o: $(RISCV_TESTS)/rv32ui/%.S $(RISCV_TESTS)/riscv_test.h \
			$(RISCV_TESTS)/macros/scalar/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

$(RISCV_TESTS)/rv32um/%.o: $(RISCV_TESTS)/rv32um/%.S $(RISCV_TESTS)/riscv_test.h \
			$(RISCV_TESTS)/macros/scalar/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

$(RISCV_TESTS)/rv32uc/%.o: $(RISCV_TESTS)/rv32uc/%.S $(RISCV_TESTS)/riscv_test.h \
			$(RISCV_TESTS)/macros/scalar/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

# Build riscv_compliance_test. Make sure to escape dashes to underscores
$(RISCV_COMPLIANCE_TESTS)/%.o: $(RISCV_COMPLIANCE_TESTS)/%.S $(RISCV_COMPLIANCE_TESTS)/riscv_test.h \
			$(RISCV_COMPLIANCE_TESTS)/test_macros.h $(RISCV_COMPLIANCE_TESTS)/compliance_io.h \
			$(RISCV_COMPLIANCE_TESTS)/compliance_test.h
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -o $@ \
		-DTEST_FUNC_NAME=$(notdir $(subst -,_,$(basename $<))) \
		-DTEST_FUNC_TXT='"$(notdir $(subst -,_,$(basename $<)))"' \
		-DTEST_FUNC_RET=$(notdir $(subst -,_,$(basename $<)))_ret $<

# in dsim
.PHONY: dsim-unit-test 
dsim-unit-test:  firmware-unit-test-clean 
dsim-unit-test:  $(FIRMWARE)/firmware_unit_test.hex 
dsim-unit-test: ALL_VSIM_FLAGS += "+firmware=$(FIRMWARE)/firmware_unit_test.hex +elf_file=$(FIRMWARE)/firmware_unit_test.elf"
dsim-unit-test: dsim-firmware-unit-test

# in vcs
.PHONY: firmware-vcs-run
firmware-vcs-run: vcsify $(FIRMWARE)/firmware.hex
	./simv $(SIMV_FLAGS) "+firmware=$(FIRMWARE)/firmware.hex"

.PHONY: firmware-vcs-run-gui
firmware-vcs-run-gui: VCS_FLAGS+=-debug_all
firmware-vcs-run-gui: vcsify $(FIRMWARE)/firmware.hex
	./simv $(SIMV_FLAGS) -gui "+firmware=$(FIRMWARE)/firmware.hex"

.PHONY: vcs-unit-test
vcs-unit-test:  firmware-unit-test-clean
vcs-unit-test:  $(FIRMWARE)/firmware_unit_test.hex 
vcs-unit-test:  vcsify $(FIRMWARE)/firmware_unit_test.hex
vcs-unit-test:  vcs-run

###############################################################################
# house-cleaning for unit-testing
custom-clean:
	rm -rf $(CUSTOM)/hello_world.elf $(CUSTOM)/hello_world.hex


.PHONY: firmware-clean
firmware-clean:
	rm -vrf $(addprefix $(FIRMWARE)/firmware., elf bin hex map) \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS)

.PHONY: firmware-unit-test-clean
firmware-unit-test-clean:
	rm -vrf $(addprefix $(FIRMWARE)/firmware_unit_test., elf bin hex map) \
		$(FIRMWARE_OBJS) $(FIRMWARE_UNIT_TEST_OBJS)

#endend
