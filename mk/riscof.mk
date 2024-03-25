###############################################################################
#
# Copyright 2023 OpenHW Group
# Copyright 2023 Dolphin Design
# Copyright 2024 Silicon Labs
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
# This Makefile adds RISCOF RISCV-ARCH-TEST SUITE, related make variables
# to support running of riscof's riscv-arch-test suite within the core-v-verif
# testbench
#
###############################################################################

RISCOF_ARCH_TEST_SUITE_PKG   := $(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/riscof/riscof_arch_test_suite
RISCOF_SIM ?= NO
RISCOF_TEST_PLUSARGS ?= +signature=DUT-$(CV_CORE).signature
RISCOF_TEST_RUN_DIR ?=$(SIM_CFG_RESULTS)/riscof_dut_work
RISCOF_WORK_DIR ?= $(SIM_CFG_RESULTS)/riscof_work
SIM_RISCOF_ARCH_TESTS_RESULTS ?= $(RISCOF_TEST_RUN_DIR)
RISCOF_CONFIG_FILE ?= config.ini
RISCOF_VERBOSE ?= info
RISCOF_TEST_SUITE_CLONE_CMD = git clone -b $(RISCOF_ARCH_TEST_SUITE_BRANCH) --single-branch $(RISCOF_ARCH_TEST_SUITE_REPO) --recurse $(RISCOF_ARCH_TEST_SUITE_PKG)
RISCOF_RUN_ALL_CMD = riscof --verbose $(RISCOF_VERBOSE) run --config=$(RISCOF_CONFIG_FILE) --suite=$(RISCOF_ARCH_TEST_SUITE_PKG)/ --env=$(RISCOF_ARCH_TEST_SUITE_PKG)/riscv-test-suite/env --work-dir=$(RISCOF_WORK_DIR)
RISCOF_CWD ?= $(MAKE_PATH)

ifeq ($(call IS_NO,$(RISCOF_REF_RUN)),NO)
  RISCOF_RUN_ALL_CMD += --no-ref-run
endif
ifeq ($(call IS_NO,$(RISCOF_DUT_RUN)),NO)
  RISCOF_RUN_ALL_CMD += --no-dut-run
endif

ifeq ($(RISCOF_ARCH_TEST_SUITE_TAG), latest)
  CLONE_RISCOF_ARCH_TEST_SUITE_CMD = riscof --verbose $(RISCOF_VERBOSE) arch-test --clone --dir $(RISCOF_ARCH_TEST_SUITE_PKG)
else
  CLONE_RISCOF_ARCH_TEST_SUITE_CMD = $(RISCOF_TEST_SUITE_CLONE_CMD); cd $(RISCOF_ARCH_TEST_SUITE_PKG); git checkout $(RISCOF_ARCH_TEST_SUITE_TAG)
endif

.PHONY: mk_work_dir clean_riscof_arch_test_suite riscof_validate_yaml riscof_get_testlist riscof_run_all

mk_work_dir:
	$(MKDIR_P) $(RISCOF_WORK_DIR)

clean_riscof_arch_test_suite:
	rm -rf $(RISCOF_ARCH_TEST_SUITE_PKG)

clone_riscof_arch_test_suite: $(RISCOF_ARCH_TEST_SUITE_PKG)

$(RISCOF_ARCH_TEST_SUITE_PKG):
	$(CLONE_RISCOF_ARCH_TEST_SUITE_CMD)

riscof_validate_yaml: mk_work_dir
	cd $(RISCOF_CWD) && riscof validateyaml --config=$(RISCOF_CONFIG_FILE) --work-dir=$(RISCOF_WORK_DIR)

riscof_get_testlist: mk_work_dir
	cd $(RISCOF_CWD) && riscof testlist --config=$(RISCOF_CONFIG_FILE) --suite=$(RISCOF_ARCH_TEST_SUITE_PKG)/ --env=$(RISCOF_ARCH_TEST_SUITE_PKG)/riscv-test-suite/env --work-dir=$(RISCOF_WORK_DIR)

riscof_run_all: mk_work_dir
	cd $(RISCOF_CWD) && $(RISCOF_RUN_ALL_CMD)
