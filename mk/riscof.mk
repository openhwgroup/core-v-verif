###############################################################################
#
# Copyright 2023 OpenHW Group
# Copyright 2023 Dolphin Design
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

RISCOF_TEST_PLUSARGS ?= +signature=DUT-cv32e40p.signature
RISCOF_TEST_RUN_DIR ?=$(SIM_CFG_RESULTS)/riscof_dut_work
SIM_RISCOF_ARCH_TESTS_RESULTS ?= $(RISCOF_TEST_RUN_DIR)

RISCOF_CONFIG_FILE    ?= config.ini

###############################################################################
# Generate command to clone RISCOF RISCV-ARCH-TEST SUITE
RISCOF_TEST_SUITE_CLONE_CMD = git clone -b $(RISCOF_ARCH_TEST_SUITE_BRANCH) --single-branch $(RISCOF_ARCH_TEST_SUITE_REPO) --recurse $(RISCOF_ARCH_TEST_SUITE_PKG)

ifeq ($(RISCOF_ARCH_TEST_SUITE_TAG), latest)
  CLONE_RISCOF_ARCH_TEST_SUITE_CMD = riscof --verbose info arch-test --clone --dir $(RISCOF_ARCH_TEST_SUITE_PKG)
else
  CLONE_RISCOF_ARCH_TEST_SUITE_CMD = $(RISCOF_TEST_SUITE_CLONE_CMD); cd $(RISCOF_ARCH_TEST_SUITE_PKG); git checkout $(RISCOF_ARCH_TEST_SUITE_TAG)
endif

###############################################################################
#Clean riscof riscv-arch-test suite
clean_riscof_arch_test_suite:
	rm -rf $(RISCOF_ARCH_TEST_SUITE_PKG)


###############################################################################
#Clone the riscv-arch-test suite in core-v-verif for running the tests
clone_riscof_arch_test_suite: $(RISCOF_ARCH_TEST_SUITE_PKG)

$(RISCOF_ARCH_TEST_SUITE_PKG):
	$(CLONE_RISCOF_ARCH_TEST_SUITE_CMD)

###############################################################################
#RISCOF Validate YAML Command
ifeq ($(call IS_YES,$(RISCOF_SIM)),YES)
RISCOF_VALIDATE_YAML_CMD = riscof validateyaml --config=$(RISCOF_CONFIG_FILE) --work-dir=$(SIM_CFG_RESULTS)/riscof_work
else
RISCOF_VALIDATE_YAML_CMD = echo $(RISCOF_SIM)
endif

.PHONY: riscof_validate_yaml
riscof_validate_yaml: 
	$(shell $(RISCOF_VALIDATE_YAML_CMD))

###############################################################################
#RISCOF Get Testlist Command
ifeq ($(call IS_YES,$(RISCOF_SIM)),YES)
RISCOF_GET_TESTLIST_CMD = riscof testlist --config=$(RISCOF_CONFIG_FILE) --suite=$(RISCOF_ARCH_TEST_SUITE_PKG)/ --env=$(RISCOF_ARCH_TEST_SUITE_PKG)/riscv-test-suite/env --work-dir=$(SIM_CFG_RESULTS)/riscof_work
else
RISCOF_GET_TESTLIST_CMD = echo $(RISCOF_SIM)
endif

.PHONY: riscof_get_testlist
riscof_get_testlist: 
	$(shell $(RISCOF_GET_TESTLIST_CMD))

#################################################################################
##RISCOF Run Command
ifeq ($(call IS_YES,$(RISCOF_SIM)),YES)
RISCOF_RUN_ALL_CMD = riscof run --config=$(RISCOF_CONFIG_FILE) --suite=$(RISCOF_ARCH_TEST_SUITE_PKG)/ --env=$(RISCOF_ARCH_TEST_SUITE_PKG)/riscv-test-suite/env --work-dir=$(SIM_CFG_RESULTS)/riscof_work
else
RISCOF_RUN_ALL_CMD = echo $(RISCOF_SIM)
endif

.PHONY: riscof_run_all
riscof_run_all: 
	$(shell $(RISCOF_RUN_ALL_CMD))
