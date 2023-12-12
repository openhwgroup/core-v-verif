# Copyright 2022 Silicon Labs, Inc.
# Copyright 2022 OpenHW Group
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
# not use this file except in compliance with the License, or, at your option,
# the Apache License version 2.0.
#
# You may obtain a copy of the License at
#
# https://solderpad.org/licenses/SHL-2.1/
#
# Unless required by applicable law or agreed to in writing, any work
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#
# See the License for the specific language governing permissions and
# limitations under the License.


default_target:
	@echo error: specify a make target


export CV_CORE_PKG  ?= $(CORE_V_VERIF)/core-v-cores/$(CV_CORE)

export DV_ISA_DECODER_PATH  ?= $(CORE_V_VERIF)/lib/isa_decoder
export DV_SUPPORT_PATH      ?= $(CORE_V_VERIF)/lib/support
export DV_UVM_TESTCASE_PATH ?= $(CORE_V_VERIF)/$(CV_CORE)/tests/uvmt
export DV_UVMA_PATH         ?= $(CORE_V_VERIF)/lib/uvm_agents
export DV_UVME_PATH         ?= $(CORE_V_VERIF)/$(CV_CORE)/env/uvme
export DV_UVMT_PATH         ?= $(CORE_V_VERIF)/$(CV_CORE)/tb/uvmt

export DESIGN_RTL_DIR ?= $(CV_CORE_PKG)/rtl


include $(CORE_V_VERIF)/mk/Common.mk


$(CV_CORE_PKG):
	$(CLONE_CV_CORE_CMD)
