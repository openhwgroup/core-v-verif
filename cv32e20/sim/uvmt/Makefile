###############################################################################
#
# Copyright 2020,2022 OpenHW Group
# 
# Licensed under the Solderpad Hardware Licence, Version 2.1 (the "License");
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
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
###############################################################################
#
# Makefile for the CV32E20 UVM testbench.
#
###############################################################################

# "Constants"
MAKE                  = make
MAKE_PATH            := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
export CORE_V_VERIF   = $(abspath $(MAKE_PATH)/../../..)
export CV_CORE       ?= cv32e20

DPI_DASM_SPIKE_REPO  ?= https://github.com/riscv/riscv-isa-sim.git
CV_SW_TOOLCHAIN      ?= /opt/riscv
CV_SW_PREFIX         ?= " "

include ../ExternalRepos.mk
include $(CORE_V_VERIF)/mk/uvmt/uvmt.mk
