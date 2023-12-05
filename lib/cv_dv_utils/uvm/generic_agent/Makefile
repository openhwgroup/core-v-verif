# ----------------------------------------------------------------------------
# Copyright 2023 CEA*
# *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
#
# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#[END OF HEADER]
# ----------------------------------------------------------------------------
# ----------------------------------------------------------------------------

########################################################
# select default UNIMAKE target
########################################################
ifeq (${UNIMAKE_TARGET},)
  UNIMAKE_TARGET=QUESTA_SIMULATION
  export UNIMAKE_TARGET
  $(info compiling for ${UNIMAKE_TARGET})
endif

ifeq (${UNIMAKE_TARGET},QUESTA_SIMULATION)
  QUESTA_MODE=VOPT
  export QUESTA_MODE
endif

########################################################
# HDL compilation
########################################################
MAKEFILE_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

REQ_ACK_AGENT_DIR  = $(CV_DV_UTILS_DIR)/uvm/generic_agent

SVLOG_SOURCES    += generic_if.sv \
                    generic_agent_pkg.sv

LIB_NAME := cv_uvm_dv_utils_lib
TOP_ENTITY_NAME := 

WORK_LIB = cv_uvm_dv_utils_lib

## Libraries options
LIST_LIBS += -L cv_uvm_dv_utils_lib

AM_VLOG_OPTIONS += $(LIST_LIBS)
AM_SVLOG_OPTIONS += $(LIST_LIBS)
AM_VOPT_OPTIONS += $(LIST_LIBS)
AM_VSIM_OPTIONS += $(LIST_LIBS)
                  
WORK_DIR = $(PROJECT_LIBS_DIR)/$(WORK_LIB)

##################################################################
# Makefile inclusion (after definition of all previous variables)
##################################################################

include $(PROJECT_DIR)/config/Makefile.def
