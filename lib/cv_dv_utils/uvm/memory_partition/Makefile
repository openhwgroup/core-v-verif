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
# Target Library and Top Entity
########################################################
LIB_NAME := cv_uvm_dv_utils_lib
TOP_ENTITY_NAME := 

WORK_LIB = cv_uvm_dv_utils_lib
WORK_DIR = $(PROJECT_LIBS_DIR)/$(WORK_LIB)

ifneq (,${UVM_LOCAL_LIB})
########################################################
# List libraries for simulation
########################################################
LIB_LIST := -L uvm_local_lib

########################################################
# List of Units (all required sub-units before compiling this Makefile)
########################################################
LIST_UNITS = \
$(UVM_LOCAL_LIB)/uvm_local

endif # ifneq(,${UVM_LOCAL_LIB},)

AM_VSIM_OPTIONS += $(LIB_LIST)
AM_VOPT_OPTIONS += $(LIB_LIST)
AM_SVLOG_OPTIONS += $(LIB_LIST)

########################################################
# List Source FIles
########################################################
VERILOG_VPATH += $(CV_DV_UTILS_DIR)/uvm/memory_partition

SVLOG_SOURCES := \
memory_partitions_pkg.sv

########################################################
# Include Template
########################################################
include $(PROJECT_DIR)/config/Makefile.def

