###############################################################################
#
# Copyright 2020 AMIQ EDA s.r.l. 
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
# Bring up the project inside the AMIQ DVT Eclipse IDE (https://dvteclipse.com/)
#
# Usage: make SIMULATOR=<simulator> open_in_dvt_ide
###############################################################################

DVT_COMMAND=$(DVT_HOME)/bin/dvt_cli.sh createProject $(CORE_V_VERIF) -force -lang vlog -build default $(DVT_CLI_ARGS)
DVT_BUILD_FILE_CONTENT_HEADER="+dvt_enable_elaboration +dvt_enable_elaboration_incremental+FULL"

ifeq ($(SIMULATOR), xrun)
	DVT_BUILD_FILE_CONTENT=$(DVT_BUILD_FILE_CONTENT_HEADER)" +dvt_init+xcelium.xrun $(XRUN_COMP) -top $(RTLSRC_VLOG_TB_TOP)"
else
ifeq ($(SIMULATOR), vcs)
	DVT_BUILD_FILE_CONTENT=$(DVT_BUILD_FILE_CONTENT_HEADER)" +dvt_init+vcs.vlogan $(VCS_COMP) -top $(RTLSRC_VLOG_TB_TOP)"
else
ifeq ($(SIMULATOR), vsim)
	DVT_BUILD_FILE_CONTENT=$(DVT_BUILD_FILE_CONTENT_HEADER)" +dvt_init+questa.vlog -work $(VWORK) $(VLOG_FLAGS)	+incdir+$(DV_UVME_PATH) +incdir+$(DV_UVMT_PATH) +incdir+$(UVM_HOME) $(UVM_HOME)/uvm_pkg.sv -f $(CV_CORE_MANIFEST) $(VLOG_FILE_LIST) $(TBSRC_PKG) -top $(RTLSRC_VLOG_TB_TOP)"
else
	DVT_BUILD_FILE_CONTENT=$(DVT_BUILD_FILE_CONTENT_HEADER)" +dvt_init+dvt -uvm	+define+CV32E40P_ASSERT_ON +define+ISS+CV32E40P_TRACE_EXECUTION +incdir+$(DV_UVME_PATH) +incdir+$(DV_UVMT_PATH) -f $(CV_CORE_MANIFEST) -f $(DV_UVMT_PATH)/uvmt_$(CV_CORE_LC).flist -f $(DV_UVMT_PATH)/imperas_iss.flist -top $(RTLSRC_VLOG_TB_TOP)"
endif
endif
endif

.PHONY: open_in_dvt_ide check_dvt_home create_dvt_build_dir create_dvt_build_file

create_dvt_build_dir:
	@ mkdir -p $(CORE_V_VERIF)/.dvt

create_dvt_build_file: create_dvt_build_dir $(CV_CORE_PKG)
	@ echo $(DVT_BUILD_FILE_CONTENT) > $(CORE_V_VERIF)/.dvt/default.build

open_in_dvt_ide: check_dvt_home create_dvt_build_file
	$(DVT_COMMAND)

check_dvt_home:
ifndef DVT_HOME
	@echo "DVT_HOME env var is not set!"; \
	exit 1; \
endif
endif
