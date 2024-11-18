// ----------------------------------------------------------------------------
// Copyright 2023 CEA*
// *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//[END OF HEADER]

+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/memory_partition
+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/reset_gen
+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/watchdog
+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/clock_gen
+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/unix_utils
+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/pulse_gen
+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/bp_gen
+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/generic_agent
+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/memory_rsp_model
+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/memory_rsp_model/axi2mem
+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/memory_shadow
+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/clock_mon
+incdir+$CORE_V_VERIF/lib/cv_dv_utils/uvm/perf_mon

${CORE_V_VERIF}/lib/cv_dv_utils/uvm/memory_partition/memory_partitions_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/reset_gen/reset_vif_xrtl_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/reset_gen/xrtl_reset_vif.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/reset_gen/reset_driver_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/watchdog/watchdog_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/clock_gen/xrtl_clock_vif.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/clock_gen/clock_vif_xrtl_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/clock_gen/clock_driver_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/unix_utils/unix_utils_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/pulse_gen/pulse_if.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/pulse_gen/pulse_gen_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/bp_gen/bp_vif_xrtl_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/bp_gen/bp_driver_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/bp_gen/bp_vif.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/generic_agent/generic_agent_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/generic_agent/generic_if.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/memory_rsp_model/memory_response_model_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/memory_rsp_model/memory_response_if.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/memory_rsp_model/axi2mem/axi2mem_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/memory_rsp_model/axi2mem/axi_intf.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/memory_shadow/memory_shadow_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/clock_mon/xrtl_clock_mon_vif.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/clock_mon/clock_mon_vif_xrtl_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/clock_mon/clock_monitor_pkg.sv
${CORE_V_VERIF}/lib/cv_dv_utils/uvm/perf_mon/perf_mon_pkg.sv
