# Copyright 2022 Silicon Labs, Inc.
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
# not use this file except in compliance with the License, or, at your option,
# the Apache License version 2.0.
#
# You may obtain a copy of the License at
# https://solderpad.org/licenses/SHL-2.1/
#
# Unless required by applicable law or agreed to in writing, any work
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#
# See the License for the specific language governing permissions and
# limitations under the License.


proc cvfv_rerun {} {
  onerror  {exit 1}

  puts  "cvfv: compiling verilog"
  vlog  -mfcu  -f fv.flist

  puts  "cvfv: cutpointing general 'control points'"
  netlist cutpoint {uvmt_cv32e40s_tb.clknrst_if.reset_n} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.debug_if.debug_req} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.interrupt_if.irq} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.core_cntrl_if.boot_addr} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.core_cntrl_if.mtvec_addr} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.core_cntrl_if.dm_halt_addr} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.core_cntrl_if.dm_exception_addr} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.core_cntrl_if.mhartid} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.core_cntrl_if.mimpid_patch} -module uvmt_cv32e40s_tb
  #cutpoints needed to subdue "Design Checks" errors that lead to bonkers CEXes

  puts  "cvfv: cutpointing obi 'control points'"
  netlist cutpoint {uvmt_cv32e40s_tb.obi_instr_if.err} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_instr_if.gntpar} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_instr_if.gnt} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_instr_if.rchk} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_instr_if.rdata} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_instr_if.rvalidpar} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_instr_if.rvalid} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_data_if.err} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_data_if.gntpar} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_data_if.gnt} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_data_if.rchk} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_data_if.rdata} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_data_if.rvalidpar} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.obi_data_if.rvalid} -module uvmt_cv32e40s_tb
  netlist cutpoint {uvmt_cv32e40s_tb.fencei_if.flush_ack} -module uvmt_cv32e40s_tb

  puts  "cvfv: setting constants"
  netlist constant {uvmt_cv32e40s_tb.core_cntrl_if.scan_cg_en} {0} -module uvmt_cv32e40s_tb
  netlist constant {uvmt_cv32e40s_tb.core_cntrl_if.fetch_en} {1} -module uvmt_cv32e40s_tb

  puts  "cvfv: initializing clock/reset"
  netlist clock {uvmt_cv32e40s_tb.clknrst_if.clk} -module uvmt_cv32e40s_tb
  netlist reset {uvmt_cv32e40s_tb.clknrst_if.reset_n} -active_low -module uvmt_cv32e40s_tb
  formal init -inferred

  puts  "cvfv: compiling formal model"
  formal  compile  -d uvmt_cv32e40s_tb  -work work

  puts  "cvfv: see the visualizer log for compilation warnings"
}

cvfv_rerun
