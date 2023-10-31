// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


// This module contains assertions relating to the "Core Integration" chapter
// of the user manual

module uvmt_cv32e40s_integration_assert
  import uvm_pkg::*;
  import uvma_rvfi_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  import isa_decoder_pkg::*;
(
  input clk_i,
  input rst_ni,

  uvma_rvfi_instr_if_t rvfi_if,

  input fetch_enable_i,

  input [31:0] boot_addr_i,
  input [31:0] dm_exception_addr_i,
  input [31:0] dm_halt_addr_i,
  input [31:0] mtvec_addr_i,

  input alert_major_o,
  input scan_cg_en_i,

  uvmt_cv32e40s_support_logic_module_o_if_t  support_if
);

  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;

  string info_tag = "CV32E40S_INTEGRATION_ASSERT";


  // Helper Logic

  logic fetch_enable_i_sticky;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fetch_enable_i_sticky <= 0;
    end else if (fetch_enable_i) begin
      fetch_enable_i_sticky <= 1;
    end
  end


  // Check that addresses are stable after "fetch_enable_i"

  property p_stable_addr(addr);
    fetch_enable_i_sticky |-> $stable(addr);
  endproperty

  a_stable_bootaddr : assert property (p_stable_addr(boot_addr_i))
    else `uvm_error(info_tag, "boot_addr_i changed after fetch_enable_i");

  a_stable_dmexceptionaddr : assert property (p_stable_addr(dm_exception_addr_i))
    else `uvm_error(info_tag, "dm_exception_addr_i changed after fetch_enable_i");

  a_stable_dmhaltaddr : assert property (p_stable_addr(dm_halt_addr_i))
    else `uvm_error(info_tag, "dm_halt_addr_i changed after fetch_enable_i");

  a_stable_mtvecaddr : assert property (p_stable_addr(mtvec_addr_i))
    else `uvm_error(info_tag, "mtvec_addr_i changed after fetch_enable_i");


  // Check that addresses are word-aligned

  property p_aligned_addr(addr);
    addr[1:0] == 2'b00;
  endproperty

  a_aligned_bootaddr : assert property (p_aligned_addr(boot_addr_i))
    else `uvm_error(info_tag, "boot_addr_i not word-aligned");

  a_aligned_dmexceptionaddr : assert property (p_aligned_addr(dm_exception_addr_i))
    else `uvm_error(info_tag, "dm_exception_addr_i not word-aligned");

  a_aligned_dmhaltaddr : assert property (p_aligned_addr(dm_halt_addr_i))
    else `uvm_error(info_tag, "dm_halt_addr_i not word-aligned");


  // No major alerts in normal operation

  a_no_alert_major: assert property (
    !alert_major_o
    // Note: Do not assume this property
  ) else `uvm_error(info_tag, "major alert should not happen in normal operation");


  // No scan testing in normal operation

  a_no_scan_cg: assert property (
    !scan_cg_en_i
  ) else `uvm_error(info_tag, "scan test should be disabled in normal operation");

  //if m_ext = M_NONE, all mul and div instructions should trap
  if (CORE_PARAM_M_EXT == cv32e40s_pkg::M_NONE) begin: gen_m_none_assert
    a_m_none_mul_trap: assert property(
      rvfi_if.rvfi_valid &&
      rvfi_if.instr_asm.instr inside{CLMUL, CLMULH, CLMULR, MUL, MULH, MULHSU, MULHU, C_MUL}
      |->
      rvfi_if.rvfi_trap.trap
    ) else `uvm_error(info_tag, "Multiply instruction is not illegal when M_EXT = M_NONE");

    a_m_none_div_trap: assert property(
      rvfi_if.rvfi_valid &&
      rvfi_if.instr_asm.instr inside{DIV, DIVU, REM, REMU}
      |->
      rvfi_if.rvfi_trap.trap
    ) else `uvm_error(info_tag, "Divide instruction is not illegal when M_EXT = M_NONE");

  end: gen_m_none_assert


  // Maximum Outstanding OBI Transactions

  a_maximum_outstanding_instr: assert property (
    support_if.instr_bus_v_addr_ph_cnt  inside  {0, 1, 2}
  ) else `uvm_error(info_tag, "More than 2 outstanding OBI transactions");

  a_maximum_outstanding_data: assert property (
    support_if.data_bus_v_addr_ph_cnt  inside  {0, 1, 2}
  ) else `uvm_error(info_tag, "More than 2 outstanding OBI transactions");

  covergroup cg_outstanding @(posedge clk_i);
    option.per_instance = 1;

    cp_instr: coverpoint support_if.instr_bus_v_addr_ph_cnt {
      bins zero = {0};
      bins one  = {1};
      bins two  = {2};
    }

    cp_data: coverpoint support_if.data_bus_v_addr_ph_cnt {
      bins zero = {0};
      bins one  = {1};
      bins two  = {2};
    }

    x_instr_data: cross cp_instr, cp_data;
  endgroup

  cg_outstanding  outstanding_cg = new;


endmodule : uvmt_cv32e40s_integration_assert
