// Copyright 2022 Silicon Labs, Inc.
// Copyright 2022 OpenHW Group
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


`default_nettype  none


module uvmt_cv32e40s_rvfi_assert
  import cv32e40s_pkg::*;
  import cv32e40s_rvfi_pkg::*;
  import uvm_pkg::*;
#(
  parameter logic  SMCLIC,
  parameter int    SMCLIC_ID_WIDTH
)(
  input wire  clk_i,
  input wire  rst_ni,

  input wire             rvfi_valid,
  input wire [ 4:0]      rvfi_rs1_addr,
  input wire [ 4:0]      rvfi_rs2_addr,
  input wire [31:0]      rvfi_rs1_rdata,
  input wire [31:0]      rvfi_rs2_rdata,
  input wire [ 2:0]      rvfi_dbg,
  input wire [31:0]      rvfi_csr_dcsr_rdata,
  input wire rvfi_trap_t rvfi_trap,
  input wire rvfi_intr_t rvfi_intr,
  input wire [31:0]      rvfi_csr_mcause_wdata,
  input wire [31:0]      rvfi_csr_mcause_wmask,
  input wire             rvfi_dbg_mode
);

  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;
  string info_tag = "CV32E40S_RVFI_ASSERT";


  // Helper signals

  logic  was_rvfi_dbg_mode;
  always @(posedge clk_i, negedge rst_ni) begin
    if (rst_ni == 0) begin
      was_rvfi_dbg_mode <= 0;
    end else if (rvfi_valid) begin
      was_rvfi_dbg_mode <= rvfi_dbg_mode;
    end
  end


  // rs1/rs2 reset values

  property p_rs_resetvalue (addr, rdata);
    $past(rst_ni == 0)  ##0
    (rvfi_valid [->1])  ##0
    addr
    |->
    (rdata == 0);  // TODO:ropeders use "RF_REG_RV"
  endproperty : p_rs_resetvalue

  a_rs1_resetvalue: assert property (
    p_rs_resetvalue(rvfi_rs1_addr, rvfi_rs1_rdata)
  ) else `uvm_error(info_tag, "unexpected 'rs1' reset value");

  a_rs2_resetvalue: assert property (
    p_rs_resetvalue(rvfi_rs2_addr, rvfi_rs2_rdata)
  ) else `uvm_error(info_tag, "unexpected 'rs2' reset value");


  // RVFI debug cause matches dcsr debug cause

  a_dbg_cause_general: assert property (
    rvfi_valid  &&
    rvfi_dbg    &&
    !was_rvfi_dbg_mode
    |->
    (rvfi_dbg == rvfi_csr_dcsr_rdata[8:6])
  ) else `uvm_error(info_tag, "'rvfi_dbg' did not match 'dcsr.cause'");

  property  p_dbg_cause_n (n);
    rvfi_valid          &&
    rvfi_dbg            &&
    !was_rvfi_dbg_mode  &&
    (rvfi_csr_dcsr_rdata[8:6] == n)
    |->
    (rvfi_dbg == n);
  endproperty : p_dbg_cause_n

  a_dbg_cause_ebreak: assert property (
    p_dbg_cause_n(1)
  ) else `uvm_error(info_tag, "'rvfi_dbg' did not match 'dcsr.cause'");

  a_dbg_cause_trigger: assert property (
    p_dbg_cause_n(2)
  ) else `uvm_error(info_tag, "'rvfi_dbg' did not match 'dcsr.cause'");

  a_dbg_cause_haltreq: assert property (
    p_dbg_cause_n(3)
  ) else `uvm_error(info_tag, "'rvfi_dbg' did not match 'dcsr.cause'");

  a_dbg_cause_step: assert property (
    p_dbg_cause_n(4)
  ) else `uvm_error(info_tag, "'rvfi_dbg' did not match 'dcsr.cause'");


  // RVFI exception cause matches "mcause"

  wire logic [10:0]  rvfi_mcause_exccode;
  assign rvfi_mcause_exccode = (rvfi_csr_mcause_wdata & rvfi_csr_mcause_wmask);

  a_exc_cause: assert property (
    rvfi_valid           &&
    rvfi_trap.exception  &&
    !rvfi_dbg_mode
    |->
    (rvfi_trap.exception_cause == rvfi_mcause_exccode)
  ) else `uvm_error(info_tag, "'exception_cause' must match 'mcause'");


  // RVFI interrupt cause matches legal causes

  if (!SMCLIC) begin: gen_legal_cause_clint
    a_irq_cause_clint: assert property (
      rvfi_valid  &&
      rvfi_intr.interrupt
      |->
      (rvfi_intr.cause inside {3, 7, 11, [16:31], [1024:1027]})
    ) else `uvm_error(info_tag, "unexpected interrupt cause");
  end : gen_legal_cause_clint

  if (SMCLIC) begin: gen_legal_cause_clic
    localparam logic [31:0]  MAX_CLIC_ID = 2^SMCLIC_ID_WIDTH - 1;

    a_irq_cause_clic: assert property (
      rvfi_valid  &&
      rvfi_intr.interrupt
      |->
      (rvfi_intr.cause inside {[0:MAX_CLIC_ID], [1024:1027]})
    ) else `uvm_error(info_tag, "unexpected interrupt cause");
  end : gen_legal_cause_clic


  // Exceptions/Interrupts/Debugs have a cause

  a_exceptions_cause: assert property (
    rvfi_valid  &&
    rvfi_trap.exception
    |->
    rvfi_trap.exception_cause
  ) else `uvm_error(info_tag, "rvfi_trap exceptions must have a cause");

  if (!SMCLIC) begin: gen_clint_cause
    a_interrupts_cause: assert property (
      rvfi_valid  &&
      rvfi_intr
      |->
      rvfi_intr.cause
    ) else `uvm_error(info_tag, "rvfi_intr interrupts must have a cause");
  end : gen_clint_cause

  a_debugs_cause: assert property (
    rvfi_valid  &&
    rvfi_trap.debug
    |->
    rvfi_trap.debug_cause
  ) else `uvm_error(info_tag, "rvfi_trap debugs must have a cause");


endmodule : uvmt_cv32e40s_rvfi_assert


`default_nettype  wire
