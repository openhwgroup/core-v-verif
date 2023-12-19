// Copyright 2023 Silicon Labs, Inc.
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


//Information:
//The division and remainder operation not enabled in all run configurations.
//Make sure to run a configuration that support the division and reminder instructions

module uvmt_cv32e40s_xsecure_data_independent_timing_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
   uvma_rvfi_instr_if_t rvfi_if,
   uvma_rvfi_csr_if_t rvfi_cpuctrl,
   input rst_ni,
   input clk_i,

   input logic dataindtiming_enabled
  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) || !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";

  // Local parameters:
  localparam FUNCT7_DIV_REM = 7'b0000001;
  localparam FUNCT3_DIV_REM_MSB = 1'b1;

  localparam FUNCT3_BRANCH_CMPR_2_MSBS = 2'b11;
  localparam OPCODE_BRANCH_CMPR = 2'b01;

  localparam DATAINDTIMING = 0;
  localparam PC_HARDENING = 3;


  //Verify that data independent timing is enabled when exiting reset mode:

  a_xsecure_dataindtiming_default_on: assert property (
    $rose(rst_ni)
    |->
    dataindtiming_enabled
  ) else `uvm_error(info_tag, "Data independent timing is disabled when exiting reset.\n");


  //Verify that execution of branches has non-varying timing when the data independent timing feature is enabled

  //Information:
  //All branch instructions in the EX stage flush the IF and ID stage.
  //It will therefore be two empty cycles after a branch instruction.
  //However, there are 2 exceptions:
  //1) A memory instruction prior to a branch instruction:
    //The memory instruction can stall the WB stage and then also the branch instruction in the EX stage,
    //The incoming instruction can propegate to IF or ID stage therby reducing the number of empty cycles after a branch instruction.
  //2) PC hardening enabled:
    //The PC hardening feature make a branch instruction into a multicycled instruction.
    //When a branch instruction reach the EX stage, the instruction is recalculated in the ID instead of flushing the ID stage.
    //Consequently, it is only the IF stage that is flushed, and the branch instruction is considered retired when the
    //second branch instruction is retired.
    //There is therefor only 1 empty cycle after a branch instruction.

  sequence seq_no_mem_instr_for_cycles(x);
    @(posedge clk_i) (!rvfi_if.is_mem_act)[*x];
  endsequence

  a_xsecure_dataindtiming_branch_timing_pc_hardening_disabled: assert property (

    !rvfi_cpuctrl.rvfi_csr_rdata[PC_HARDENING]
    && rvfi_cpuctrl.rvfi_csr_rdata[DATAINDTIMING]
    && rvfi_if.is_branch

    //The current cycle is not a memory operation (but a branch operation),
    //and the prior cycle is not a memory operation
    ##0 seq_no_mem_instr_for_cycles(2).triggered

    |=>
    (!rvfi_if.rvfi_valid)[*2]
  ) else `uvm_error(info_tag, "Branch instruction is not taken even though independent data timing is enabled (PC hardening enabled).\n");


  a_xsecure_dataindtiming_branch_timing_pc_hardening_enabled: assert property (

    rvfi_cpuctrl.rvfi_csr_rdata[PC_HARDENING]
    && rvfi_cpuctrl.rvfi_csr_rdata[DATAINDTIMING]
    && rvfi_if.is_branch

    //The current cycle is not a memory operation (but the first part of a branch operation),
    //the cycle prior to that is not a memory operation (but the second part of a branch operation),
    //the cycle prior to that is not a memory cycle as well
    ##0 seq_no_mem_instr_for_cycles(3).triggered

    |->
    !$past(rvfi_if.rvfi_valid) //Verifies that the first branch instruction is not considered a retired instruction
    ##1 !rvfi_if.rvfi_valid
  ) else `uvm_error(info_tag, "Branch instruction is not taken even though independent data timing is enabled (PC hardening enabled).\n");


  //Verify that execution of division or (division)-remainder have non-varying timing when the data independent timing feature is enabled

  sequence seq_no_rvalid_for_past_34_cycles;
    @(posedge clk_i) (!rvfi_if.rvfi_valid[*34] ##1 1);
  endsequence

  a_xsecure_dataindtiming_div_rem_timing: assert property (

    rvfi_cpuctrl.rvfi_csr_rdata[DATAINDTIMING]
    && (rvfi_if.is_div || rvfi_if.is_rem)
    && !rvfi_if.rvfi_trap.trap
    ##0 seq_no_mem_instr_for_cycles(35).triggered

    |->
    seq_no_rvalid_for_past_34_cycles.triggered

  ) else `uvm_error(info_tag, "DIV/REM operations do not use 35 cycles to execute when data independent timing is enabled\n");


  //Verify that there is varying timing of branch, division or (division) remainder operations when the data independent timing feature is disabled

  c_xsecure_dataindtiming_branch_timing_off: cover property (

    !rvfi_cpuctrl.rvfi_csr_rdata[DATAINDTIMING]

    && rvfi_if.is_branch

    //Make sure the branch instruction can be directly followed by another instruction (as the branch is not taken)
    ##1 rvfi_if.rvfi_valid
  );


  c_xsecure_dataindtiming_core_div_rem_timing_off: cover property (

    !rvfi_cpuctrl.rvfi_csr_rdata[DATAINDTIMING]

    && rvfi_if.is_div || rvfi_if.is_rem

    //Make sure the DIV or REM can be calculated in one cycle only (indicating that data independent timing is off)
    && $past(rvfi_if.rvfi_valid)
  );

  endmodule : uvmt_cv32e40s_xsecure_data_independent_timing_assert

