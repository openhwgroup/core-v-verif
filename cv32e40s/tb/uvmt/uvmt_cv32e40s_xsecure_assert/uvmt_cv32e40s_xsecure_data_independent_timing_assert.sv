// Copyright 2022 OpenHW Group
// Copyright 2022 Silicon Labs, Inc.
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

//TODO: bruk konfig med divisjon enablet
module uvmt_cv32e40s_xsecure_data_independent_timing_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
   uvma_rvfi_instr_if rvfi_if,
   uvma_rvfi_csr_if rvfi_cpuctrl,
   input rst_ni,
   input clk_i,

   input logic dataindtiming_enabled
  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) | !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";

  // Local parameters:
  localparam FUNCT7_DIV_REM = 7'b0000001;
  localparam FUNCT3_DIV_REM_MSB = 1'b1;

  localparam FUNCT3_BRANCH_CMPR_2_MSBS = 2'b11;
  localparam OPCODE_BRANCH_CMPR = 2'b01;

  localparam DATAINDTIMING = 0;
  localparam PC_HARDENING = 3;


  //Verify that data independent timing is off then exiting reset mode:

  a_xsecure_dataindtiming_default_on: assert property (
	  $rose(rst_ni)
    |->
	  dataindtiming_enabled
  ) else `uvm_error(info_tag, "Data independent timing is disabled when exiting reset.\n");


  //Verify that execution of branches has non-varying timing when the data independent timing feature is enabled

  logic branch_instr;
  assign branch_instr = rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap
    && ((rvfi_if.rvfi_insn[6:0] == OPCODE_BRANCH)
    || (rvfi_if.rvfi_insn[1:0] == OPCODE_BRANCH_CMPR
    && rvfi_if.rvfi_insn[15:14] == FUNCT3_BRANCH_CMPR_2_MSBS));


  logic div_rem_instr;
  assign div_rem_instr = rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap

    && rvfi_if.rvfi_insn[6:0] == OPCODE_OP
    && rvfi_if.rvfi_insn[14] == FUNCT3_DIV_REM_MSB
    && rvfi_if.rvfi_insn[31:25] == FUNCT7_DIV_REM;


  sequence seq_no_memory_operation_for_x_cycles(x);
    (!(((|rvfi_if.rvfi_mem_rmask) || (|rvfi_if.rvfi_mem_wmask)) && rvfi_if.rvfi_valid))[*x];
  endsequence

  a_xsecure_dataindtiming_branch_timing_pc_hardening_enabled: assert property (

    rvfi_cpuctrl.rvfi_csr_rdata[PC_HARDENING]
    && rvfi_cpuctrl.rvfi_csr_rdata[DATAINDTIMING]
    && branch_instr
    ##0 seq_no_memory_operation_for_x_cycles(3).triggered //TODO: why 3? comment or change to non-magic

    |=>
    //Make sure there is at least one instruction stall after every branch because a branch is always taken.
    //We expect 2 instruction stalls, but since the branch instruction is recalculated in the ID stage there is only one stall.
    !rvfi_if.rvfi_valid
  ) else `uvm_error(info_tag, "Branch instruction is not taken even though independent data timing is enabled (PC hardening enabled).\n");


  a_xsecure_dataindtiming_branch_timing_pc_hardening_disabled: assert property (

    !rvfi_cpuctrl.rvfi_csr_rdata[PC_HARDENING]
    && rvfi_cpuctrl.rvfi_csr_rdata[DATAINDTIMING]
    && branch_instr
    ##0 seq_no_memory_operation_for_x_cycles(3).triggered //TODO: samme som over

    |=>
    //Make sure there is at least one instruction stall after every branch because a branch is always taken.
    //We expect 2 instruction stalls, but since the branch instruction is recalculated in the ID stage there is only one stall.
    !rvfi_if.rvfi_valid[*2]
  ) else `uvm_error(info_tag, "Branch instruction is not taken even though independent data timing is enabled (PC hardening enabled).\n");


  //Verify that execution of division or (division)-remainder have non-varying timing when the data independent timing feature is enabled

  sequence seq_rvfi_not_valid_for_34_cycles;
    //@(posedge clk_i)

    //Make sure there is no memory operations retiring during the execution of the DIV/REM operation
    //(!(rvfi_if.rvfi_valid && (rvfi_if.rvfi_mem_rmask || rvfi_if.rvfi_mem_wmask))) throughout

    //Make sure rvfi_valid is off for 35 cycles (34 unretired cycles + 1 retired cycle)
    (!rvfi_if.rvfi_valid[*34] ##1 rvfi_if.rvfi_valid);

  endsequence


  sequence seq_no_memory_operation_during_35_cycles;
    //Make sure no memory operation retires for 35 cycles
    (!(rvfi_if.rvfi_valid && (rvfi_if.rvfi_mem_rmask || rvfi_if.rvfi_mem_wmask)))[*34] ##1 rvfi_if.rvfi_valid;
  endsequence


  a_xsecure_dataindtiming_div_rem_timing: assert property (

    rvfi_cpuctrl.rvfi_csr_rdata[DATAINDTIMING]

    && div_rem_instr

    && seq_no_memory_operation_during_35_cycles.triggered //TODO: comment

    |->
    //Verify that the RVFI valid signal has been low during 34 cycles due to the data independent timing duration of the DIV/REM instruction
    seq_rvfi_not_valid_for_34_cycles.triggered

  ) else `uvm_error(info_tag, "DIV/REM operations do not use 35 cycles to execute when data independent timing is enabled\n");


  //Verify that there is varying timing og branch, division or (division) remainder operations when the data independent timing feature is disabled

  c_xsecure_dataindtiming_branch_timing_off: cover property (

    !rvfi_cpuctrl.rvfi_csr_rdata[DATAINDTIMING]

    && branch_instr

    //Make sure the branch instruction can be directly followed by another instruction (as the branch is not taken)
    ##1 rvfi_if.rvfi_valid
  );


  c_xsecure_dataindtiming_core_div_rem_timing_off: cover property (

    !rvfi_cpuctrl.rvfi_csr_rdata[DATAINDTIMING]

    && div_rem_instr

    //Make sure the DIV or REM can be calculated in one cycle only (indicating that data independent timing is off)
    && $past(rvfi_if.rvfi_valid)
  );

  endmodule : uvmt_cv32e40s_xsecure_data_independent_timing_assert

