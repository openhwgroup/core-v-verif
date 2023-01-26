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


module uvmt_cv32e40s_xsecure_data_independent_timing_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
   uvmt_cv32e40s_xsecure_if xsecure_if,
   uvma_rvfi_instr_if rvfi_if,
   input rst_ni,
   input clk_i
  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) | !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";
  string info_tag_glitch = "CV32E40S_XSECURE_ASSERT_COVERPOINTS (GLITCH BEHAVIOR)";

  property p_xsecure_setting_default_on(logic xsecure_setting);

    //Make sure that when exiting reset mode the xsecure setting is off
    $rose(rst_ni)
    |->
    xsecure_setting;
  endproperty

    // Local parameters:
  localparam FUNCT7_DIV_REM_INSTRUCTION = 7'b0000001;
  localparam FUNCT3_DIV_REM_INSTRUCTION_MSB = 1'b1;

  localparam FUNCT3_COMPR_BRANCH_2_MSBS = 2'b11;
  localparam OPCODE_COMPR_BRANCH = 2'b01;


    //Descriptive signal names
  logic [2:0] rvfi_insn_funct3;
  logic [2:0] rvfi_insn_cmpr_funct3;
  logic [6:0] rvfi_insn_funct7;
  logic [6:0] rvfi_insn_opcode;
  logic [1:0] rvfi_insn_cmpr_opcode;

  assign rvfi_insn_funct3 = rvfi_if.rvfi_insn[14:12];
  assign rvfi_insn_cmpr_funct3 = rvfi_if.rvfi_insn[15:13];
  assign rvfi_insn_funct7 = rvfi_if.rvfi_insn[31:25];
  assign rvfi_insn_opcode = rvfi_if.rvfi_insn[6:0];
  assign rvfi_insn_cmpr_opcode = rvfi_if.rvfi_insn[1:0];

  ////////// DATA INDEPENDENT TIMING IS CONFIGURABLE //////////

  // Check that we have data independent timing when configured to be on:
  // a_xsecure_dataindtiming_default_off
  // a_xsecure_core_div_rem_timing_clk

  // Check that we do not have data independent timing when configured to be off:

  c_xsecure_branch_timing_off: cover property (

    //Make sure the instruction is a branch instruction (both non-compressed and compressed)
    ((rvfi_insn_opcode == OPCODE_BRANCH)
    || (rvfi_insn_cmpr_opcode == OPCODE_COMPR_BRANCH
    && rvfi_insn_cmpr_funct3[2:1] == FUNCT3_COMPR_BRANCH_2_MSBS))

    //Make sure the instruction is valid and has been executed without traps
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap

    //Make sure the data independent timing was off when executing the branch (ex stage):
    && $past(!xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)

    //Make sure the branch instruction can be directly followed by another instruction (as the branch is not taken)
    ##1 rvfi_if.rvfi_valid
  );


  c_xsecure_core_div_rem_timing: cover property (

    //Make sure we detect an DIV or REM instruction in rvfi
    (rvfi_insn_opcode == OPCODE_OP
    && rvfi_insn_funct3[2] == FUNCT3_DIV_REM_INSTRUCTION_MSB
    && rvfi_insn_funct7 == FUNCT7_DIV_REM_INSTRUCTION)

    //Make sure the instruction is valid and has been executed without traps
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap

    //Make sure data independent timing was off when the DIV/REM instruction was in EX stage
    and $past(!xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)

    //Make sure the branch instruction can be directly followed by another instruction
    && $past(rvfi_if.rvfi_valid)

  );


  ////////// DATA INDEPENDENT TIMING DEFAULT ENABLED //////////

  a_xsecure_dataindtiming_default_on: assert property (
	  p_xsecure_setting_default_on(
	    xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming)
  ) else `uvm_error(info_tag, "Data independent timing is disabled when exiting reset.\n");


  ////////// BRANCH TIMING //////////

  a_xsecure_dataindtiming_branch_timing: assert property (

    //Make sure the instruction is a branch instruction (both non-compressed and compressed)
    ((rvfi_insn_opcode == OPCODE_BRANCH)
    || (rvfi_insn_cmpr_opcode == OPCODE_COMPR_BRANCH
    && rvfi_insn_cmpr_funct3[2:1] == FUNCT3_COMPR_BRANCH_2_MSBS))

    //Make sure the instruction is valid and has been executed without traps
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap

    //Make sure the data independent timing was on when executing the branch (ex stage):
    && $past(xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)

    //Make sure that the instruction before the branch instruction was not a load or a store (rvfi stage):
    //We use past 2 because branching needs two cycles to complete execution due to PC hardening safety.
    && $past(!(|rvfi_if.rvfi_mem_rmask),2)
    && $past(!(|rvfi_if.rvfi_mem_wmask),2)

    |=>
    //Make sure there is at least one instruction stall after every branch because a branch is always taken.
    //We would expect 2 instruction stalls, but since the branch instruction is recalculated in the ID stage there is only one stall, not two.
    !rvfi_if.rvfi_valid
  ) else `uvm_error(info_tag, "Branch timing does not stall the pipeline (given no load/store instruction before the branch instruction).\n");


////////// DIV/REM TIMING //////////

  sequence seq_rvfi_not_valid_for_34_cycles;
    @(posedge clk_i)

    //Make sure rvfi_valid is off for 34 cycles
    !rvfi_if.rvfi_valid[*34] ##1 1;

  endsequence

  sequence seq_set_rvfi_valid_once_as_memory_instruction_during_the_past_34_cycles;
    @(posedge clk_i)

    //Make sure a memory instruction is retired in an interval of 34 cycles

    //Make sure rvfi_valid is low an unknown number of cycles
    !rvfi_if.rvfi_valid[*0:33]

    //Make sure that once the rvfi_valid is high we retire a memory instruction
    ##1 (rvfi_if.rvfi_valid
    && (rvfi_if.rvfi_mem_rmask || rvfi_if.rvfi_mem_wmask))

    //Make sure rvfi_valid is off in an unknown number of cycles
    ##1 !rvfi_if.rvfi_valid[*0:33]

    //Make sure the sequence only looks at previous clock cycles when triggered
    ##1 1;

  endsequence


  a_xsecure_dataindtiming_div_rem_timing: assert property (

    //Make sure the instruction is a DIV or REM instruction
    (rvfi_insn_opcode == OPCODE_OP
    && rvfi_insn_funct3[2] == FUNCT3_DIV_REM_INSTRUCTION_MSB
    && rvfi_insn_funct7 == FUNCT7_DIV_REM_INSTRUCTION)

    //Make sure the instruction is valid and has been executed without traps
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap

    //Make sure data independent timing was on when the DIV/REM instruction was in the EX stage
    //(If data independent timing is on when the instruction is in the WB stage, it was on during the whole execution as well)
    and $past(xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)
    |->
    //Make sure that there are at least 34 cycles from the last retired instruction
    seq_rvfi_not_valid_for_34_cycles.triggered

    //or the retired instructions are loads or stores
    or seq_set_rvfi_valid_once_as_memory_instruction_during_the_past_34_cycles.triggered

  ) else `uvm_error(info_tag, "DIV/REM operations do not use 35 cycles to execute\n");


  endmodule : uvmt_cv32e40s_xsecure_data_independent_timing_assert