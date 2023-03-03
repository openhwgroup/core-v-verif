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


  ////////// DATA INDEPENDENT TIMING IS CONFIGURABLE //////////

  c_xsecure_branch_timing_off: cover property (

    //Make sure the instruction is a branch instruction (both non-compressed and compressed)
    ((xsecure_if.rvfi_opcode == OPCODE_BRANCH)
    || (xsecure_if.rvfi_cmpr_opcode == OPCODE_COMPR_BRANCH
    && xsecure_if.rvfi_cmpr_funct3[2:1] == FUNCT3_COMPR_BRANCH_2_MSBS))

    //Make sure the instruction is valid and has been executed without traps
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap

    //Make sure the data independent timing was off when executing the branch (ex stage):
    && $past(!xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)

    //Make sure the branch instruction can be directly followed by another instruction (as the branch is not taken)
    ##1 rvfi_if.rvfi_valid
  );


  c_xsecure_core_div_rem_timing_off: cover property (

    //Make sure we detect an DIV or REM instruction in rvfi
    (xsecure_if.rvfi_opcode == OPCODE_OP
    && xsecure_if.rvfi_funct3[2] == FUNCT3_DIV_REM_INSTRUCTION_MSB
    && xsecure_if.rvfi_funct7 == FUNCT7_DIV_REM_INSTRUCTION)

    //Make sure the instruction is valid and has been executed without traps
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap

    //Make sure data independent timing was off when the DIV/REM instruction was in EX stage
    && $past(!xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)

    //Make sure the DIV or REM can be calculated in one cycle only (indicating that data independent timing is off)
    && $past(rvfi_if.rvfi_valid)
  );



  ////////// DATA INDEPENDENT TIMING DEFAULT ENABLED //////////

  a_xsecure_dataindtiming_default_on: assert property (
	  p_xsecure_setting_default_on(
	    xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming)
  ) else `uvm_error(info_tag, "Data independent timing is disabled when exiting reset.\n");


  ////////// BRANCH TIMING //////////

  sequence seq_dataindtiming_branch_timing_antecedent(is_pchardening);

    //Check whether the pc hardening setting is on or not
    is_pchardening

    //Make sure the instruction is a branch instruction (both non-compressed and compressed)
    && ((xsecure_if.rvfi_opcode == OPCODE_BRANCH)
    || (xsecure_if.rvfi_cmpr_opcode == OPCODE_COMPR_BRANCH
    && xsecure_if.rvfi_cmpr_funct3[2:1] == FUNCT3_COMPR_BRANCH_2_MSBS))

    //Make sure the instruction is valid and has been executed without traps
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap

    //Make sure the data independent timing was on/off when executing the branch:
    //(If data independent timing is on when the instruction is in the WB stage, it was on during the whole execution as well)
    && $past(xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming);

  endsequence


  sequence seq_no_memory_operation_for_x_cycles(x);
    //Make sure the x following instructions are not a valid memory instruction
    (!(((|rvfi_if.rvfi_mem_rmask) || (|rvfi_if.rvfi_mem_wmask)) && rvfi_if.rvfi_valid))[*x];
  endsequence

  a_xsecure_dataindtiming_branch_timing_pc_hardening_enabled: assert property (

    //Make sure a branch instruction has retired, that the previouse instruction was not a memory operation, and that PC hardening is enabled
    seq_dataindtiming_branch_timing_antecedent(
      xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening)

    ##0 seq_no_memory_operation_for_x_cycles(3).triggered

    |=>
    //Make sure there is at least one instruction stall after every branch because a branch is always taken.
    //We expect 2 instruction stalls, but since the branch instruction is recalculated in the ID stage there is only one stall.
    !rvfi_if.rvfi_valid
  ) else `uvm_error(info_tag, "Branch instruction is not taken even though independent data timing is enabled (PC hardening enabled).\n");


  a_xsecure_dataindtiming_branch_timing_pc_hardening_disabled: assert property (

    (xsecure_if.core_i_controller_i_controller_fsm_i_ctrl_fsm_cs == FUNCTIONAL)
    throughout

    (xsecure_if.if_id_pipe_opcode == OPCODE_BRANCH
    ##[2:$]
    //Make sure a branch instruction has retired, that the previouse instruction was not a memory operation, and that PC hardening is disabled
    seq_dataindtiming_branch_timing_antecedent(
      !xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening)

    ##0 seq_no_memory_operation_for_x_cycles(2).triggered)

    |=>
    //Make sure there is at least one instruction stall after every branch because a branch is always taken.
    //We expect 2 instruction stalls, because the branch instruction kills the IF and ID stages
    !rvfi_if.rvfi_valid[*2]
  ) else `uvm_error(info_tag, "Branch instruction is not taken even though independent data timing is enabled (PC hardening disabled).\n");


  ////////// DIV/REM TIMING //////////

  sequence seq_rvfi_not_valid_for_34_cycles;
    @(posedge clk_i)

    //Make sure there is no memory operations retiring during the execution of the DIV/REM operation, and that data independent timing is enabled during the whole operation
    (!(rvfi_if.rvfi_valid && (rvfi_if.rvfi_mem_rmask || rvfi_if.rvfi_mem_wmask)) && xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming) throughout

    //Make sure rvfi_valid is off for 35 cycles (34 unretired cycles + 1 retired cycle)
    (!rvfi_if.rvfi_valid[*34] ##1 rvfi_if.rvfi_valid);

  endsequence


  sequence seq_data_independent_timing_enabled_for_35_cycles;
    //Make sure the data independent timing feature is enabled for 35 cycles
    xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming[*35];
  endsequence


  sequence seq_no_memory_operation_during_35_cycles;
    //Make sure no memory operation retires for 35 cycles
    (!(rvfi_if.rvfi_valid && (rvfi_if.rvfi_mem_rmask || rvfi_if.rvfi_mem_wmask)))[*35];
  endsequence


  a_xsecure_dataindtiming_div_rem_timing: assert property (
    //Make sure the instruction is a DIV or REM instruction
    (xsecure_if.rvfi_opcode == OPCODE_OP
    && xsecure_if.rvfi_funct3[2] == FUNCT3_DIV_REM_INSTRUCTION_MSB
    && xsecure_if.rvfi_funct7 == FUNCT7_DIV_REM_INSTRUCTION)

    //Make sure the instruction is valid and has been executed without traps
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap

    //Make sure data independent timing was on when the DIV/REM instruction was in the EX stage
    //(If data independent timing is on when the instruction is in the WB stage, it was on during the whole execution as well)
    && $past(xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming)

    |->
    //Verify that the RVFI valid signal has been low during 34 cycles due to the data independent timing duration of the DIV/REM instruction
    seq_rvfi_not_valid_for_34_cycles.triggered

    //Or that the data independent timing has not been enabled during the execution of the DIV/REM instruction
    or not seq_data_independent_timing_enabled_for_35_cycles.triggered

    //Or that a memory operation has retired during the execution of the DIV/REM instruction
    or not seq_no_memory_operation_during_35_cycles.triggered

  ) else `uvm_error(info_tag, "DIV/REM operations do not use 35 cycles to execute when data independent timing is enabled\n");


  endmodule : uvmt_cv32e40s_xsecure_data_independent_timing_assert