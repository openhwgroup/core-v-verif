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


module uvmt_cv32e40s_xsecure_hardened_pc_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
    //Signals:
    input clk_i,
    input rst_ni,

    //CSRs:
    input logic pc_hardening_enabled,
    input logic dataindtiming_enabled,

    //Alert:
    input logic alert_major_due_to_pc_err,

    //IF:
    input logic if_valid,
    input logic ptr_in_if,
    input logic if_instr_cmpr,
    input logic [31:0] if_pc,
    input logic dummy_insert,

    //ID:
    input logic id_ready,
    input logic [31:0] id_pc,
    input logic id_last_op,
    input logic id_first_op,
    input logic jump_in_id,
    input logic kill_id,
    input logic halt_id,

    //EX:
    input logic ex_first_op,
    input logic branch_in_ex,
    input logic kill_ex,
    input logic halt_ex,

    //Controll signals:
    input logic pc_set,
    input logic [3:0] pc_mux,

    //Signals to glitch check:
    input logic [31:0] branch_target,
    input logic branch_decision,
    input logic [31:0] jump_target,
    input logic [31:0] mepc

  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) || !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";
  string info_tag_glitch = "CV32E40S_XSECURE_ASSERT_COVERPOINTS (GLITCH BEHAVIOR)";


  // Local parameters:
  localparam JUMP = 4'b0100;
  localparam MRET = 4'b0001;

  localparam INSTRUCTION_INCREMENT = 4;
  localparam INSTR_INCREMENT_CMPR = 2;


  //Verify that pc hardening is enabled by default

  a_xsecure_pc_hardening_default_on: assert property (
    $rose(rst_ni)
    |->
    pc_hardening_enabled
  ) else `uvm_error(info_tag, "PC hardening is not enabled when exiting reset.\n");


  //Verify that the PC increment correctly when there is no PC jumping

  //Make sure the PC of ID and IF stage is equal when there is a dummy instruction in the ID stage
  sequence seq_equal_if_id_pc_if_dummy_instr;
    @(posedge clk_i)

    dummy_insert

    ##1 (if_pc == id_pc)[*1:$];
  endsequence

  sequence seq_pc_initialization;
    @(posedge clk_i)

    $rose(rst_ni)

    ##0 (!if_pc && !id_pc)[*1:$];
  endsequence


  //Make sure the PC, which is set due to a PC jump, is stable in the IF stage until it is forwarded to the id stage
  sequence seq_pc_set_stable;
    @(posedge clk_i)

    pc_set

    //(Uses ##2 because: in the first cycle the PC is set, and in the second cycle the PC is stable
    ##2 $stable(if_pc)[*1:$];
  endsequence


  a_xsecure_pc_hardening: assert property (

    pc_hardening_enabled
    && $past(if_valid)
    && $past(id_ready)

    && !$past(ptr_in_if) // pointers insert a non-incremental PC

    |->

    if_pc == id_pc + INSTR_INCREMENT_CMPR && $past(if_instr_cmpr)
    or if_pc == id_pc + INSTRUCTION_INCREMENT && $past(!if_instr_cmpr)

    or seq_pc_initialization.triggered
    or if_pc == if_pc && !id_last_op
    or seq_equal_if_id_pc_if_dummy_instr.triggered
    or $past(pc_set)
    or seq_pc_set_stable.triggered

  ) else `uvm_error(info_tag, "There is a PC fault in the IF stage.\n");


  //Verify that the major alert is set due to pc hardening fault when the PC is incremented wrongly, when there is no PC jumping and the PC hardening feature is enabled

  sequence seq_unexpected_behavior;
    @(posedge clk_i)

    $past(if_valid)
    && $past(id_ready)

    && !$past(ptr_in_if) // pointers insert a non-incremental PC

    and !(if_pc == id_pc + INSTR_INCREMENT_CMPR && $past(if_instr_cmpr))
    and !(if_pc == id_pc + INSTRUCTION_INCREMENT && $past(!if_instr_cmpr))

    and !(seq_pc_initialization.triggered)
    and !(if_pc == if_pc && !id_last_op)
    and !(seq_equal_if_id_pc_if_dummy_instr.triggered)
    and !(seq_pc_set_stable.triggered)
    and !($past(pc_set));

  endsequence


  a_glitch_xsecure_pc_hardening_sequential_instruction_hardening_enabled: assert property (

    pc_hardening_enabled

    ##0 seq_unexpected_behavior

    |->
    alert_major_due_to_pc_err

  ) else `uvm_error(info_tag_glitch, "A PC fault in the IF stage does not set the major alert when PC hardening is on.\n");


  //Verify that the major alert is not set due to pc hardening fault when the PC is incremented wrongly, when there is no PC jumping and the PC hardening feature is disabled

  a_glitch_xsecure_pc_hardening_sequential_instruction_hardening_disabled: assert property (

    !pc_hardening_enabled

    ##0 seq_unexpected_behavior

    |->
    !alert_major_due_to_pc_err

  ) else `uvm_error(info_tag_glitch, "A PC fault in the IF stage does set the major alert when PC hardening is off.\n");


  //Verify that the major alert is set due to pc hardening fault when the PC target of a jump instruction or a branch decision is unstable, and the PC hardening feature is enabled

  sequence seq_non_hardened_jump(kill, halt, instr, first_op, jump_addr);
    @(posedge clk_i)

    (!kill && !halt) throughout

    ((instr && $rose(first_op))
    || ($rose(instr) && first_op))

    && pc_set
    ##1 instr
    && jump_addr != $past(jump_addr);
  endsequence


  a_glitch_xsecure_pc_hardening_branch_hardening_enabled: assert property(

    pc_hardening_enabled

    ##0 seq_non_hardened_jump(
      kill_ex,
      halt_ex,
      branch_in_ex,
      ex_first_op,
      branch_target)
    |->
    alert_major_due_to_pc_err
  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed branch instruction does not set the major alert.\n");


  a_glitch_xsecure_pc_hardening_jump_hardening_enabled: assert property(

    pc_hardening_enabled
    && pc_mux == JUMP

    ##0 seq_non_hardened_jump(
      kill_id,
      halt_id,
      jump_in_id,
      id_first_op,
      jump_target)
    |->
    alert_major_due_to_pc_err
  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed jump instruction does not set the major alert.\n");


  a_glitch_xsecure_pc_hardening_mret_hardening_enabled: assert property(

    pc_hardening_enabled
    && pc_mux == MRET

    ##0 seq_non_hardened_jump(
      kill_id,
      halt_id,
      jump_in_id,
      id_first_op,
      mepc)
    |->
    alert_major_due_to_pc_err
  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed mret instruction does not set the major alert.\n");


  a_glitch_xsecure_pc_hardening_branch_decision_hardening_enabled: assert property(

    pc_hardening_enabled
    && !dataindtiming_enabled //Make sure the branch decision is not always taken

    ##0 seq_non_hardened_jump(
      kill_ex,
      halt_ex,
      branch_in_ex,
      ex_first_op,
      branch_decision)

    |->

    alert_major_due_to_pc_err //Decision is first untaken then taken
    || $past(alert_major_due_to_pc_err) //Decision is first taken than untaken

  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed branch decision does not set the major alert.\n");


  //Verify that the major alert is set due to pc hardening fault when the PC target of a jump instruction or a branch decision is unstable, and the PC hardening feature is disabled

  a_glitch_xsecure_pc_hardening_branch_hardening_disabled: assert property(

    !pc_hardening_enabled

    ##0 seq_non_hardened_jump(
      kill_ex,
      halt_ex,
      branch_in_ex,
      ex_first_op,
      branch_target)
    |->
    !alert_major_due_to_pc_err
  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed branch instruction (jump location) sets the major alert even though PC hardening is off.\n");


  a_glitch_xsecure_pc_hardening_jump_hardening_disabled: assert property(

    !pc_hardening_enabled
    && pc_mux == JUMP

    ##0 seq_non_hardened_jump(
      kill_id,
      halt_id,
      jump_in_id,
      id_first_op,
      jump_target)

    |->
    !alert_major_due_to_pc_err
  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed jump instruction sets the major alert even though PC hardening is off.\n");

  a_glitch_xsecure_pc_hardening_mret_hardening_disabled: assert property(

    !pc_hardening_enabled

    && pc_mux == MRET

    ##0 seq_non_hardened_jump(
      kill_id,
      halt_id,
      jump_in_id,
      id_first_op,
      mepc)

    |->
    !alert_major_due_to_pc_err
  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed mret instruction sets the major alert even though PC hardening is off.\n");


  a_glitch_xsecure_pc_hardening_branch_decision_hardening_disabled: assert property(

    !pc_hardening_enabled
    && !dataindtiming_enabled //Make sure the branch decision is not always taken

    ##0 seq_non_hardened_jump(
      kill_ex,
      halt_ex,
      branch_in_ex,
      ex_first_op,
      branch_decision)

    |->

    !alert_major_due_to_pc_err //Decision is first untaken then taken
    && !$past(alert_major_due_to_pc_err) //Decision is first taken than untaken

  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed branch instruction (decision calculation) sets the major alert even though PC hardening is off.\n");


  endmodule : uvmt_cv32e40s_xsecure_hardened_pc_assert

