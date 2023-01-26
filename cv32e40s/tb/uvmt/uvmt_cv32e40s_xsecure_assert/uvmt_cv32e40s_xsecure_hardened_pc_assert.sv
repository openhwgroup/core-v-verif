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


module uvmt_cv32e40s_xsecure_hardened_pc_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
   uvmt_cv32e40s_xsecure_if xsecure_if,
   input rst_ni,
   input clk_i
  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) | !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";
  string info_tag_glitch = "CV32E40S_XSECURE_ASSERT_COVERPOINTS (GLITCH BEHAVIOR)";

  // Local parameters:
  localparam BRANCH_STATE = 4'b0101;
  localparam JUMP_STATE = 4'b0100;
  localparam MRET_STATE = 4'b0001;

  localparam NON_CMPR_INSTRUCTION_INCREMENT = 4;
  localparam CMPR_INSTRUCTION_INCREMENT = 2;


  ////////// PC HARDENING IS ENABLED BY DEFAULT //////////

  a_xsecure_pc_hardening_default_on: assert property (
    p_xsecure_setting_default_on(
        xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening)
  ) else `uvm_error(info_tag, "PC hardening is not enabled when exiting reset.\n");

  ////////// PC HARDENING BEHAVIOUR WHEN THERE ARE NO GLITCHES //////////

  sequence seq_dummy_if_id;
    @(posedge clk_i)

    //Generate a dummy instruction
    xsecure_if.core_if_stage_instr_meta_n_dummy

    //Make sure the PC of ID and IF stage is equal when there is a dummy instruction in the ID stage
    ##1 (xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc)[*1:$];
  endsequence

  sequence seq_pc_set_stable;
    @(posedge clk_i)

    //Set the PC value to a given address
    xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_ctrl_fsm_i_pc_set

    //Make sure the PC in the IF stage remains the same until it is forwarded to the id stage (and then either incremented or set of a new valid PC jump)
    //(Uses ##2 because: In the first clock cycle the FSM signal has "reached" IF, while in the second clock cycle its stability can be checked)
    ##2 $stable(xsecure_if.core_i_if_stage_i_pc_if_o)[*1:$];
  endsequence

  a_xsecure_pc_hardening: assert property (

    //Make sure the PC hardening setting is on
    xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening

    //Make sure the inspected instruction is valid
    && $past(xsecure_if.core_if_stage_if_valid_o)
    && $past(xsecure_if.core_if_stage_id_ready_i)

    //Make sure the instruction is not a pointer (as pointers insert a non-incremental PC)
    && !xsecure_if.core_i_if_stage_i_ptr_in_if_o

    |->
    //Correct behavior requires that one of the following behaviors are true:

    //Incremental behavior as compressed or non-compressed instruction
    xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc + CMPR_INSTRUCTION_INCREMENT && $past(xsecure_if.core_i_if_stage_i_compressed_decoder_i_is_compressed_o)
    or xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc + NON_CMPR_INSTRUCTION_INCREMENT && $past(!xsecure_if.core_i_if_stage_i_compressed_decoder_i_is_compressed_o)

    //Initialization after reset
    or xsecure_if.core_i_if_stage_i_pc_if_o == 0 && xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc == 0

    //Multi cycles instruction
    or xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_if_stage_i_pc_if_o && !xsecure_if.core_i_if_id_pipe_last_op

    //Insertion of a dummy instruction
    or seq_dummy_if_id.triggered

    //PC jumping
    or seq_pc_set_stable.triggered

    //PC jumping
    or $past(xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_ctrl_fsm_i_pc_set)

  ) else `uvm_error(info_tag, "There is a PC fault in the IF stage.\n");


  ////////// PC HARDENING SET THE MAJOR ALERT IF GLITCH //////////

  sequence seq_xsecure_pc_hardening_with_glitch;
    @(posedge clk_i)

    //Make sure the inspected instruction is valid
    $past(xsecure_if.core_if_stage_if_valid_o)
    && $past(xsecure_if.core_if_stage_id_ready_i)

    //Make sure the instruction is not a pointer
    && !xsecure_if.core_i_if_stage_i_ptr_in_if_o

    //Make sure it is not icremental behaviour
    and !(xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc + CMPR_INSTRUCTION_INCREMENT && $past(xsecure_if.core_i_if_stage_i_compressed_decoder_i_is_compressed_o))
    and !(xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc + NON_CMPR_INSTRUCTION_INCREMENT && $past(!xsecure_if.core_i_if_stage_i_compressed_decoder_i_is_compressed_o))

    //Make sure the non-incremental pc is not caused by any of the following reasons:

    //Initialization after reset
    and !(xsecure_if.core_i_if_stage_i_pc_if_o == 0 && xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc == 0)

    //Multi cycles instruction
    and !(xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_if_stage_i_pc_if_o && !xsecure_if.core_i_if_id_pipe_last_op)

    //Insertion of a dummy instruction
    and !(seq_dummy_if_id.triggered)

    //PC jumping
    and !(seq_pc_set_stable.triggered)

    //PC jumping
    and !($past(xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_ctrl_fsm_i_pc_set));

  endsequence


  a_glitch_xsecure_pc_hardening_sequential_instruction_sets_alert_major: assert property (

    //Make sure the PC hardening setting is on
    xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening

    ##0 seq_xsecure_pc_hardening_with_glitch

    |=>
    //Make sure the alert major is set
    xsecure_if.core_alert_major_o

  ) else `uvm_error(info_tag_glitch, "A PC fault in the IF stage does not set the major alert when PC hardening is on.\n");


  ////////// PC HARDENING OFF: DO NOT SET THE MAJOR ALERT IF GLITCH //////////

  a_glitch_xsecure_pc_hardening_off_sequential_instruction_dont_set_alert_major: assert property (

    //Make sure the PC hardening setting is off
    !xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening

    ##0 seq_xsecure_pc_hardening_with_glitch

    |=>
    //Make sure the alert major is not set
    !xsecure_if.core_alert_major_o

  ) else `uvm_error(info_tag_glitch, "A PC fault in the IF stage does set the major alert when PC hardening is off.\n");


  ////////// PC HARDENING ON: SET THE MAJOR ALERT IF GLITCH IN PC TARGET //////////

  sequence seq_pc_hardening_jump_instruction_with_glitch(pc_hardening, fsm_state, calculated_signal);
    @(posedge clk_i)

    //Make sure pc hardening setting is set
    pc_hardening

    //Make sure the FSM is in a given state
    && xsecure_if.core_i_if_stage_i_pc_check_i_ctrl_fsm_i_pc_mux == fsm_state

    //Make sure the PC is set
    ##1 xsecure_if.core_i_if_stage_i_pc_check_i_pc_set_q

    //Make sure the calculated signal differs in the hardened cycles
    && calculated_signal != $past(calculated_signal);

  endsequence


  a_glitch_xsecure_pc_hardening_branch_set_alert_major: assert property(
    seq_pc_hardening_jump_instruction_with_glitch(
      xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening,
      BRANCH_STATE,
      xsecure_if.core_i_ex_stage_i_branch_target_o)
    |=>
    xsecure_if.core_alert_major_o
  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed branch instruction does not set the major alert.\n");

  a_glitch_xsecure_pc_hardening_jump_set_alert_major: assert property(
    seq_pc_hardening_jump_instruction_with_glitch(
      xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening,
      JUMP_STATE,
      xsecure_if.core_i_jump_target_id)
    |=>
    xsecure_if.core_alert_major_o
  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed jump instruction does not set the major alert.\n");

  a_glitch_xsecure_pc_hardening_mret_set_alert_major: assert property(
    seq_pc_hardening_jump_instruction_with_glitch(
      xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening,
      MRET_STATE,
      xsecure_if.core_i_cs_registers_i_mepc_o)
    |=>
    xsecure_if.core_alert_major_o
  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed mret instruction does not set the major alert.\n");


  ////////// PC HARDENING ON: SET THE MAJOR ALERT IF GLITCH IN BRANCH DECISION //////////

  sequence seq_pc_hardening_branch_decision_glitch(pc_hardening);
    @(posedge clk_i)

    //Make sure pc hardening setting is on
    xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening

    //Make sure the branch decision is not always taken
    && !xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming

    //Make sure the FSM is doing a branching operation
    && xsecure_if.core_i_if_stage_i_pc_check_i_ctrl_fsm_i_pc_mux == BRANCH_STATE

    //Make sure the branch decision differs in the hardened cycles
    ##1 xsecure_if.core_i_ex_stage_i_alu_i_cmp_result_o != $past(xsecure_if.core_i_ex_stage_i_alu_i_cmp_result_o);

  endsequence



  a_xsecure_pc_hardening_branch_decision_set_alert_major: assert property(

    seq_pc_hardening_branch_decision_glitch(xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening)

    |=>

    //Make sure the alert major was/is set
    xsecure_if.core_alert_major_o
    || $past(xsecure_if.core_alert_major_o)

  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed branch decision does not set the major alert.\n");


  ////////// PC HARDENING OFF: DO NOT SET THE MAJOR ALERT IF GLITCH IN PC TARGET //////////

  property p_xsecure_hardened_pc_non_sequential_dont_set_major_alert(pc_hardening, fsm_state, calculated_signal);

    seq_pc_hardening_jump_instruction_with_glitch(pc_hardening, fsm_state, calculated_signal)

    |=>
    //Make sure the alert major is not set
    !xsecure_if.core_alert_major_o;

  endproperty

  a_glitch_xsecure_pc_hardening_off_branch_set_alert_major: assert property(
    p_xsecure_hardened_pc_non_sequential_dont_set_major_alert(!
    xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening,
    BRANCH_STATE,
    xsecure_if.core_i_ex_stage_i_branch_target_o)
  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed branch instruction (jump location) sets the major alert even though PC hardening is off.\n");

  a_glitch_xsecure_pc_hardening_off_jump_set_alert_major: assert property(
    p_xsecure_hardened_pc_non_sequential_dont_set_major_alert(!
    xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening,
    JUMP_STATE,
    xsecure_if.core_i_jump_target_id)
  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed jump instruction sets the major alert even though PC hardening is off.\n");

  a_glitch_xsecure_pc_hardening_off_mret_set_alert_major: assert property(
    p_xsecure_hardened_pc_non_sequential_dont_set_major_alert(!
    xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening,
    MRET_STATE,
    xsecure_if.core_i_cs_registers_i_mepc_o)
  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed mret instruction sets the major alert even though PC hardening is off.\n");


  ////////// PC HARDENING OFF: DO NOT SET THE ALERT MAJOR IF GLITCH IN THE BRANCH DECISION //////////

  a_glitch_xsecure_pc_hardening_off_branch_decision_set_alert_major: assert property(

    seq_pc_hardening_branch_decision_glitch(!xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening)

    |=>
    //Make sure the alert major was/is not set
    !xsecure_if.core_alert_major_o
    && !$past(xsecure_if.core_alert_major_o)

  ) else `uvm_error(info_tag_glitch, "Mismatch between the computed and the recomputed branch instruction (decision calculation) sets the major alert even though PC hardening is off.\n");


  endmodule : uvmt_cv32e40s_xsecure_hardened_pc_assert