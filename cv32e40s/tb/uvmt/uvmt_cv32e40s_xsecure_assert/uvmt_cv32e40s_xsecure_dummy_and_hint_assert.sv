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


module uvmt_cv32e40s_xsecure_dummy_and_hint_assert
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

  property p_xsecure_setting_default_off(logic xsecure_setting);

    //Make sure that when exiting reset mode the xsecure setting is off
    $rose(rst_ni)
    |->
    !xsecure_setting;
  endproperty


    // Local parameters:
  localparam LOCKUP_ERROR = 1'b1;

  localparam FUNCT3_ADD = 3'b000;
  localparam FUNCT3_AND = 3'b111;
  localparam FUNCT3_MUL = 3'b000;
  localparam FUNCT3_BLTU = 3'b110;

  localparam FUNCT7_ADD = 7'b0000000;
  localparam FUNCT7_AND = 7'b0000000;
  localparam FUNCT7_MUL = 7'b0000001;

  localparam FUNCT3_CSRRW_IMM = 3'b101;
  localparam FUNCT3_CSRRW_REG = 3'b001;

  localparam FUNCT3_COMPR_SLLI = 3'b000;
  localparam OPCODE_COMPR_SLLI = 2'b10;

  localparam REGISTER_MHPMCOUNTER_MCYCLE_FULL = 64'hFFFFFFFFFFFFFFFF;

  localparam REGISTER_X0 = 5'b00000;

  localparam FREQ_SETTING_64_MIN = 4'b1000;
  localparam FREQ_SETTING_64_MAX = 4'b1111;
  localparam FREQ_SETTING_32_MIN = 4'b0100;
  localparam logic [3:0] FREQ_SETTING_32_MAX = FREQ_SETTING_64_MIN -1;
  localparam FREQ_SETTING_16_MIN = 4'b0010;
  localparam logic [3:0] FREQ_SETTING_16_MAX = FREQ_SETTING_32_MIN -1;
  localparam FREQ_SETTING_8_MIN = 4'b0001;
  localparam logic [3:0] FREQ_SETTING_8_MAX = FREQ_SETTING_16_MIN -1;
  localparam FREQ_SETTING_4_MIN = 4'b0000;
  localparam logic [3:0] FREQ_SETTING_4_MAX = FREQ_SETTING_8_MIN -1;

  localparam DUMMY_INCREMENT = 0;
  localparam HINT_INCREMENT = 2;

  //The alert signals used the gated clock, so we must therefore make sure the gated clock is enabled. TODO: update text
  logic core_i_sleep_unit_i_clock_en_q1;

  always @(posedge clk_i) begin
    if(!rst_ni) begin
      core_i_sleep_unit_i_clock_en_q1 <= 0;
    end else begin
      core_i_sleep_unit_i_clock_en_q1 <= xsecure_if.core_i_sleep_unit_i_clock_en;
    end
  end

  ////////// DUMMY AND HINT INSTRUCTIONS ARE DEFAULT DISABLED //////////

  a_xsecure_dummy_default_off: assert property (
	  p_xsecure_setting_default_off(
	    xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy)
  ) else `uvm_error(info_tag, "Dummy instruction setting is on when exiting reset.\n");

  a_xsecure_hint_default_off: assert property (
	  p_xsecure_setting_default_off(
	    xsecure_if.core_xsecure_ctrl_cpuctrl_rndhint)
  ) else `uvm_error(info_tag, "Hint instruction setting is on when exiting reset.\n");


  ////////// DUMMY AND HINT INSTRUCTIONS ARE CONFIGURABLE /////////

  // Check that we do not generate dummy/hint instructions when dummy/hint is disabled:

  property p_dont_generate_dummy_hint_instruction_if_setting_is_off(hint_or_dummy_setting, hint_or_dummy_instruction);
    //Make sure the dummy/hint instruction setting is off
    !hint_or_dummy_setting

    //Make sure we look at a valid instruction
    && xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i

    //Make sure we do not generate a dummy/hint instruction
    |=>
    !hint_or_dummy_instruction;
  endproperty

  a_xsecure_dummy_instruction_dont_generated_dummy_instruction_if_dummy_setting_is_off: assert property(
    p_dont_generate_dummy_hint_instruction_if_setting_is_off(
      xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy,
      xsecure_if.core_if_id_pipe_instr_meta_dummy)
  ) else `uvm_error(info_tag, "We generated a dummy instruction even though the dummy setting was off.\n");

  a_xsecure_hint_instruction_dont_generated_hint_instruction_if_hint_setting_is_off: assert property(
    p_dont_generate_dummy_hint_instruction_if_setting_is_off(
      xsecure_if.core_xsecure_ctrl_cpuctrl_rndhint,
      xsecure_if.core_if_id_pipe_instr_meta_hint)
  ) else `uvm_error(info_tag, "We generated a hint instruction even though the hint setting was off.\n");

  // Verify that we do generate dummy/hint instructions when dummy/hint is enabled:

  property p_generate_dummy_hint_instruction_if_setting_is_on(hint_or_dummy_setting, hint_or_dummy_instruction);
    //Make sure the dummy/hint instruction setting is off
    hint_or_dummy_setting

    //Make sure we look at a valid instruction
    && xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i

    //Make sure we do not generate a dummy/hint instruction
    ##1
    hint_or_dummy_instruction;
  endproperty

  c_xsecure_dummy_instruction_generated_dummy_instruction_if_dummy_setting_is_on: cover property(
    p_generate_dummy_hint_instruction_if_setting_is_on(
      xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy,
      xsecure_if.core_if_id_pipe_instr_meta_dummy)
  );

  c_xsecure_hint_instruction_generated_hint_instruction_if_hint_setting_is_on: cover property(
    p_generate_dummy_hint_instruction_if_setting_is_on(
      xsecure_if.core_xsecure_ctrl_cpuctrl_rndhint,
      xsecure_if.core_if_id_pipe_instr_meta_hint)
  );

  ////////// DUMMY INSTRUCTION INSERTED IN IF /////////

  property p_dummy_hint_instruction_is_inserted_in_if_stage(dummy_hint_in_id_stage, dummy_hint_in_if_stage);
    //Make sure the instruction in the ID stage is a dummy/hint instruction
    dummy_hint_in_id_stage

    //Make sure the instruction in the ID stage is valid
    && $past(xsecure_if.core_if_stage_if_valid_o)
    && $past(xsecure_if.core_if_stage_id_ready_i)

    |->
    //Make sure the dummy/hint instruction originated from the IF stage
    $past(dummy_hint_in_if_stage);
  endproperty

  a_xsecure_dummy_instruction_is_inserted_in_if_stage: assert property(
    p_dummy_hint_instruction_is_inserted_in_if_stage(
      xsecure_if.core_if_id_pipe_instr_meta_dummy,
      xsecure_if.core_i_if_stage_i_dummy_insert)
  ) else `uvm_error(info_tag, "The dummy instruction is not inserted in the IF stage.\n");


  ////////// BLTU DUMMY AND HINT INSTRUCTIONS ARE EITHER AN ADD, AND, MUL OR BTLU INSTRUCTION //////////

  property p_dummy_hint_instruction_opcode_is_either_add_and_mul_or_bltu(dummy_hint_in_id_stage);

    //Make sure the instruction insterted into the ID stage is valid
    xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i

    //Make sure the instruction in ID stage is a dummy/hint instruction
    ##1 dummy_hint_in_id_stage

    |->
    //Make sure the instruction is either an ADD, ADD, MUL or BTLU instruction
    (xsecure_if.if_id_pipe_opcode == OPCODE_OP
    && xsecure_if.if_id_pipe_funct3 == FUNCT3_ADD
    && xsecure_if.if_id_pipe_funct7 == FUNCT7_ADD)

    || (xsecure_if.if_id_pipe_opcode == OPCODE_OP
    && xsecure_if.if_id_pipe_funct3 == FUNCT3_AND
    && xsecure_if.if_id_pipe_funct7 == FUNCT7_AND)

    || (xsecure_if.if_id_pipe_opcode == OPCODE_OP
    && xsecure_if.if_id_pipe_funct3 == FUNCT3_MUL
    && xsecure_if.if_id_pipe_funct7 == FUNCT7_MUL)

    || (xsecure_if.if_id_pipe_opcode == OPCODE_BRANCH
    && xsecure_if.if_id_pipe_funct3 == FUNCT3_BLTU);

  endproperty

  a_xsecure_dummy_instruction_is_add_mul_or_btlu: assert property(
    p_dummy_hint_instruction_opcode_is_either_add_and_mul_or_bltu(
      xsecure_if.core_if_id_pipe_instr_meta_dummy)
  ) else `uvm_error(info_tag, "The dummy instruction is neither an ADD, MUL nor a BTLU instruction.\n");

  a_xsecure_hint_instruction_is_add_mul_or_btlu: assert property(
    p_dummy_hint_instruction_opcode_is_either_add_and_mul_or_bltu(
      xsecure_if.core_if_id_pipe_instr_meta_dummy)
  ) else `uvm_error(info_tag, "The hint instruction is neither an ADD, MUL nor a BTLU instruction.\n");


  property p_dummy_hint_instruction_add_and_mul(dummy_hint_in_id_stage, opcode, funct3, funct7);

    //Make sure the instruction insterted into the ID stage is valid
    xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i

    //Make sure the instruction in ID stage is a dummy/hint instruction
    ##1 dummy_hint_in_id_stage

    //Make sure the instruction is either an ADD or MUL instruction
    && xsecure_if.if_id_pipe_opcode == opcode
    && xsecure_if.if_id_pipe_funct3 == funct3
    && xsecure_if.if_id_pipe_funct7 == funct7;

  endproperty

  c_xsecure_dummy_instruction_is_add: cover property(
    p_dummy_hint_instruction_add_and_mul(
      xsecure_if.core_if_id_pipe_instr_meta_dummy,
      OPCODE_OP,
      FUNCT3_ADD,
      FUNCT7_ADD)
  );

  c_xsecure_hint_instruction_is_add: cover property(
    p_dummy_hint_instruction_add_and_mul(
      xsecure_if.core_if_id_pipe_instr_meta_dummy,
      OPCODE_OP,
      FUNCT3_ADD,
      FUNCT7_ADD)
  );

  c_xsecure_dummy_instruction_is_and: cover property(
    p_dummy_hint_instruction_add_and_mul(
      xsecure_if.core_if_id_pipe_instr_meta_dummy,
      OPCODE_OP,
      FUNCT3_AND,
      FUNCT7_AND)
  );

  c_xsecure_hint_instruction_is_and: cover property(
    p_dummy_hint_instruction_add_and_mul(
      xsecure_if.core_if_id_pipe_instr_meta_dummy,
      OPCODE_OP,
      FUNCT3_AND,
      FUNCT7_AND)
  );

  c_xsecure_dummy_instruction_is_mul: cover property(
    p_dummy_hint_instruction_add_and_mul(
      xsecure_if.core_if_id_pipe_instr_meta_dummy,
      OPCODE_OP,
      FUNCT3_MUL,
      FUNCT7_MUL)
  );

  c_xsecure_hint_instruction_is_mul: cover property(
    p_dummy_hint_instruction_add_and_mul(
      xsecure_if.core_if_id_pipe_instr_meta_dummy,
      OPCODE_OP,
      FUNCT3_MUL,
      FUNCT7_MUL)
  );


  property p_dummy_hint_instruction_bltu(dummy_hint_in_id_stage, opcode, funct3);

    //Make sure the instruction insterted into the ID stage is valid
    xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i

    //Make sure the instruction in ID stage is a dummy/hint instruction
    ##1 dummy_hint_in_id_stage

    //Make sure the instruction is a BTLU instruction
    && xsecure_if.if_id_pipe_opcode == opcode
    && xsecure_if.if_id_pipe_funct3 == funct3;

  endproperty

  c_xsecure_dummy_instruction_is_bltu: cover property(
    p_dummy_hint_instruction_bltu(
      xsecure_if.core_if_id_pipe_instr_meta_dummy,
      OPCODE_BRANCH,
      FUNCT3_BLTU)
  );

  c_xsecure_hint_instruction_is_btlu: cover property(
    p_dummy_hint_instruction_bltu(
      xsecure_if.core_if_id_pipe_instr_meta_dummy,
      OPCODE_BRANCH,
      FUNCT3_BLTU)
  );


  ////////// BLTU DUMMY AND HINT INSTRUCTIONS JUMP TO THE SUBSEQUENT INSTRUCTION //////////

  property p_bltu_dummy_hint_instruction_jumps_to_the_subsequent_instruction(dummy_hint_in_id_stage, dummy_hint_increment);
    //Make sure we detect a new instruction in the IF ID pipe
    $past(xsecure_if.core_if_stage_if_valid_o)
    && $past(xsecure_if.core_if_stage_id_ready_i)

    //Make sure the instruction is a dummy/hint
    && dummy_hint_in_id_stage

    //Make sure the dummy/hint is a branch instruction
    && xsecure_if.if_id_pipe_opcode == cv32e40s_pkg::OPCODE_BRANCH

    |->
    //Make sure we jump to next instruction (dummy: PC + 0)(hint: PC + 2)
    xsecure_if.if_id_pipe_bltu_incrementation == dummy_hint_increment;
  endproperty

  a_xsecure_dummy_instruction_bltu_jumping: assert property(
    p_bltu_dummy_hint_instruction_jumps_to_the_subsequent_instruction(
      xsecure_if.core_if_id_pipe_instr_meta_dummy,
      DUMMY_INCREMENT)
  ) else `uvm_error(info_tag, "A dummy branch instruction does not jump to the next non-dummy instruction.\n");

  a_xsecure_hint_instruction_bltu_jumping: assert property(
    p_bltu_dummy_hint_instruction_jumps_to_the_subsequent_instruction(
      xsecure_if.core_if_id_pipe_instr_meta_hint,
      HINT_INCREMENT)
  ) else `uvm_error(info_tag, "A hint branch instruction does not jump to the next non-hint instruction.\n");


  ////////// DUMMY AND HINT INSTRUCTION OPERAND SOURCES //////////

  property p_dummy_hint_instruction_operands_originate_from_LFSR1_and_LFSR2(dummy_hint_in_id_stage);

    //Make sure we detect a new instruction in the IF ID pipe
    $past(xsecure_if.core_if_stage_if_valid_o)
    && $past(xsecure_if.core_if_stage_id_ready_i)

    //Make sure the detected instruction is a dummy/hint instruction
    && dummy_hint_in_id_stage

    |->
    //Check that the sr1 part of the instruction originates from the LFSR1 register, or is zero if RS1 = x0
    ((xsecure_if.core_i_id_stage_i_operand_a == (xsecure_if.core_xsecure_ctrl_lfsr1))
    || xsecure_if.if_id_pipe_rs1 == REGISTER_X0)

    //Check that the sr2 part of the instruction originates from the LFSR2 register
    && ((xsecure_if.core_i_id_stage_i_operand_b == (xsecure_if.core_xsecure_ctrl_lfsr2))
    || xsecure_if.if_id_pipe_rs2 == REGISTER_X0);

  endproperty

  a_xsecure_dummy_instruction_operands_from_LFSR1_and_LFSR2: assert property (
    p_dummy_hint_instruction_operands_originate_from_LFSR1_and_LFSR2(
      xsecure_if.core_if_id_pipe_instr_meta_dummy)
  ) else `uvm_error(info_tag, "Dummy instruction does not fetch data from LFSR1 and LFSR2.\n");

  a_xsecure_hint_instruction_operands_from_LFSR1_and_LFSR2: assert property (
    p_dummy_hint_instruction_operands_originate_from_LFSR1_and_LFSR2(
      xsecure_if.core_if_id_pipe_instr_meta_hint)
  ) else `uvm_error(info_tag, "Hint instruction does not fetch data from LFSR1 and LFSR2.\n");


  ////////// DUMMY AND HINT INSTRUCTION DESTINATION //////////

  property p_dummy_hint_destination_is_x0(dummy_hint_in_id_stage);

    //Make sure we detect a new instruction in the IF ID pipe
    $past(xsecure_if.core_if_stage_if_valid_o)
    && $past(xsecure_if.core_if_stage_id_ready_i)

    //Make sure the detected instruction is a dummy/hint instruction
    && dummy_hint_in_id_stage

    //Make sure the instruction is not a branch (as they do not use a destination register)
    && xsecure_if.if_id_pipe_opcode != OPCODE_BRANCH

    |->
    //Check that the destination register is x0
    xsecure_if.if_id_pipe_rd == REGISTER_X0;
  endproperty

  a_xsecure_dummy_instruction_destination_is_x0: assert property (
    p_dummy_hint_destination_is_x0(xsecure_if.core_if_id_pipe_instr_meta_dummy)
  ) else `uvm_error(info_tag, "The result of a dummy instruction is not stored in the x0 GPR.\n");

  a_xsecure_hint_instruction_destination_is_x0: assert property (
    p_dummy_hint_destination_is_x0(xsecure_if.core_if_id_pipe_instr_meta_hint)
  ) else `uvm_error(info_tag, "The result of a hint instruction is not stored in the x0 GPR.\n");

    ////////// DUMMY AND HINT INSTRUCTION UPDATE LFSR REGISTERS /////////

  property p_dummy_hint_update_lfsr0(dummy_hint_in_if_stage, lfsr_reg, lfsr_n_reg, write_lfsr, write_lfsr_value);

    //Make sure we detect a dummy instruction
    dummy_hint_in_if_stage
    && xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i

    |=>

    (lfsr_reg == $past(lfsr_n_reg))
    || (lfsr_reg == LFSR_CFG_DEFAULT.default_seed)
    || ($past(write_lfsr) && write_lfsr_value == $past(lfsr_reg));

  endproperty


  a_xsecure_dummy_updates_lfsr0: assert property (
    p_dummy_hint_update_lfsr0(
      xsecure_if.core_i_if_stage_i_dummy_insert,
      xsecure_if.core_xsecure_ctrl_lfsr0,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_lfsr_n,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_seed_we_i,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_seed_i)
  ) else `uvm_error(info_tag, "A dummy instruction does not update the LFSR0 register.\n");

  a_xsecure_hint_updates_lfsr0: assert property (
    p_dummy_hint_update_lfsr0(
      xsecure_if.core_i_if_stage_i_instr_hint,
      xsecure_if.core_xsecure_ctrl_lfsr0,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_lfsr_n,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_seed_we_i,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_seed_i)
  ) else `uvm_error(info_tag, "A hint instruction does not update the LFSR0 register.\n");


  property p_dummy_hint_update_lfsr1_lfsr2(dummy_hint_in_if_stage, lfsr_reg, lfsr_n_reg, write_lfsr, write_lfsr_value);

    //Make sure we detect a dummy instruction
    dummy_hint_in_if_stage
    && xsecure_if.core_id_stage_id_valid_o
    && xsecure_if.core_id_stage_ex_ready_i
    && xsecure_if.core_i_id_stage_i_last_op

    |=>

    (lfsr_reg == $past(lfsr_n_reg))
    || (lfsr_reg == LFSR_CFG_DEFAULT.default_seed)
    || ($past(write_lfsr) && write_lfsr_value == $past(lfsr_reg));
  endproperty


  a_xsecure_dummy_updates_lfsr1: assert property (
    p_dummy_hint_update_lfsr1_lfsr2(
      xsecure_if.core_if_id_pipe_instr_meta_dummy,
      xsecure_if.core_xsecure_ctrl_lfsr1,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_lfsr_n,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_seed_we_i,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_seed_i)
  ) else `uvm_error(info_tag, "A dummy instruction does not update the LFSR1 register.\n");

  a_xsecure_dummy_updates_lfsr2: assert property (
    p_dummy_hint_update_lfsr1_lfsr2(
      xsecure_if.core_if_id_pipe_instr_meta_dummy,
      xsecure_if.core_xsecure_ctrl_lfsr2,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_lfsr_n,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_seed_we_i,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_seed_i)
  ) else `uvm_error(info_tag, "A dummy instruction does not update the LFSR2 register.\n");

  a_xsecure_hint_updates_lfsr1: assert property (
    p_dummy_hint_update_lfsr1_lfsr2(
      xsecure_if.core_if_id_pipe_instr_meta_hint,
      xsecure_if.core_xsecure_ctrl_lfsr1,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_lfsr_n,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_seed_we_i,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_seed_i)
  ) else `uvm_error(info_tag, "A hint instruction does not update the LFSR1 register.\n");

  a_xsecure_hint_updates_lfsr2: assert property (
    p_dummy_hint_update_lfsr1_lfsr2(
      xsecure_if.core_if_id_pipe_instr_meta_hint,
      xsecure_if.core_xsecure_ctrl_lfsr2,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_lfsr_n,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_seed_we_i,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_seed_i)
  ) else `uvm_error(info_tag, "A hint instruction does not update the LFSR2 register.\n");


  ////////// DUMMY AND HINT INSTRUCTIONS STALL IN THE ID STAGE IF THEY ARE SUCCESSOR OF A LOAD INSTRUCTION //////////

  a_xsecure_dummy_instruction_load_dummy_stall: assert property (
    //Random gyldig instruksjon
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_LOAD
    && rvfi_if.rvfi_rd1_addr != '0

    //Dummy instruksjon i wb
    && xsecure_if.core_ex_wb_pipe_instr_meta_dummy //Must be so we know it is not a compressed instruction
    && xsecure_if.core_wb_stage_wb_valid_o

    |->
    //dummy rs1 og rs2 != random instruksjon rd
    xsecure_if.core_i_ex_wb_pipe_instr_bus_resp_rdata[24:20] != rvfi_if.rvfi_rd1_addr
    && xsecure_if.core_i_ex_wb_pipe_instr_bus_resp_rdata[19:15] != rvfi_if.rvfi_rd1_addr
  ) else `uvm_error(info_tag, "A dummy instruction does not stall in ID stage even though the value of a source register is not fetched from memory yet.\n");


  property load_then_hint_instruction_hazard;
    logic [4:0] id_hint_rs1;
    logic [4:0] id_hint_rs2;

    //Make sure the instruction propegates through the pipeline
    (!xsecure_if.core_i_wb_stage_i_ctrl_fsm_i_kill_if
    & !xsecure_if.core_i_wb_stage_i_ctrl_fsm_i_kill_id
    & !xsecure_if.core_i_wb_stage_i_ctrl_fsm_i_kill_ex
    & !xsecure_if.core_i_wb_stage_i_ctrl_fsm_i_kill_wb
    ) throughout (

      //Make sure there is detected a hint instruction that propegates from id to ex stage
      (xsecure_if.core_if_id_pipe_instr_meta_hint && xsecure_if.core_id_stage_id_valid_o && xsecure_if.core_id_stage_ex_ready_i,

      //Make sure we store the hint instructions source register addresses
      id_hint_rs1 = xsecure_if.if_id_pipe_rs1,
      id_hint_rs2 = xsecure_if.if_id_pipe_rs2)

      //Make sure we detect the same hint instruction as above in the WB stage
      ##0 first_match(##[2:$]
      xsecure_if.core_ex_wb_pipe_instr_meta_hint
      && xsecure_if.core_wb_stage_wb_valid_o)

      //Make sure the instruction currently reported on the RVFI is a load instruction
      ##0 rvfi_if.rvfi_valid
      && !rvfi_if.rvfi_trap
      && rvfi_if.rvfi_insn[6:0] == OPCODE_LOAD
      && rvfi_if.rvfi_rd1_addr != '0
    )

    |->
    //Verify that the source register of the hint register is not the same register as the load instruction stores its result in, to make sure pipeline stalls occurs as they are supposed to
    id_hint_rs1 != rvfi_if.rvfi_rd1_addr
    && id_hint_rs2 != rvfi_if.rvfi_rd1_addr;
  endproperty

  a_xsecure_hint_instruction_load_hint_stall: assert property (
    load_then_hint_instruction_hazard
  ) else `uvm_error(info_tag, "A hint instruction does not stall in ID stage even though the value of a source register is not fetched from memory yet.\n");


  ////////// DUMMY AND HINT INSTRUCTION UPDATES MCYCLE //////////

  a_xsecure_dummy_instruction_updates_mcycle: assert property (

    //Make sure that mcycle is operative (not inhibited)
    !xsecure_if.core_cs_registers_mcountinhibit_rdata_mcycle

    //Make sure we count according to the gated clock
    && core_i_sleep_unit_i_clock_en_q1

    //Make sure the counters are not stopped
    && !$past(xsecure_if.core_i_cs_registers_i_debug_stopcount)

    //Make sure we do not write to the mcycle or mcycleh CSRs
    && !($past(xsecure_if.core_cs_registers_csr_waddr) == cv32e40s_pkg::CSR_MCYCLE || $past(xsecure_if.core_cs_registers_csr_waddr) == cv32e40s_pkg::CSR_MCYCLEH)

    |->
    //Make sure the mcycle counts every cycle (including the clock cycles used by dummy and hint instructions)
    xsecure_if.core_cs_registers_mhpmcounter_mcycle == ($past(xsecure_if.core_cs_registers_mhpmcounter_mcycle) + 1)

    //But make sure it resets in case of overflow
    or xsecure_if.core_cs_registers_mhpmcounter_mcycle == '0 && $past(xsecure_if.core_cs_registers_mhpmcounter_mcycle) == REGISTER_MHPMCOUNTER_MCYCLE_FULL

    //And allow the first mcycle count to not increment
    or xsecure_if.core_cs_registers_mhpmcounter_mcycle == $past(xsecure_if.core_cs_registers_mhpmcounter_mcycle) && $past(xsecure_if.core_cs_registers_mcountinhibit_rdata_mcycle)

  ) else `uvm_error(info_tag, "Dummy and hint instructions do not update the MCYCLE register.\n");


  ////////// DUMMY INSTRUCTIONS DO NOT UPDATE MINSTRET //////////

  a_xsecure_dummy_instruction_do_not_update_minstret: assert property (

    //Make sure minstret is operative (not inhibited)
    !xsecure_if.core_cs_registers_mcountinhibit_rdata_minstret

    //Make sure there is a dummy instruction
    && xsecure_if.core_ex_wb_pipe_instr_meta_dummy

    //Make sure the dummy instruction is ready to retire
    && xsecure_if.core_wb_stage_wb_valid_o

    //Make sure the minstret counter ignores the retired dummy instruction
    |=>
    xsecure_if.core_cs_registers_mhpmcounter_minstret == $past(xsecure_if.core_cs_registers_mhpmcounter_minstret)

  ) else `uvm_error(info_tag, "Dummy instruction updated the minstret register.\n");



  ////////// HINT INSTRUCTIONS UPDATE MINSTRET //////////

  a_xsecure_hint_instructions_updates_minstret: assert property (

    //Make sure that minstret is operative (not inhibited)
    !xsecure_if.core_cs_registers_mcountinhibit_rdata_minstret

    //Make sure the counters are not stopped
    && !xsecure_if.core_i_cs_registers_i_debug_stopcount

    //Make sure there is a hint instruction in the WB stage
    && xsecure_if.core_ex_wb_pipe_instr_meta_hint

    //Make sure a valid hint instruction retires
    ##1 rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap
    && xsecure_if.rvfi_cmpr_funct3 == FUNCT3_COMPR_SLLI
    && xsecure_if.rvfi_cmpr_opcode == OPCODE_COMPR_SLLI
    && rvfi_if.rvfi_rd1_addr == REGISTER_X0
    && xsecure_if.rvfi_c_slli_shamt != '0

    |->
    //Make sure the minstret counter is updated
    xsecure_if.core_cs_registers_mhpmcounter_minstret == $past(xsecure_if.core_cs_registers_mhpmcounter_minstret) + 1

  ) else `uvm_error(info_tag, "Hint instruction did not update the minstret register.\n");


  ////////// DUMMY INSTRUCTION FREQUENCY //////////

  sequence seq_dummy_instruction_within_normal_valid_instructions (num_normal_valid_instructions);
    @(posedge clk_i)

    //Make sure we detect a dummy instruction
    xsecure_if.core_i_if_stage_i_dummy_insert
    && xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i

    //Make sure we detect up to <num_normal_valid_instructions> non-dummy instructions
    ##1 (xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i)[->0:(num_normal_valid_instructions)];
  endsequence


  property p_xsecure_dummy_instruction_frequency(num_normal_valid_instructions_per_dummy_instruction, logic [3:0] rnddummyfreq_reg_value_min, logic [3:0] rnddummyfreq_reg_value_max);

    //Make sure the dummy setting is on
    (xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy

    //Make sure the frequency of the dummy instructions is in between the specified range
    && xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummyfreq >= rnddummyfreq_reg_value_min
    && xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummyfreq <= rnddummyfreq_reg_value_max

    //Make sure the controller is not in debug mode
    && !xsecure_if.core_controller_controller_fsm_debug_mode_q

    //Make sure the dummy instructions are always enabled
    && xsecure_if.core_if_stage_gen_dummy_instr_dummy_instr_dummy_en)

    //Make sure we detect new instructions in the if id pipe
    throughout (xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i)[->(num_normal_valid_instructions_per_dummy_instruction)+1]

    |->
    //Make sure that we detect one valid dummy instruction in between the number of normal valid instructions
    seq_dummy_instruction_within_normal_valid_instructions(num_normal_valid_instructions_per_dummy_instruction).triggered;

  endproperty


  //FREQ = 4
  a_xsecure_dummy_instruction_frequency_4: assert property (
	  p_xsecure_dummy_instruction_frequency(
      4,
      FREQ_SETTING_4_MIN,
      FREQ_SETTING_4_MAX)
  ) else `uvm_error(info_tag, "There is not 1 dummy instruction per 1-4 instructions.\n");

  //FREQ = 8
  a_xsecure_dummy_instruction_frequency_8: assert property (
	  p_xsecure_dummy_instruction_frequency(
      8,
      FREQ_SETTING_8_MIN,
      FREQ_SETTING_8_MAX)
  ) else `uvm_error(info_tag, "There is not 1 dummy instruction per 1-8 instructions.\n");

  //FREQ = 16
  a_xsecure_dummy_instruction_frequency_16: assert property (
	  p_xsecure_dummy_instruction_frequency(
      16,
      FREQ_SETTING_16_MIN,
      FREQ_SETTING_16_MAX)
  ) else `uvm_error(info_tag, "There is not 1 dummy instruction per 1-16 instructions.\n");

  //FREQ = 32
  a_xsecure_dummy_instruction_frequency_32: assert property (
	  p_xsecure_dummy_instruction_frequency(
      32,
      FREQ_SETTING_32_MIN,
      FREQ_SETTING_32_MAX)
  ) else `uvm_error(info_tag, "There is not 1 dummy instruction per 1-32 instructions.\n");

  //FREQ = 64
  a_xsecure_dummy_instruction_frequency_64: assert property (
	  p_xsecure_dummy_instruction_frequency(
      64,
      FREQ_SETTING_64_MIN,
      FREQ_SETTING_64_MAX)
  ) else `uvm_error(info_tag, "There is not 1 dummy instruction per 1-64 instructions.\n");


  ////////// RESET SEED WHENEVER THERE A LOCKUP IS DETECTED //////////

  sequence p_xsecure_dummy_hint_instruction_LFSRx_lockup_detection(logic get_new_lfsr_value, logic seed_we, logic [31:0] seed_value, logic [31:0] lfsrx_n);

    (xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy || xsecure_if.core_xsecure_ctrl_cpuctrl_rndhint)
    throughout
    (get_new_lfsr_value
    && ((!seed_we && lfsrx_n == '0)
    || (seed_we && seed_value == '0)));
  endsequence

  //LFSR0
  a_xsecure_dummy_hint_instruction_LFSR0_lockup_reset: assert property (
	  p_xsecure_dummy_hint_instruction_LFSRx_lockup_detection(
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_clock_en,
      xsecure_if.core_cs_registers_xsecure_lfsr0_seed_we,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_seed_i,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_lfsr_n)

    |=>
	  //Make sure the LFSR registers reseeds to default value
    xsecure_if.core_xsecure_ctrl_lfsr0 == LFSR_CFG_DEFAULT.default_seed

  ) else `uvm_error(info_tag, "LFSR0 does not reset to the default value when there is a lookup error (given that we do not write to the LFSR register).\n");

  //LFSR1
  a_xsecure_dummy_hint_instruction_LFSR1_lockup_reset: assert property (
	  p_xsecure_dummy_hint_instruction_LFSRx_lockup_detection(
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_clock_en,
      xsecure_if.core_cs_registers_xsecure_lfsr1_seed_we,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_seed_i,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_lfsr_n)

    |=>
	  //Make sure the LFSR registers reseeds to default value
    xsecure_if.core_xsecure_ctrl_lfsr1 == LFSR_CFG_DEFAULT.default_seed

  ) else `uvm_error(info_tag, "LFSR0 does not reset to the default value when there is a lookup error (given that we do not write to the LFSR register).\n");

  //LFSR2
  a_xsecure_dummy_hint_instruction_LFSR2_lockup_reset: assert property (
	  p_xsecure_dummy_hint_instruction_LFSRx_lockup_detection(
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_clock_en,
      xsecure_if.core_cs_registers_xsecure_lfsr2_seed_we,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_seed_i,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_lfsr_n)

    |=>
	  //Make sure the LFSR registers reseeds to default value
    xsecure_if.core_xsecure_ctrl_lfsr2 == LFSR_CFG_DEFAULT.default_seed
  ) else `uvm_error(info_tag, "LFSR2 does not reset to the default value when there is a lookup error (given that we do not write to the LFSR register).\n");


  ////////// WRITES TO THE LFSRS SEED THE SECURESEED REGISTERS //////////


  property p_xsecure_LFSRx_write_secureseedx_reg(csr_addr_secureseedx, lfsrx);

    //Make sure we retire a write CSR instruction that wirtes the value of a GPR to the CSR SECURESEEDX
    xsecure_if.rvfi_opcode == OPCODE_SYSTEM
    && xsecure_if.rvfi_funct3 == FUNCT3_CSRRW_REG
    && xsecure_if.rvfi_csr == csr_addr_secureseedx

    //MAke sure the value of the GPR is not zero
    && rvfi_if.rvfi_rs1_rdata != 5'b0000_0

    //Make sure the instruction is retired without traps
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap

    |->

    //Verify that the LFSRx register is written by writing to the CSR SECURESEEDX
    lfsrx == rvfi_if.rvfi_rs1_rdata;
  endproperty


  a_xsecure_dummy_hint_instruction_LFSR0_write_secureseed0_reg: assert property (
    p_xsecure_LFSRx_write_secureseedx_reg(
      CSR_SECURESEED0,
      xsecure_if.core_xsecure_ctrl_lfsr0)
  ) else `uvm_error(info_tag, "The LFSR0 register is not written to, even though the secureseed CSR is written to (CSR register instruction).\n");

  a_xsecure_dummy_hint_instruction_LFSR1_write_secureseed1_reg: assert property (
    p_xsecure_LFSRx_write_secureseedx_reg(
      CSR_SECURESEED1,
      xsecure_if.core_xsecure_ctrl_lfsr1)
  ) else `uvm_error(info_tag, "The LFSR1 register is not written to, even though the secureseed CSR is written to (CSR register instruction).\n");

  a_xsecure_dummy_hint_instruction_LFSR2_write_secureseed2_reg: assert property (
    p_xsecure_LFSRx_write_secureseedx_reg(
      CSR_SECURESEED2,
      xsecure_if.core_xsecure_ctrl_lfsr2)
  ) else `uvm_error(info_tag, "The LFSR2 register is not written to, even though the secureseed CSR is written to (CSR register instruction).\n");


  ////////// HINT INSTRUCTION APPEARS AS SLT ON RVFI //////////

  a_xsecure_hint_instructions_reports_on_rvfi_as_slli: assert property (

    //Make sure there is a hint instruction in the WB stage
    xsecure_if.core_ex_wb_pipe_instr_meta_hint

    //Make sure we retire the hint instruction in the next cycle
    ##1 rvfi_if.rvfi_valid

    |->
    //Verify that the hint instruction appears as c.slli instruction with rd=x0 and shamt != 0
    xsecure_if.rvfi_cmpr_funct3 == FUNCT3_COMPR_SLLI
    && xsecure_if.rvfi_cmpr_opcode == OPCODE_COMPR_SLLI
    && rvfi_if.rvfi_rd1_addr == REGISTER_X0
    && xsecure_if.rvfi_c_slli_shamt != '0

  ) else `uvm_error(info_tag, "Hint instruction do not appears as a c.slli instruction with rd=x0 and shamt != 0 on RVFI.\n");


  endmodule : uvmt_cv32e40s_xsecure_dummy_and_hint_assert