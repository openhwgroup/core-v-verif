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

  localparam FUNCT7_DIV_REM_INSTRUCTION = 7'b0000001;
  localparam FUNCT3_DIV_REM_INSTRUCTION_MSB = 1'b1;

  localparam FUNCT3_COMPR_BRANCH_2_MSBS = 2'b11;
  localparam OPCODE_COMPR_BRANCH = 2'b01;

  localparam FUNCT3_COMPR_SLLI = 3'b000;
  localparam OPCODE_COMPR_SLLI = 2'b10;

  localparam REGISTER_MHPMCOUNTER_MCYCLE_FULL = 64'hFFFFFFFFFFFFFFFF;

  localparam REGISTER_x0 = 5'b00000; //TODO: x to X


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

  //Descriptive signal names
  logic [5:0] rvfi_c_slli_shamt;
  assign rvfi_c_slli_shamt = {rvfi_if.rvfi_insn[12], rvfi_if.rvfi_insn[6:2]};

  logic [4:0] if_id_pipe_instr_rs1;
  logic [4:0] if_id_pipe_instr_rs2;
  logic [4:0] if_id_pipe_instr_rd;
  logic [6:0] if_id_pipe_instr_opcode;
  logic [12:0] if_id_pipe_bltu_incrementation;

  assign if_id_pipe_instr_rs1 = xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[19:15];
  assign if_id_pipe_instr_rs2 = xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[24:20];
  assign if_id_pipe_instr_rd = xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[11:7];
  assign if_id_pipe_instr_opcode = xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[6:0];
  assign if_id_pipe_bltu_incrementation = {xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[31],
    xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[7],
    xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[30:25],
    xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[11:8],
    1'b0};


  logic [2:0] rvfi_insn_cmpr_funct3;
  logic [1:0] rvfi_insn_cmpr_opcode;

  assign rvfi_insn_cmpr_funct3 = rvfi_if.rvfi_insn[15:13];
  assign rvfi_insn_cmpr_opcode = rvfi_if.rvfi_insn[1:0];

  //The alert signals used the gated clock, so we must therefore make sure the gated clock is enabled.
  logic core_i_sleep_unit_i_core_clock_gate_i_clk_en_q1;

  always @(posedge clk_i) begin
    if(!rst_ni) begin
      core_i_sleep_unit_i_core_clock_gate_i_clk_en_q1 <= 0;
    end else begin
      core_i_sleep_unit_i_core_clock_gate_i_clk_en_q1 <= xsecure_if.core_i_sleep_unit_i_core_clock_gate_i_clk_en;
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


  ////////// DUMMY AND HINT INSTRUCTION INSERTED IN IF /////////

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

  a_xsecure_hint_instruction_is_inserted_in_if_stage: assert property(
    p_dummy_hint_instruction_is_inserted_in_if_stage(
      xsecure_if.core_if_id_pipe_instr_meta_hint,
      xsecure_if.core_i_if_stage_i_instr_hint)
  ) else `uvm_error(info_tag, "The hint instruction is not inserted in the IF stage.\n");


  ////////// BLTU DUMMY AND HINT INSTRUCTIONS JUMP TO THE SUBSEQUENT INSTRUCTION //////////

  property p_bltu_dummy_hint_instruction_jumps_to_the_subsequent_instruction(dummy_hint_in_id_stage, dummy_hint_increment);
    //Make sure we detect a new instruction in the IF ID pipe
    $past(xsecure_if.core_if_stage_if_valid_o)
    && $past(xsecure_if.core_if_stage_id_ready_i)

    //Make sure the instruction is a dummy/hint
    && dummy_hint_in_id_stage

    //Make sure the dummy/hint is a branch instruction
    && if_id_pipe_instr_opcode == cv32e40s_pkg::OPCODE_BRANCH

    |->
    //Make sure we jump to next instruction (dummy: PC + 0)(hint: PC + 2)
    if_id_pipe_bltu_incrementation == dummy_hint_increment;
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
    //Check that the sr1 part of the instruction originates from the LFSR1 register
    if_id_pipe_instr_rs1 == $past(xsecure_if.core_if_stage_gen_dummy_instr_dummy_instr_lfsr_rs1)

    //Check that the sr2 part of the instruction originates from the LFSR2 register
    && if_id_pipe_instr_rs2 == $past(xsecure_if.core_if_stage_gen_dummy_instr_dummy_instr_lfsr_rs2);

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
    && if_id_pipe_instr_opcode != OPCODE_BRANCH

    |->
    //Check that the destination register is x0
    if_id_pipe_instr_rd == REGISTER_x0;
  endproperty

  a_xsecure_dummy_instruction_destination_is_x0: assert property (
    p_dummy_hint_destination_is_x0(xsecure_if.core_if_id_pipe_instr_meta_dummy)
  ) else `uvm_error(info_tag, "The result of a dummy instruction is not stored in the x0 GPR.\n");

  a_xsecure_hint_instruction_destination_is_x0: assert property (
    p_dummy_hint_destination_is_x0(xsecure_if.core_if_id_pipe_instr_meta_hint)
  ) else `uvm_error(info_tag, "The result of a hint instruction is not stored in the x0 GPR.\n");


  ////////// DUMMY AND HINT INSTRUCTION UPDATES MCYCLE //////////

  a_xsecure_dummy_instruction_updates_mcycle: assert property (

    //Make sure the gated clock is enabled
    core_i_sleep_unit_i_core_clock_gate_i_clk_en_q1

    //Make sure that mcycle is operative (not inhibited)
    && !xsecure_if.core_cs_registers_mcountinhibit_q_mcycle_inhibit

    //Make sure we do not write to mcycle
    && !($past(xsecure_if.core_cs_registers_csr_en_gated)
    && ($past(xsecure_if.core_cs_registers_csr_waddr == cv32e40s_pkg::CSR_MCYCLE)) || $past(xsecure_if.core_cs_registers_csr_waddr == cv32e40s_pkg::CSR_MCYCLEH))

    |->
    //Make sure the mcycle counts every cycle (including the clock cycles used by dummy and hint instructions)
    xsecure_if.core_cs_registers_mhpmcounter_mcycle == ($past(xsecure_if.core_cs_registers_mhpmcounter_mcycle) + 1)

    //But make sure it resets in case of overflow
    or xsecure_if.core_cs_registers_mhpmcounter_mcycle == '0 && $past(xsecure_if.core_cs_registers_mhpmcounter_mcycle) == REGISTER_MHPMCOUNTER_MCYCLE_FULL

    //And allow the first mcycle count to not increment
    or xsecure_if.core_cs_registers_mhpmcounter_mcycle == $past(xsecure_if.core_cs_registers_mhpmcounter_mcycle) && $past(xsecure_if.core_cs_registers_mcountinhibit_q_mcycle_inhibit)

  ) else `uvm_error(info_tag, "Dummy and hint instructions do not update the MCYCLE register.\n");


  ////////// DUMMY INSTRUCTIONS DO NOT UPDATE MINSTRET //////////

  a_xsecure_dummy_instruction_do_not_update_minstret: assert property (

    //Make sure the gated clock is enabled
    core_i_sleep_unit_i_core_clock_gate_i_clk_en_q1

    //Make sure minstret is operative (not inhibited)
    && !xsecure_if.core_cs_registers_mcountinhibit_q_minstret_inhibit

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

    //Make sure the gated clock is enabled
    core_i_sleep_unit_i_core_clock_gate_i_clk_en_q1

    //Make sure that minstret is operative (not inhibited)
    && !xsecure_if.core_cs_registers_mcountinhibit_q_minstret_inhibit

    //Make sure there is a hint instruction in the WB stage
    && xsecure_if.core_ex_wb_pipe_instr_meta_hint

    //Make sure a valid hint instruction retires
    ##1 rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap
    && rvfi_insn_cmpr_funct3 == FUNCT3_COMPR_SLLI
    && rvfi_insn_cmpr_opcode == OPCODE_COMPR_SLLI
    && rvfi_if.rvfi_rd1_addr == REGISTER_x0
    && rvfi_c_slli_shamt != '0

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


  ////////// RESET SEED WHENEVER THERE IS A LOCKUP ERROR //////////

  property p_xsecure_dummy_instruction_LFSRx_lockup_reset(integer x, logic core_cs_registers_xsecure_lfsrx_seed_we, logic [31:0] core_xsecure_ctrl_lfsrx, logic [31:0] core_LFSRx_CFG_default_seed);

    //Make sure there is a lockup error on register x
    xsecure_if.core_cs_registers_xsecure_lfsr_lockup[x] == LOCKUP_ERROR

    //Make sure we check the case where we do not specificly write a new value to the register at this moment (because writing new value has higher priority than setting default seed)
    && !core_cs_registers_xsecure_lfsrx_seed_we

    //Make sure the LFSR registers reseeds to default value
    |->
    ##1 core_xsecure_ctrl_lfsrx == core_LFSRx_CFG_default_seed;

  endproperty

  //LFSR0
  a_xsecure_dummy_instruction_LFSR0_lockup_reset: assert property (
	  p_xsecure_dummy_instruction_LFSRx_lockup_reset(
      0,
      xsecure_if.core_cs_registers_xsecure_lfsr0_seed_we,
	    xsecure_if.core_xsecure_ctrl_lfsr0,
      xsecure_if.core_LFSR0_CFG_default_seed)
  ) else `uvm_error(info_tag, "LFSR0 does not reset to the default value when there is a lookup error (given that we do not write to the LFSR register).\n");

  //LFSR1
  a_xsecure_dummy_instruction_LFSR1_lockup_reset: assert property (
	  p_xsecure_dummy_instruction_LFSRx_lockup_reset(
      1,
      xsecure_if.core_cs_registers_xsecure_lfsr1_seed_we,
	    xsecure_if.core_xsecure_ctrl_lfsr1,
      xsecure_if.core_LFSR1_CFG_default_seed)
  ) else `uvm_error(info_tag, "LFSR0 does not reset to the default value when there is a lookup error (given that we do not write to the LFSR register).\n");

  //LFSR2
  a_xsecure_dummy_instruction_LFSR2_lockup_reset: assert property (
	  p_xsecure_dummy_instruction_LFSRx_lockup_reset(
      2,
      xsecure_if.core_cs_registers_xsecure_lfsr2_seed_we,
	    xsecure_if.core_xsecure_ctrl_lfsr2,
      xsecure_if.core_LFSR2_CFG_default_seed)
  ) else `uvm_error(info_tag, "LFSR0 does not reset to the default value when there is a lookup error (given that we do not write to the LFSR register).\n");


  ////////// HINT INSTRUCTION APPEARS AS SLT ON RVFI //////////

  a_xsecure_hint_instructions_reports_on_rvfi_as_slli: assert property (

    //Make sure the gated clock is enabled
    core_i_sleep_unit_i_core_clock_gate_i_clk_en_q1

    //Make sure there is a hint instruction in the WB stage
    && xsecure_if.core_ex_wb_pipe_instr_meta_hint

    //Make sure we retire the hint instruction in the next cycle
    ##1 rvfi_if.rvfi_valid

    |->
    //Verify that the hint instruction appears as c.slli instruction with rd=x0 and shamt != 0
    rvfi_insn_cmpr_funct3 == FUNCT3_COMPR_SLLI
    && rvfi_insn_cmpr_opcode == OPCODE_COMPR_SLLI
    && rvfi_if.rvfi_rd1_addr == REGISTER_x0
    && rvfi_c_slli_shamt != '0

  ) else `uvm_error(info_tag, "Hint instruction do not appears as a c.slli instruction with rd=x0 and shamt != 0 on RVFI.\n");


  endmodule : uvmt_cv32e40s_xsecure_dummy_and_hint_assert