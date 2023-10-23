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


module uvmt_cv32e40s_xsecure_dummy_and_hint_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  import isa_decoder_pkg::*;
  import support_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
    //Interfaces:
    uvma_rvfi_instr_if_t rvfi_if,
    uvma_rvfi_csr_if_t rvfi_mcountinhibit_if,
    uvma_rvfi_csr_if_t rvfi_dcsr_if,

    //Signals:
    input logic rst_ni,
    input logic clk_i,
    input logic gated_clk_enabled,

    //CSRs:
    input logic rnddummy_enabled,
    input logic rndhint_enabled,
    input logic [3:0] dummy_freq,
    input logic [31:0][63:0] mhpmcounter,
    input logic [31:0] mcountinhibit,
    input logic [11:0] csr_waddr,

    //LFSR:
    input logic lfsr0_seed_we,
    input logic lfsr1_seed_we,
    input logic lfsr2_seed_we,
    input logic [31:0] lfsr0_seed,
    input logic [31:0] lfsr1_seed,
    input logic [31:0] lfsr2_seed,
    input logic [31:0] lfsr0,
    input logic [31:0] lfsr1,
    input logic [31:0] lfsr2,
    input logic [31:0] lfsr0_n,
    input logic [31:0] lfsr1_n,
    input logic [31:0] lfsr2_n,
    input logic lfsr0_clk_en,
    input logic lfsr1_clk_en,
    input logic lfsr2_clk_en,

    //IF:
    input logic if_hint,
    input logic if_dummy,
    input logic kill_if,
    input logic ptr_in_if,
    input logic if_valid,
    input logic if_first_op,

    //ID:
    input logic [31:0] operand_a,
    input logic [31:0] operand_b,
    input logic [31:0] id_instr,
    input logic id_dummy,
    input logic id_hint,
    input logic kill_id,
    input logic id_ready,
    input logic id_valid,
    input logic id_last_op,

    //EX:
    input logic kill_ex,
    input logic ex_ready,

    //WB:
    input logic kill_wb,
    input logic wb_dummy,
    input logic wb_hint,
    input logic wb_valid,
    input logic [31:0] wb_instr,

    //Controller:
    input logic debug_mode,
    input logic stopcount_in_debug

  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) || !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";


  // Local parameters:
  localparam MCYCLE = 0;
  localparam MINSTRET = 2;
  localparam STOPCOUNT = 10;

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

  logic gated_clk_enabled_q1;

  always @(posedge clk_i) begin
    if(!rst_ni) begin
      gated_clk_enabled_q1 <= 0;
    end else begin
      gated_clk_enabled_q1 <= gated_clk_enabled;
    end
  end

  logic        is_wb_csr_write;
  asm_t        wb_instr_decoded;
  asm_t        id_instr_decoded;

  always_comb begin
    wb_instr_decoded    <= decode_instr(wb_instr);
    id_instr_decoded    <= decode_instr(id_instr);
    is_wb_csr_write     <= wb_valid && is_csr_write_spec_f(wb_instr_decoded);
  end

  //Verify that dummy and hint instructions are default disabled

  property p_setting_default_off(logic setting);
    $rose(rst_ni)
    |->
    !setting;
  endproperty

  a_xsecure_dummy_default_off: assert property (
	  p_setting_default_off(
	    rnddummy_enabled)
  ) else `uvm_error(info_tag, "Dummy instruction setting is on when exiting reset.\n");

  a_xsecure_hint_default_off: assert property (
	  p_setting_default_off(
	    rndhint_enabled)
  ) else `uvm_error(info_tag, "Hint instruction setting is on when exiting reset.\n");


  //Verify that the dummy and hint features are configurable
  //Features enabled:

  property p_generate_dummy_hint_instruction(feature_enabled, hint_or_dummy);

    feature_enabled
    && id_valid
    && hint_or_dummy;
  endproperty

  c_xsecure_dummy_instr_generated_dummy_instr_if_dummy_setting_is_on: cover property(
    p_generate_dummy_hint_instruction(
      rnddummy_enabled,
      id_dummy)
  );

  c_xsecure_hint_instr_generated_hint_instr_if_hint_setting_is_on: cover property(
    p_generate_dummy_hint_instruction(
      rndhint_enabled,
      id_hint)
  );

  //Feature disabled:

  property p_dont_generate_dummy_hint_instruction(feature_enabled, hint_or_dummy);

    !feature_enabled
    && id_valid
    |->
    !hint_or_dummy;
  endproperty

  a_xsecure_dummy_instr_dont_generated_dummy_instr_if_dummy_setting_is_off: assert property(
    p_dont_generate_dummy_hint_instruction(
      rnddummy_enabled,
      id_dummy)
  ) else `uvm_error(info_tag, "We generated a dummy instruction even though the dummy setting was off.\n");

  a_xsecure_hint_instr_dont_generated_hint_instr_if_hint_setting_is_off: assert property(
    p_dont_generate_dummy_hint_instruction(
      rndhint_enabled,
      id_hint)
  ) else `uvm_error(info_tag, "We generated a hint instruction even though the hint setting was off.\n");


  //Verify that dummy instructions are inserted in the IF stage

  a_xsecure_dummy_instr_is_inserted_in_if_stage: assert property(
    if_valid
    && id_ready

    ##1 id_dummy
    && id_valid

    |->
    $past(if_dummy)
  ) else `uvm_error(info_tag, "The dummy instruction is not inserted in the IF stage.\n");


  //Verify that dummy and hint instructions are either add, and, mul, or bltu instructions

  property p_dummy_hint_instr_is_either_add_and_mul_or_bltu(id_dummy_or_hint);

    id_valid
    && id_dummy_or_hint

    |->
    id_instr_decoded.instr == ADD
    || id_instr_decoded.instr == AND
    || id_instr_decoded.instr == MUL
    || id_instr_decoded.instr == BLTU;

  endproperty

  a_xsecure_dummy_instr_is_add_and_mul_or_bltu: assert property(
    p_dummy_hint_instr_is_either_add_and_mul_or_bltu(
      id_dummy)
  ) else `uvm_error(info_tag, "The dummy instruction is neither an ADD, MUL nor a BTLU instruction.\n");

  a_xsecure_hint_instr_is_add_and_mul_or_bltu: assert property(
    p_dummy_hint_instr_is_either_add_and_mul_or_bltu(
      id_dummy)
  ) else `uvm_error(info_tag, "The hint instruction is neither an ADD, MUL nor a BTLU instruction.\n");


  property p_dummy_hint_instr_is_add_and_or_mul(id_dummy_or_hint, instr_name);

    id_valid
    && id_dummy_or_hint

    && id_instr_decoded.instr == instr_name;

  endproperty

  c_xsecure_dummy_instr_is_add: cover property(
    p_dummy_hint_instr_is_add_and_or_mul(
      id_dummy,
      ADD)
  );

  c_xsecure_hint_instr_is_add: cover property(
    p_dummy_hint_instr_is_add_and_or_mul(
      id_hint,
      ADD)
  );

  c_xsecure_dummy_instr_is_and: cover property(
    p_dummy_hint_instr_is_add_and_or_mul(
      id_dummy,
      AND)
  );

  c_xsecure_hint_instr_is_and: cover property(
    p_dummy_hint_instr_is_add_and_or_mul(
      id_hint,
      AND)
  );

  c_xsecure_dummy_instr_is_mul: cover property(
    p_dummy_hint_instr_is_add_and_or_mul(
      id_dummy,
      MUL)
  );

  c_xsecure_hint_instr_is_mul: cover property(
    p_dummy_hint_instr_is_add_and_or_mul(
      id_hint,
      MUL)
  );


  property p_dummy_hint_instr_bltu(id_dummy_or_hint, instr_name);

    id_valid
    && id_dummy_or_hint

    && id_instr_decoded.instr == instr_name;
  endproperty

  c_xsecure_dummy_instr_is_bltu: cover property(
    p_dummy_hint_instr_bltu(
      id_dummy,
      BLTU)
  );

  c_xsecure_hint_instr_is_btlu: cover property(
    p_dummy_hint_instr_bltu(
      id_hint,
      BLTU)
  );


  //Verify that the dummy and hint instructions in form of bltu operations always jump to the subsequent instruction

  property p_bltu_dummy_hint_instr_jumps_to_the_subsequent_instruction(id_dummy_or_hint, dummy_hint_increment);

    id_valid
    && id_dummy_or_hint
    && id_instr_decoded.instr == BLTU

    |->
    id_instr_decoded.imm.imm_value == dummy_hint_increment;
  endproperty

  a_xsecure_dummy_instr_bltu_jumping: assert property(
    p_bltu_dummy_hint_instr_jumps_to_the_subsequent_instruction(
      id_dummy,
      DUMMY_INCREMENT) //A dummy bltu instruction increment with 0 as it is an instruction inserted by the hardware itself
  ) else `uvm_error(info_tag, "A dummy branch instruction does not jump to the next non-dummy instruction.\n");

  a_xsecure_hint_instr_bltu_jumping: assert property(
    p_bltu_dummy_hint_instr_jumps_to_the_subsequent_instruction(
      id_hint,
      HINT_INCREMENT) //A hint bltu instruction increment with 2 as it is an compressed instruction inserted in software
  ) else `uvm_error(info_tag, "A hint branch instruction does not jump to the next non-hint instruction.\n");


  //Verify that the source for the operands to dummy and hint instructions can be either of the x0 to x32 registers


  property p_dummy_hint_instr_rs(id_dummy_or_hint, rs, addr_rs);

    id_valid
    && id_dummy_or_hint

    && rs == addr_rs;
  endproperty

  for (genvar rs_addr = 0; rs_addr < 32; rs_addr++) begin

    c_xsecure_dummy_source_reg1: cover property(
      p_dummy_hint_instr_rs(
        id_dummy,
        id_instr_decoded.rs1.gpr.raw,
        rs_addr)
    );

    c_xsecure_dummy_source_reg2: cover property(
      p_dummy_hint_instr_rs(
        id_dummy,
        id_instr_decoded.rs2.gpr.raw,
        rs_addr)
    );

    c_xsecure_hint_source_reg1: cover property(
      p_dummy_hint_instr_rs(
        id_hint,
        id_instr_decoded.rs1.gpr.raw,
        rs_addr)
    );

    c_xsecure_hint_source_reg2: cover property(
      p_dummy_hint_instr_rs(
        id_hint,
        id_instr_decoded.rs2.gpr.raw,
        rs_addr)
    );

  end


  //Verify that the source for the operands to dummy and hint instructions are fetched from the LFSR1 and LFSR2 registers,
  //Or that we fetch data from the R0 register

  property p_dummy_hint_instr_operands_originate_from_lfsr1_lfsr2_or_r0(id_dummy_or_hint);

    id_valid
    && id_dummy_or_hint

    |->
    ((operand_a == (lfsr1))
    || id_instr_decoded.rs1.gpr.gpr == X0)

    && ((operand_b == (lfsr2))
    || id_instr_decoded.rs2.gpr.gpr == X0);

  endproperty

  a_xsecure_dummy_instr_operands_from_lfsr1_lfsr2_or_r0: assert property (
    p_dummy_hint_instr_operands_originate_from_lfsr1_lfsr2_or_r0(
      id_dummy)
  ) else `uvm_error(info_tag, "Dummy instruction does not fetch data from LFSR1 and LFSR2.\n");

  a_xsecure_hint_instr_operands_from_lfsr1_lfsr2_or_r0: assert property (
    p_dummy_hint_instr_operands_originate_from_lfsr1_lfsr2_or_r0(
      id_hint)
  ) else `uvm_error(info_tag, "Hint instruction does not fetch data from LFSR1 and LFSR2.\n");



  //Verify that the destination register of dummy and hint instructions are R0

  property p_dummy_hint_destination_is_r0(id_dummy_or_hint);

    id_valid
    && id_dummy_or_hint
    && id_instr_decoded.instr != BLTU //branch instructions do not use a destination register

    |->
    id_instr_decoded.rd.gpr.gpr == X0;
  endproperty


  a_xsecure_dummy_instr_destination_is_r0: assert property (
    p_dummy_hint_destination_is_r0(id_dummy)
  ) else `uvm_error(info_tag, "The result of a dummy instruction is not stored in the x0 GPR.\n");

  a_xsecure_hint_instr_destination_is_r0: assert property (
    p_dummy_hint_destination_is_r0(id_hint)
  ) else `uvm_error(info_tag, "The result of a hint instruction is not stored in the x0 GPR.\n");



  //Verify that the LFSR registers are updated if a dummy or hint instruction is executed

  property p_dummy_hint_update_lfsr0(is_dummy_or_hint, lfsr);

    //Make sure we detect a dummy/hint instruction
    is_dummy_or_hint
    && if_valid
    && id_ready

    |=>

    lfsr != $past(lfsr);
  endproperty


  a_xsecure_dummy_updates_lfsr0: assert property (
    p_dummy_hint_update_lfsr0(
      if_dummy,
      lfsr0)
  ) else `uvm_error(info_tag, "A dummy instruction does not update the LFSR0 register.\n");

  a_xsecure_hint_updates_lfsr0: assert property (
    p_dummy_hint_update_lfsr0(
      if_hint,
      lfsr0)
  ) else `uvm_error(info_tag, "A hint instruction does not update the LFSR0 register.\n");


  property p_dummy_hint_update_lfsr1_lfsr2(is_dummy_or_hint, lfsr);

    //Make sure we detect a dummy/hint instruction
    is_dummy_or_hint
    && id_valid
    && ex_ready
    && id_last_op

    |=>
    lfsr != $past(lfsr);
  endproperty


  a_xsecure_dummy_updates_lfsr1: assert property (
    p_dummy_hint_update_lfsr1_lfsr2(
      id_dummy,
      lfsr1)
  ) else `uvm_error(info_tag, "A dummy instruction does not update the LFSR1 register.\n");

  a_xsecure_dummy_updates_lfsr2: assert property (
    p_dummy_hint_update_lfsr1_lfsr2(
      id_dummy,
      lfsr2)
  ) else `uvm_error(info_tag, "A dummy instruction does not update the LFSR2 register.\n");

  a_xsecure_hint_updates_lfsr1: assert property (
    p_dummy_hint_update_lfsr1_lfsr2(
      id_hint,
      lfsr1)
  ) else `uvm_error(info_tag, "A hint instruction does not update the LFSR1 register.\n");

  a_xsecure_hint_updates_lfsr2: assert property (
    p_dummy_hint_update_lfsr1_lfsr2(
      id_hint,
      lfsr2)
  ) else `uvm_error(info_tag, "A hint instruction does not update the LFSR2 register.\n");


  //Verify that the source registers of the dummy and hint instructions generate pipeline stalls as normal

  //If a load instruction set a value in rd=rd_load, and the source register of the next instruction is rs=rd_load,
  //then the next instruction must wait in id stage untill rd_load is set. This also account for dummy and hint instructions.
  //The assertions below state that this is true for dummy and hint instruction by verifying that if there is a dummy/hint
  //instruction in wb stage when there is a load instruction in the rvfi stage, the dummy/hint instruction does not have rs=rd_load

  a_xsecure_dummy_instr_load_dummy_stall: assert property (

    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_LOAD
    && rvfi_if.rvfi_rd1_addr != '0

    && wb_dummy
    && wb_valid

    |->
    wb_instr[24:20] != rvfi_if.rvfi_rd1_addr
    && wb_instr[19:15] != rvfi_if.rvfi_rd1_addr
  ) else `uvm_error(info_tag, "A dummy instruction does not stall in ID stage even though the value of a source register is not fetched from memory yet.\n");


  property p_load_stall_for_hints;
    logic [4:0] id_hint_rs1;
    logic [4:0] id_hint_rs2;

    //Make sure the instruction propegates through the pipeline
    (!kill_if
    & !kill_id
    & !kill_ex
    & !kill_wb
    ) throughout (

      (id_hint
      && id_valid
      && ex_ready,

      id_hint_rs1 = id_instr_decoded.rs1.gpr.raw,
      id_hint_rs2 = id_instr_decoded.rs2.gpr.raw)

      ##0 first_match(##[2:$]
      wb_hint
      && wb_valid)

      ##0 rvfi_if.rvfi_valid
      && !rvfi_if.rvfi_trap
      && rvfi_if.rvfi_insn[6:0] == OPCODE_LOAD
      && rvfi_if.rvfi_rd1_addr != '0
    )

    |->
    id_hint_rs1 != rvfi_if.rvfi_rd1_addr
    && id_hint_rs2 != rvfi_if.rvfi_rd1_addr;
    endproperty

  a_xsecure_hint_instr_load_hint_stall: assert property (
    p_load_stall_for_hints
  ) else `uvm_error(info_tag, "A hint instruction does not stall in ID stage even though the value of a source register is not fetched from memory yet.\n");


  //Verify that both the dummy and the hint instructions update mcycle

  a_xsecure_dummy_instr_updates_mcycle: assert property (

    !stopcount_in_debug
    && !(csr_waddr == cv32e40s_pkg::CSR_MCYCLE || csr_waddr == cv32e40s_pkg::CSR_MCYCLEH) //Writing to the register can give unsequential behavior

    ##1 gated_clk_enabled_q1 //mcycle is only updated when the gated clock is active
    && !mcountinhibit[MCYCLE] //mcycle is operative (not inhibited)

    |->
    mhpmcounter[MCYCLE] == ($past(mhpmcounter[MCYCLE]) + 1) //mcycle should count every clock cycle, including the clock cycles used by dummy and hint instructions
    or mhpmcounter[MCYCLE] == '0 && $past(mhpmcounter[MCYCLE]) == REGISTER_MHPMCOUNTER_MCYCLE_FULL //Reset
    or mhpmcounter[MCYCLE] == $past(mhpmcounter[MCYCLE]) && $past(mcountinhibit[MCYCLE]) //Allow the first mcycle count to not increment

  ) else `uvm_error(info_tag, "Dummy and hint instructions do not update the MCYCLE register.\n");



  //Verify that dummy instructions do not update minstret

  a_xsecure_dummy_instr_do_not_update_minstret: assert property (

    !mcountinhibit[MINSTRET] //minstret is operative (not inhibited)
    && wb_valid
    && wb_dummy

    |=>
    mhpmcounter[MINSTRET] == $past(mhpmcounter[MINSTRET])

  ) else `uvm_error(info_tag, "Dummy instruction updated the minstret register.\n");



  //Verify that hint instructions update minstret

  a_xsecure_hint_instructions_updates_minstret: assert property (

    !rvfi_mcountinhibit_if.rvfi_csr_rdata[MINSTRET] //minstret was operative (not inhibited)
    && (!rvfi_dcsr_if.rvfi_csr_rdata[STOPCOUNT] || !rvfi_if.rvfi_dbg_mode) //the minstret counter was not stopped

    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap

    //Hint instruction:
    && rvfi_if.is_cslli
    && rvfi_if.rvfi_rd1_addr == REGISTER_X0
    && rvfi_if.cslli_shamt != '0

    |->
    mhpmcounter[MINSTRET] == $past(mhpmcounter[MINSTRET]) + 1

  ) else `uvm_error(info_tag, "Hint instruction did not update the minstret register.\n");


  //Verify that dummy instructions appears within specifyed frequency

  //There is at least one dummy instruction for every <num_valid_instructions> valid instructions
  sequence seq_dummy_instr_within_normal_valid_instructions (num_valid_instructions);
    @(posedge clk_i)

    // Reset the checker every time we see a dummy instruction
    first_match(if_dummy)
    within
    // Within n+1 issued instruction, there should be a dummy instruction (dummy counts as issued)
    (if_valid && if_first_op && id_ready && !ptr_in_if)[->0:(num_valid_instructions + 1)];
  endsequence

  property p_xsecure_dummy_instr_frequency(num_normal_valid_instructions_per_dummy_instruction, logic [3:0] rnddummyfreq_reg_value_min, logic [3:0] rnddummyfreq_reg_value_max);
    disable iff (
      !rnddummy_enabled
      || dummy_freq < rnddummyfreq_reg_value_min
      || dummy_freq > rnddummyfreq_reg_value_max
      || debug_mode
      || is_wb_csr_write && wb_instr_decoded.csr.address.name inside { CPUCTRL, SECURESEED0 }
    )

    // This should always hold, unless disabled by any of the clauses in the disable iff-statement above
    seq_dummy_instr_within_normal_valid_instructions(num_normal_valid_instructions_per_dummy_instruction);
  endproperty


  a_xsecure_dummy_instr_frequency_4: assert property (
	  p_xsecure_dummy_instr_frequency(
      4,
      FREQ_SETTING_4_MIN,
      FREQ_SETTING_4_MAX)
  ) else `uvm_error(info_tag, "There is not 1 dummy instruction per 1-4 instructions.\n");

  a_xsecure_dummy_instr_frequency_8: assert property (
	  p_xsecure_dummy_instr_frequency(
      8,
      FREQ_SETTING_8_MIN,
      FREQ_SETTING_8_MAX)
  ) else `uvm_error(info_tag, "There is not 1 dummy instruction per 1-8 instructions.\n");

  a_xsecure_dummy_instr_frequency_16: assert property (
	  p_xsecure_dummy_instr_frequency(
      16,
      FREQ_SETTING_16_MIN,
      FREQ_SETTING_16_MAX)
  ) else `uvm_error(info_tag, "There is not 1 dummy instruction per 1-16 instructions.\n");

  a_xsecure_dummy_instr_frequency_32: assert property (
	  p_xsecure_dummy_instr_frequency(
      32,
      FREQ_SETTING_32_MIN,
      FREQ_SETTING_32_MAX)
  ) else `uvm_error(info_tag, "There is not 1 dummy instruction per 1-32 instructions.\n");

  a_xsecure_dummy_instr_frequency_64: assert property (
	  p_xsecure_dummy_instr_frequency(
      64,
      FREQ_SETTING_64_MIN,
      FREQ_SETTING_64_MAX)
  ) else `uvm_error(info_tag, "There is not 1 dummy instruction per 1-64 instructions.\n");


  //Verify that the LFSR's seeds are reset when lockups are detected

  sequence seq_xsecure_dummy_hint_instr_LFSRx_lockup_detection(logic get_new_lfsr_value, logic seed_we, logic [31:0] seed_w_value, logic [31:0] lfsr_n);

    (rnddummy_enabled || rndhint_enabled)
    && get_new_lfsr_value
    && ((!seed_we && lfsr_n == '0)
    || (seed_we && seed_w_value == '0));
  endsequence


  a_xsecure_dummy_hint_instr_LFSR0_lockup_reset: assert property (
	  seq_xsecure_dummy_hint_instr_LFSRx_lockup_detection(
      lfsr0_clk_en,
      lfsr0_seed_we,
      lfsr0_seed,
      lfsr0_n)

    |=>

    lfsr0 == CORE_PARAM_LFSR0_CFG[31:0]
  ) else `uvm_error(info_tag, "LFSR0 does not reset to the default value when there is a lookup error (given that we do not write to the LFSR register).\n");


  a_xsecure_dummy_hint_instr_LFSR1_lockup_reset: assert property (
	  seq_xsecure_dummy_hint_instr_LFSRx_lockup_detection(
      lfsr1_clk_en,
      lfsr1_seed_we,
      lfsr1_seed,
      lfsr1_n)

    |=>

    lfsr1 == CORE_PARAM_LFSR1_CFG[31:0]

  ) else `uvm_error(info_tag, "LFSR0 does not reset to the default value when there is a lookup error (given that we do not write to the LFSR register).\n");


  a_xsecure_dummy_hint_instr_LFSR2_lockup_reset: assert property (
	  seq_xsecure_dummy_hint_instr_LFSRx_lockup_detection(
      lfsr2_clk_en,
      lfsr2_seed_we,
      lfsr2_seed,
      lfsr2_n)

    |=>

    lfsr2 == CORE_PARAM_LFSR2_CFG[31:0]
  ) else `uvm_error(info_tag, "LFSR2 does not reset to the default value when there is a lookup error (given that we do not write to the LFSR register).\n");



  //Verify that we can write the value of the LFSRs by writing to the secureseed CSRs

  property p_write_LFSR_by_writing_to_the_secureseed(csr_addr_secureseed, lfsr);

    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap

    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[14:12] == FUNCT3_CSRRW_REG
    && rvfi_if.rvfi_insn[31:20] == csr_addr_secureseed
    && rvfi_if.rvfi_rs1_rdata != 5'b0000_0

    |->
    lfsr == rvfi_if.rvfi_rs1_rdata;
  endproperty


  a_xsecure_dummy_hint_instr_LFSR0_write_secureseed0_reg: assert property (
    p_write_LFSR_by_writing_to_the_secureseed(
      CSR_SECURESEED0,
      lfsr0)
  ) else `uvm_error(info_tag, "The LFSR0 register is not written to, even though the secureseed CSR is written to (CSR register instruction).\n");

  a_xsecure_dummy_hint_instr_LFSR1_write_secureseed1_reg: assert property (
    p_write_LFSR_by_writing_to_the_secureseed(
      CSR_SECURESEED1,
      lfsr1)
  ) else `uvm_error(info_tag, "The LFSR1 register is not written to, even though the secureseed CSR is written to (CSR register instruction).\n");

  a_xsecure_dummy_hint_instr_LFSR2_write_secureseed2_reg: assert property (
    p_write_LFSR_by_writing_to_the_secureseed(
      CSR_SECURESEED2,
      lfsr2)
  ) else `uvm_error(info_tag, "The LFSR2 register is not written to, even though the secureseed CSR is written to (CSR register instruction).\n");


  //Verify that hint instructions appears as slt instructions on RVFI

  a_xsecure_hint_instructions_reports_on_rvfi_as_slli: assert property (

    wb_hint
    && wb_valid

    ##1 rvfi_if.rvfi_valid

    |->
    //The hint instruction shall appear as a c.slli instruction with rd=x0 and shamt != 0
    (rvfi_if.is_cslli
    && rvfi_if.rvfi_rd1_addr == REGISTER_X0
    && rvfi_if.cslli_shamt != '0)
    || !rvfi_if.is_instr_bus_valid

  ) else `uvm_error(info_tag, "Hint instruction do not appears as a c.slli instruction with rd=x0 and shamt != 0 on RVFI.\n");


  endmodule : uvmt_cv32e40s_xsecure_dummy_and_hint_assert
