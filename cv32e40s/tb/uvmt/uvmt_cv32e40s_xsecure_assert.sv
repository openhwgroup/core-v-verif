
module uvmt_cv32e40s_xsecure_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1,
    parameter logic     SMCLIC = 0,
    parameter int       PMP_NUM_REGIONS = 2,
    parameter int       MTVT_ADDR_WIDTH = 5,
    parameter int CSR_MINTTHRESH_MASK = 32
  )
  (
   uvmt_cv32e40s_xsecure_if xsecure_if,
   uvma_rvfi_instr_if rvfi_if,
   input rst_ni,
   input clk_i
  );

  //TODO: update hardened CSR documentation as these CSRs are no longer hardened mclicbase, mscratchcsw, mscratchcswl
  //TODO: change rvfi_trap from using bit position to struct fields when the rvfi interface is updated


  // Local parameters:
  localparam NO_LOCKUP_ERRORS = 3'b000;
  localparam LOCKUP_ERROR = 1'b1;

  localparam ERROR_CODE_INSTRUCTION_ACCESS_FAULT = 6'd1;
  localparam ERROR_CODE_ILLEGAL_INSTRUCTION_FAULT = 6'd2;
  localparam ERROR_CODE_LOAD_ACCESS_FAULT = 6'd5;
  localparam ERROR_CODE_STORE_AMO_ACCESS_FAULT = 6'd7;
  localparam ERROR_CODE_INSTRUCTION_BUS_FAULT = 6'd24;

  localparam FUNC7_BRANCH_INSTRUCTION = 7'bxxxxxxx;
  localparam FUNC3_BRANCH_INSTRUCTION = 3'bxxx;

  localparam FUNC7_DIV_REM_INSTRUCTION = 7'b0000001;
  localparam FUNC3_DIV_REM_INSTRUCTION = 3'b1xx; //TODO: can be problematic with x

  localparam FUNC3_BLTU_INSTRUCTION = 3'b110;

  localparam FUNC7_MRET_INSTRUCTION = 7'b0011000;
  localparam FUNC3_MRET_INSTRUCTION = 3'b000;

  localparam OPCODE_BIT_15_TO_13_COMPR_BRANCH = 3'b11x;
  localparam OPCODE_BIT_1_TO_0_COMPR_BRANCH = 2'b01;

  localparam REGISTER_MHPMCOUNTER_MCYCLE_FULL = 64'hFFFFFFFFFFFFFFFF;

  localparam REGISTER_x0 = 5'b00000;

  localparam FREQ_SETTING_4 = 4'b0000;
  localparam FREQ_SETTING_8 = 4'b0001;
  localparam FREQ_SETTING_16 = 4'b001x;
  localparam FREQ_SETTING_32 = 4'b01xx;
  localparam FREQ_SETTING_64 = 4'b1xxx;

  localparam BRANCH_STATE = 4'b0101;
  localparam JUMP_STATE = 4'b0100;
  localparam MRET_STATE = 4'b0001;

  localparam NON_CMPR_INSTRUCTION_INCREMENT = 4;
  localparam CMPR_INSTRUCTION_INCREMENT = 2;

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) | !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT";


  /////////////////////////////////////////////////////////////////////
  ///////////////////////// GENERAL SEQUENCES /////////////////////////
  /////////////////////////////////////////////////////////////////////


  sequence seq_rvfi_normal_instruction (logic [6:0] func7, logic [2:0] func3, logic [6:0] opcode);

    //Make sure there is no traped instruction
    !rvfi_if.rvfi_trap[0]

    //Make sure the instruction is valid
    && rvfi_if.rvfi_valid

    //Explicitly state what instruction we work with by using the opcode, func3 and func7
    && rvfi_if.rvfi_insn[6:0] == opcode
    && rvfi_if.rvfi_insn[14:12] == func3
    && rvfi_if.rvfi_insn[31:25] == func7;
  endsequence

  sequence seq_rvfi_normal_compressed_instruction (logic [15:13] opcode_bit_15_to_13, logic [1:0] opcode_bit_1_to_0);
    //Make sure there is no traped instruction
    !rvfi_if.rvfi_trap[0]

    //Make sure the instruction is valid
    && rvfi_if.rvfi_valid

    //Explicitly state what instruction we work with
    && rvfi_if.rvfi_insn[15:13] == opcode_bit_15_to_13
    && rvfi_if.rvfi_insn[1:0] == opcode_bit_1_to_0;
  endsequence

  property p_xsecure_setting_default_off(logic xsecure_setting);

    //Make sure that when exiting reset mode the xsecure setting is off
    $rose(rst_ni)
    |->
    !xsecure_setting;
  endproperty

  property p_xsecure_setting_default_on(logic xsecure_setting);

    //Make sure that when exiting reset mode the xsecure setting is off
    $rose(rst_ni)
    |->
    xsecure_setting;
  endproperty


  ///////////////////////////////////////////////////////////////////
  ///////////////////////// SECURITY ALERTS /////////////////////////
  ///////////////////////////////////////////////////////////////////


  ////////// SECURITY ALERTS MINOR //////////
  a_xsecure_security_alert_minor_1: assert property (

    //Make sure we detect a lockup error
    xsecure_if.core_cs_registers_xsecure_lfsr_lockup != NO_LOCKUP_ERRORS

    //Make sure alert minor is set
    |=>
    xsecure_if.core_alert_minor_o

  ) else `uvm_error(info_tag, "Lookup errors do not set minor alert.\n");


  a_xsecure_security_alert_minor_2_to_6: assert property (

    //Make sure we look at a valid instruction
    rvfi_if.rvfi_valid

    //Make sure the instruction is associated with a trap and an exception error
    && rvfi_if.rvfi_trap[0]
    && rvfi_if.rvfi_trap[1]

    //Instruction access fault
    && (rvfi_if.rvfi_trap[8:3] == ERROR_CODE_INSTRUCTION_ACCESS_FAULT

    //Illegal instruction fault
    || rvfi_if.rvfi_trap[8:3] == ERROR_CODE_ILLEGAL_INSTRUCTION_FAULT

    //Load access fault
    || rvfi_if.rvfi_trap[8:3] == ERROR_CODE_LOAD_ACCESS_FAULT

    //Store/AMO access fault
    || rvfi_if.rvfi_trap[8:3] == ERROR_CODE_STORE_AMO_ACCESS_FAULT

    //Instruction bus fault
    || rvfi_if.rvfi_trap[8:3] == ERROR_CODE_INSTRUCTION_BUS_FAULT)

    //TODO: The error is handled in WB stage and notify the alert minor signal in the next stage (the current/rvfi stage)
    |->
    xsecure_if.core_alert_minor_o

  ) else `uvm_error(info_tag, "Exception errors do not set minor alert.\n");


  ///////////////////////////////////////////////////////////////////////////
  ///////////////////////// DATA iNDEPENDENT TIMING /////////////////////////
  ///////////////////////////////////////////////////////////////////////////


  ////////// DATA INDEPENDENT TIMING IS CONFIGURABLE //////////

  // Check that we have data independent timing when configured to be on:
  // a_xsecure_dataindtiming_default_off
  // a_xsecure_core_div_rem_timing_clk

  // Check that we do not have data independent timing when configured to be off:

  c_xsecure_branch_timing_off: cover property (

    //Make sure a branch instruction is executed (rvfi stage):
    (seq_rvfi_normal_instruction(FUNC7_BRANCH_INSTRUCTION, FUNC3_BRANCH_INSTRUCTION, cv32e40s_pkg::OPCODE_BRANCH)
    or seq_rvfi_normal_compressed_instruction(OPCODE_BIT_15_TO_13_COMPR_BRANCH, OPCODE_BIT_1_TO_0_COMPR_BRANCH))

    //Make sure the data independent timing was off when executing the branch (ex stage):
    and $past(!xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)

    //Make sure it is possible that the branch instruction is directly followed by another instruction (as the branch is not taken)
    ##1 rvfi_if.rvfi_valid
  );


  c_xsecure_core_div_rem_timing: cover property (

    //Make sure we detect an DIV or REM instruction in rvfi
    seq_rvfi_normal_instruction(FUNC7_DIV_REM_INSTRUCTION, FUNC3_DIV_REM_INSTRUCTION, cv32e40s_pkg::OPCODE_OP)

    //Make sure data independent timing was off when the DIV/REM instruction was in EX stage
    and $past(!xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)

    //Make sure that it is possible that the instruction was directly followed by another instruction
    && $past(rvfi_if.rvfi_valid)

  );


  ////////// DATA INDEPENDENT TIMING DEFAULT OFF //////////

  a_xsecure_dataindtiming_default_on: assert property (
	  p_xsecure_setting_default_on(
	  xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming)
  ) else `uvm_error(info_tag, "Data independent timing is not on when exiting reset.\n");


  ////////// BRANCH TIMING //////////

  a_xsecure_branch_timing: assert property (

    //Make sure a branch instruction is executed:
    (seq_rvfi_normal_instruction(FUNC7_BRANCH_INSTRUCTION, FUNC3_BRANCH_INSTRUCTION, cv32e40s_pkg::OPCODE_BRANCH)
    or seq_rvfi_normal_compressed_instruction(OPCODE_BIT_15_TO_13_COMPR_BRANCH, OPCODE_BIT_1_TO_0_COMPR_BRANCH))

    //Make sure the data independent timing was on when executing the branch (ex stage):
    and $past(xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)

    //Make sure that the instruction before the branch instruction was not a load or a store (rvfi stage):
    //We use past 2 because branching needs two cycles to complete execution due to PC harning safety.
    && $past(!(|rvfi_if.rvfi_mem_rmask),2)
    && $past(!(|rvfi_if.rvfi_mem_wmask),2)

    //Make sure there are at least one instruction stall after every branch, because a branch is allways taken.
    //We would expect 2 instruction stalls, but since the branch instruction is recalculated in id stage we have only one stall, instead of two.
    |=>
    !rvfi_if.rvfi_valid
  ) else `uvm_error(info_tag, "Branch timing does not stall the pipeline (given no load/store instruction before the branch instruction).\n");


////////// DIV/REM TIMING //////////

  sequence seq_rvfi_not_valid_for_34_cycles;

    //Make sure rvfi_valid is off for 34 cycles
    !rvfi_if.rvfi_valid[*34] ##1 1;

  endsequence

  sequence seq_set_rvfi_valid_once_as_memory_instruction_during_the_past_34_cycles;

    //Make sure a memory instruction is retired in a 34 cycle interval.

    //Make sure rvfi_valid is low an unknown number of cycles
    !rvfi_if.rvfi_valid[*0:33]

    //Make sure that once the rvfi_valid is high we retire a memory instruction
    ##1 (rvfi_if.rvfi_valid
    && (rvfi_if.rvfi_mem_rmask || rvfi_if.rvfi_mem_wmask))

    //Make sure rvfi_valid is off in an unknown number of cycles
    ##1 !rvfi_if.rvfi_valid[*0:33]

    //Make sure the sequence only look previouse clock cycles when triggered
    ##1 1;

  endsequence


  a_xsecure_core_div_rem_timing: assert property (

    //Make sure we detect an DIV or REM instruction in rvfi
    seq_rvfi_normal_instruction(FUNC7_DIV_REM_INSTRUCTION, FUNC3_DIV_REM_INSTRUCTION, cv32e40s_pkg::OPCODE_OP)

    //Make sure data independent timing was on when the DIV/REM instruction was in EX stage
    //(Checks only the last cycle the branch instruction is in EX stage because if data independent timing is on, in the last cycle DIV/REM is in EX, it must also been on in he previouse cycles)
    and $past(xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)
    |->
    //Make sure that there are at least 34 cycles from the last retired instruction
    seq_rvfi_not_valid_for_34_cycles.triggered

    //or the retired instructions are loads or stores
    or seq_set_rvfi_valid_once_as_memory_instruction_during_the_past_34_cycles.triggered

  ) else `uvm_error(info_tag, "DIV/REM operations do not use 35 cycles to execute\n");


  /////////////////////////////////////////////////////////////////////
  ///////////////////////// DUMMY INSTRUCTION /////////////////////////
  /////////////////////////////////////////////////////////////////////


  ////////// DUMMY INSTRUCTIONS ARE CONFIGURABLE /////////

  // Check that we generate dummy instructions when dummy bit is on:
  // a_xsecure_dummy_instruction_frequency

  // Check that we do not generate dummy instructions when the dummy bit is off:

  a_xsecure_dummy_instruction_not_generated_when_dummybit_is_off: assert property(

    //Make sure the dummy instruction settings is off
    !xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy

    //Make sure we look at an valid instruction
    && xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i

    //Make sure we dont generate dummy instructions
    |=>
    !xsecure_if.core_if_id_pipe_instr_meta_dummy

  ) else `uvm_error(info_tag, "We generate dummy instructions even though the dummy setting is off.\n");


  ////////// DUMMY INSTRUCTION INSTERTED IN IF /////////

  a_xsecure_dummy_instruction_in_if: assert property(

    //Make sure we detect an new instruction in the id ex pipe
    $past(xsecure_if.core_id_stage_id_valid_o)
    && $past(xsecure_if.core_id_stage_ex_ready_i)

    //Make sure the dummy instruction settings is on when fetching the instruction
    && xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy

    //Make sure the detected instruction is an dummy instruction
    && xsecure_if.core_id_ex_pipe_instr_meta_dummy

    //Make sure the dummy instruction originate from if stage
    |->
    $past(xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy)
    && $past(xsecure_if.core_if_id_pipe_instr_meta_dummy)
  ) else `uvm_error(info_tag, "Dummy instructions are not inserted in if stage.\n");


  ////////// DUMMY INSTRUCTION BLTU JUMPS TO NEXT NON-DUMMY INSTRUCTION //////////

  a_xsecure_dummy_instruction_bltu_jumping: assert property(

    //Make sure we detect an new instruction in the id ex pipe
    $past(xsecure_if.core_id_stage_id_valid_o)
    && $past(xsecure_if.core_id_stage_ex_ready_i)

    //Make sure the detected instruction is an dummy instruction
    && xsecure_if.core_id_ex_pipe_instr_meta_dummy

    //Make sure we have BLTU dummy instruction
    && xsecure_if.core_id_ex_pipe_instr_bus_resp_rdata[6:0] == cv32e40s_pkg::OPCODE_BRANCH
    && xsecure_if.core_id_ex_pipe_instr_bus_resp_rdata[14:12] == FUNC3_BLTU_INSTRUCTION

    //Make sure we jump to next instruction
    //(PC change to next instruction before inserting an dummy instruction, the jump should therefore be 0)
    |->
    xsecure_if.core_id_ex_pipe_instr_bus_resp_rdata[31:25] == '0
    && xsecure_if.core_id_ex_pipe_instr_bus_resp_rdata[11:7] == '0
  ) else `uvm_error(info_tag, "Dummy branch instructions do not jump to the next non-dummy instructions.\n");


  ////////// DUMMY INSTRUCTION OPERAND SOURCES //////////

  a_xsecure_dummy_instruction_operands_from_LFSR1_and_LFSR2: assert property (

    //Make sure we detect an new instruction in the if id pipe
    $past(xsecure_if.core_if_stage_if_valid_o)
    && $past(xsecure_if.core_if_stage_id_ready_i)

    //Make sure the dummy instruction settings is on when fetching the instruction
    && xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy

    //Make sure the detected instruction is an dummy instruction
    && xsecure_if.core_if_id_pipe_instr_meta_dummy

    |->
    //Check that the sr1 part of the instruction originates from the LFSR1 register
    xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[19:15] == $past(xsecure_if.core_if_stage_gen_dummy_instr_dummy_instr_lfsr_rs1)

    //Check that the sr2 part of the instruction originates from the LFSR2 register
    && xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[24:20] == $past(xsecure_if.core_if_stage_gen_dummy_instr_dummy_instr_lfsr_rs2)

  ) else `uvm_error(info_tag, "Dummy instructions do not fetch data from LFSR1 and LFSR2.\n");


  ////////// DUMMY INSTRUCTION DESTINATION //////////

  a_xsecure_dummy_instruction_destination_is_x0: assert property (

    //Make sure we detect an new instruction in the if id pipe
    $past(xsecure_if.core_if_stage_if_valid_o)
    && $past(xsecure_if.core_if_stage_id_ready_i)

    //Make sure the dummy instruction settings is on when fetching the instruction
    && xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy

    //Make sure the detected instruction is an dummy instruction
    && xsecure_if.core_if_id_pipe_instr_meta_dummy

    |->
    //Check that the destination register is x0
    xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[11:7] == REGISTER_x0

  ) else `uvm_error(info_tag, "The results of the dummy instructions are not stored in the x0 register.\n");


  ////////// DUMMY INSTRUCTION UPDATES MCYCLE //////////

  a_xsecure_dummy_instruction_updates_mcycle: assert property (
    //Make sure the gated clock is active
    @(posedge xsecure_if.core_clk)

    //Make sure that mcycle is on (not inhibit)
    !xsecure_if.core_cs_registers_mcountinhibit_q_mcycle_inhibit

    //Make sure we do not write to the mcycle csr register
    and !($past(xsecure_if.core_cs_registers_csr_en_gated)
    && ($past(xsecure_if.core_cs_registers_csr_waddr == cv32e40s_pkg::CSR_MCYCLE)) || $past(xsecure_if.core_cs_registers_csr_waddr == cv32e40s_pkg::CSR_MCYCLEH))

    |->
    //Make sure the mcycle counts every cycle (including the clock cycles dummy instruction occurs)
    xsecure_if.core_cs_registers_mhpmcounter_mcycle == ($past(xsecure_if.core_cs_registers_mhpmcounter_mcycle) + 1)

    //But make sure it resets in case of overflow
    or xsecure_if.core_cs_registers_mhpmcounter_mcycle == '0 && $past(xsecure_if.core_cs_registers_mhpmcounter_mcycle) == REGISTER_MHPMCOUNTER_MCYCLE_FULL

    //And allow the first mcycle count to not increment
    or xsecure_if.core_cs_registers_mhpmcounter_mcycle == $past(xsecure_if.core_cs_registers_mhpmcounter_mcycle) && $past(xsecure_if.core_cs_registers_mcountinhibit_q_mcycle_inhibit)

  ) else `uvm_error(info_tag, "Dummy instructions do not update the mcycle register.\n");


  ////////// DUMMY INSTRUCTION DO NOT UPDATE MINSTRET //////////

  a_xsecure_dummy_instruction_do_not_update_minstret: assert property (
    //Make sure the gated clock is active
    @(posedge xsecure_if.core_clk)

    //Make sure that minstret is on (not inhibit)
    !xsecure_if.core_cs_registers_mcountinhibit_q_minstret_inhibit

    //Make sure we have an dummy instruction
    && xsecure_if.core_wb_stage_ex_wb_pipe_instr_meta_dummy

    //Make sure the dummy instruction is ready to retire
    && xsecure_if.core_wb_stage_wb_valid_o

    //Make sure the minstret counter ignore the retired dummy instruction
    |=>
    xsecure_if.core_cs_registers_mhpmcounter_minstret == $past(xsecure_if.core_cs_registers_mhpmcounter_minstret)

  ) else `uvm_error(info_tag, "Dummy instructions updates the minstret register.\n");


  ////////// DUMMY INSTRUCTION FREQUENCY //////////


  sequence seq_dummy_instruction_within_normal_valid_instructions (num_normal_valid_instructions);
    //Make sure we detect a dummy instruction
    xsecure_if.core_if_stage_instr_meta_n_dummy
    && xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i

    //Make sure we detect 0 to x number of normal valid instruction in the if stage
    ##1 (xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i)[->0:(num_normal_valid_instructions)];
  endsequence


  property p_xsecure_dummy_instruction_frequency(num_normal_valid_instructions_per_dummy_instruction, logic [3:0] rnddummyfreq_value);

    //Make sure the dummy setting is on
    (xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy

    //Make sure the frequency of dummy instructions is set to correct value
    && xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummyfreq == rnddummyfreq_value

    //Make sure the controller is not in debug mode
    && !xsecure_if.core_controller_controller_fsm_debug_mode_q

    && !xsecure_if.core_i_if_stage_i_instr_hint

    //Make sure the dummy instructions are allways enabled
    && xsecure_if.core_if_stage_gen_dummy_instr_dummy_instr_dummy_en
    )
    //Make sure we detect new instructions in the if id pipe
    throughout (xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i)[->(num_normal_valid_instructions_per_dummy_instruction)+1]

    //Make sure that we detect one valid dummy instruction inbetween the number of normal valid instructions
    |->
    seq_dummy_instruction_within_normal_valid_instructions(num_normal_valid_instructions_per_dummy_instruction).triggered;

  endproperty


  //FREQ = 4
  a_xsecure_dummy_instruction_frequency_4: assert property (
	  p_xsecure_dummy_instruction_frequency(
      4,
      FREQ_SETTING_4)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-4.\n");

  //FREQ = 8
  a_xsecure_dummy_instruction_frequency_8: assert property (
	  p_xsecure_dummy_instruction_frequency(
      8,
      FREQ_SETTING_8)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-8 or higher.\n");

  //FREQ = 16
  a_xsecure_dummy_instruction_frequency_16: assert property (
	  p_xsecure_dummy_instruction_frequency(
      16,
      FREQ_SETTING_16)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-16 or higher.\n");

  //FREQ = 32
  a_xsecure_dummy_instruction_frequency_32: assert property (
	  p_xsecure_dummy_instruction_frequency(
      32,
      FREQ_SETTING_32)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-32 or higher.\n");

  //FREQ = 64
  a_xsecure_dummy_instruction_frequency_64: assert property (
	  p_xsecure_dummy_instruction_frequency(
      64,
      FREQ_SETTING_64)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-64 or higher.\n");


  ////////// DUMMY INSTRUCTION RESET SEED AT LOCKUP ERRORS //////////

  property p_xsecure_dummy_instruction_LFSRx_lockup_reset(integer x, logic core_cs_registers_xsecure_lfsrx_seed_we, logic [31:0] core_xsecure_ctrl_lfsrx, logic [31:0] core_LFSRx_CFG_default_seed);

    //Make sure the dummy setting is on
    xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy

    //Make sure there is a lockup error on register x
    && xsecure_if.core_cs_registers_xsecure_lfsr_lockup[x] == LOCKUP_ERROR

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
  ) else `uvm_error(info_tag, "LFSR0 does not reset to default value when when there is a lookup error (given that we do not write to the register).\n");

  //LFSR1
  a_xsecure_dummy_instruction_LFSR1_lockup_reset: assert property (
	  p_xsecure_dummy_instruction_LFSRx_lockup_reset(
      1,
      xsecure_if.core_cs_registers_xsecure_lfsr1_seed_we,
	    xsecure_if.core_xsecure_ctrl_lfsr1,
      xsecure_if.core_LFSR1_CFG_default_seed)
  ) else `uvm_error(info_tag, "LFSR1 does not reset to default value when when there is a lookup error (given that we do not write to the register).\n");

  //LFSR2
  a_xsecure_dummy_instruction_LFSR2_lockup_reset: assert property (
	  p_xsecure_dummy_instruction_LFSRx_lockup_reset(
      2,
      xsecure_if.core_cs_registers_xsecure_lfsr2_seed_we,
	    xsecure_if.core_xsecure_ctrl_lfsr2,
      xsecure_if.core_LFSR2_CFG_default_seed)
  ) else `uvm_error(info_tag, "LFSR2 does not reset to default value when when there is a lookup error (given that we do not write to the register).\n");


  /////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////// REDUCTION OF PROFILING INFRASTRUCTURE /////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////////


  a_xsecure_reduction_of_profiling_infrastructure_mhpmevent_31_to_3_are_zero: assert property (

    //Make sure the mhpmevent 3 to 31 are hardwired to zero
    |xsecure_if.core_cs_registers_mhpmevent_31_to_3 == 1'b0

  ) else `uvm_error(info_tag, "The mhpmevent registers 31 to 3 is not hardwired to zero.\n");


  a_xsecure_reduction_of_profiling_infrastructure_mhpmcounter_31_to_3_are_zero: assert property (

    //Make sure the mhpmcounter 3 to 31 are hardwired to zero
    //(we include mhpmcounterh in the mhpmcounter signal)
    |xsecure_if.core_cs_registers_mhpmcounter_31_to_3 == 1'b0

  ) else `uvm_error(info_tag, "The mhpmcounter registers 31 to 3 is not hardwired to zero.\n");


  ////////////////////////////////////////////////////////////////
  ///////////////////////// CSR HARDENING /////////////////////////
  ////////////////////////////////////////////////////////////////


  ////////// SOME CSR REGISTER ARE SHADOWED //////////

  /****************************************

  The following 4 assertions make sure that the CSR registers that are shadowed, are shadowed at all times:
  The shadow registers are the compliments of the CSR registers

  ****************************************/


  a_xsecure_hardened_CSRs_no_missmatch_static_registers: assert property (
    //Make sure the following csr registers are shadowed at all times:

    //JVT
    xsecure_if.core_cs_registers_jvt_csr_gen_hardened_shadow_q == ~(xsecure_if.core_i_cs_registers_i_jvt_csr_i_rdata_q & cv32e40s_pkg::CSR_JVT_MASK)

    //MSTATUS
    and xsecure_if.core_cs_registers_mstatus_csr_gen_hardened_shadow_q == ~(xsecure_if.core_i_cs_registers_i_mstatus_csr_i_rdata_q & cv32e40s_pkg::CSR_MSTATUS_MASK)

    //CPUCTRL
    and xsecure_if.core_cs_registers_xsecure_cpuctrl_csr_gen_hardened_shadow_q == ~(xsecure_if.core_i_cs_registers_i_xsecure_cpuctrl_csr_i_rdata_q & cv32e40s_pkg::CSR_CPUCTRL_MASK)

    //DCSR
    and xsecure_if.core_cs_registers_dcsr_csr_gen_hardened_shadow_q == ~(xsecure_if.core_i_cs_registers_i_dcsr_csr_i_rdata_q & cv32e40s_pkg::CSR_DCSR_MASK)

    //MEPC
    and xsecure_if.core_cs_registers_mepc_csr_gen_hardened_shadow_q == ~(xsecure_if.core_i_cs_registers_i_mepc_csr_i_rdata_q & cv32e40s_pkg::CSR_MEPC_MASK)

    //MSCRATCH
    and xsecure_if.core_cs_registers_mscratch_csr_gen_hardened_shadow_q == ~(xsecure_if.core_i_cs_registers_i_mscratch_csr_i_rdata_q & cv32e40s_pkg::CSR_MSCRATCH_MASK)

  ) else `uvm_error(info_tag, "One or several of the CSR registers jvt, mstatus, cpuctrl, dcsr, mepc, mscratch are not shadowed.\n");

  generate
    if(PMP_NUM_REGIONS > 0) begin
      a_xsecure_hardened_CSRs_no_missmatch_pmp_register: assert property (
      //Make sure the mseccfg csr register is shadowed at all times (given that we use pmp regions)

      //MSECCFG
      xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_pmp_mseccfg_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_pmp_mseccfg_csr_i_rdata_q & cv32e40s_pkg::CSR_MSECCFG_MASK)

      ) else `uvm_error(info_tag, "The CSR register mseccfg is not shadowed.\n");

    end
  endgenerate

  generate for (genvar n = 0; n < PMP_NUM_REGIONS; n++) begin

    a_xsecure_hardened_CSRs_no_missmatch_pmp_region_registers: assert property (
      //Make sure the exsisting pmp csr registers are shadowed at all times

      //PMPNCFG
      xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_gen_pmp_csr_n_pmp_region_pmpncfg_csr_i_gen_hardened_shadow_q[n] == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_csr_pmp_gen_pmp_csr_n_pmp_region_pmpncfg_csr_i_rdata_q[n] & cv32e40s_pkg::CSR_PMPNCFG_MASK)

      //PMPADDR
      and xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_gen_pmp_csr_n_pmp_region_pmp_addr_csr_gen_hardened_shadow_q[n] == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_csr_pmp_gen_pmp_csr_n_pmp_region_pmp_addr_csr_i_rdata_q[n] & cv32e40s_pkg::CSR_PMPADDR_MASK)

    ) else `uvm_error(info_tag, $sformatf("One or several of the CSR registers pmp%0dcfg or pmpaddr[%0d] are not shadowed.\n", n, n));

  end endgenerate

  generate
    if(SMCLIC) begin
      a_xsecure_hardened_CSRs_no_missmatch_smclic_registers: assert property (
        //Make sure the smclic csr registers are shadowed at all times if smclic is enabled

        //MTVT
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mtvt_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mtvt_csr_i_rdata_q & cv32e40s_pkg::CSR_MTVT_MASK)

        //MTVEC
        and xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mtvec_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mtvec_csr_i_rdata_q & cv32e40s_pkg::CSR_MTVEC_CLIC_MASK)

        //MINTSTATUS
        and xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mintstatus_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mintstatus_csr_i_rdata_q & cv32e40s_pkg::CSR_MINTSTATUS_MASK)

        //MINTTHRESH
        and xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mintthresh_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mintthresh_csr_i_rdata_q & CSR_MINTTHRESH_MASK)

      ) else `uvm_error(info_tag, "One or several of the CSR registers mtvt, mtvec, mintthresh are not shadowed.\n");

    end else begin

      a_xsecure_hardened_CSRs_no_missmatch_basic_mode_registers: assert property (
        //Make sure the csr registers used when smclic is disabled are shadowed at all times

        //MTVEC
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mtvec_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mtvec_csr_rdata_q & cv32e40s_pkg::CSR_MTVEC_BASIC_MASK)

        //MIE
        and xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mie_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mie_csr_rdata_q & cv32e40s_pkg::IRQ_MASK)

      ) else `uvm_error(info_tag, "The CSR registers mtvec or mie are not shadowed.\n");

    end
  endgenerate


  ////////// SET ALERT MAJOR IF A CSR REGISTER IS NOT SHADOWED //////////

  property p_xsecure_hardned_csr_missmatch_sets_alert_major(csr, shadow, MASK);

    //Make sure we only set major alert if we are in operating mode (use the gated clock)
    @(posedge xsecure_if.core_clk)

    //csr & mask: make sure the bits we are not interested in are set to 0s, which is determined by the mask
    //shadow | ~MASK: make sure we set the bits we are not interested in to 1s, which is also deterimend by the mask
    //~(shadow | ~MASK) != (csr & MASK): make sure that all the shadow register bits we are interestead in are compliments of each other, and that the bits that we are not interestead in are turned into compliments of eachother
    ~(shadow | ~MASK) != (csr & MASK)

    //Make sure alert major is set if there is a missmatch of the CSR and shadow register
    |=>
    xsecure_if.core_alert_major_o;

  endproperty


  /****************************************
  The following assertions checks if a missmatch in specific shadow and cs registers results in a major alert.

  Method for inserting errors:
  - Add cutpoints

  ****************************************/
  //JVT:
  a_xsecure_hardened_CSRs_missmatch_jvt: assert property (
    p_xsecure_hardned_csr_missmatch_sets_alert_major(
      xsecure_if.core_i_cs_registers_i_jvt_csr_i_rdata_q,
      xsecure_if.core_cs_registers_jvt_csr_gen_hardened_shadow_q,
      cv32e40s_pkg::CSR_JVT_MASK)
  ) else `uvm_error(info_tag, "jvt cs and shadow register missmatch does not result in major alert.\n");

  //MSTATUS:
  a_xsecure_hardened_CSRs_missmatch_mstatus: assert property (
    p_xsecure_hardned_csr_missmatch_sets_alert_major(
      xsecure_if.core_i_cs_registers_i_mstatus_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mstatus_csr_gen_hardened_shadow_q,
      cv32e40s_pkg::CSR_MSTATUS_MASK)
  ) else `uvm_error(info_tag, "mstatus cs and shadow register missmatch does not result in major alert.\n");

  //CPUCTRL:
  a_xsecure_hardened_CSRs_missmatch_cpuctrl: assert property (
    p_xsecure_hardned_csr_missmatch_sets_alert_major(
      xsecure_if.core_i_cs_registers_i_xsecure_cpuctrl_csr_i_rdata_q,
      xsecure_if.core_cs_registers_xsecure_cpuctrl_csr_gen_hardened_shadow_q,
      cv32e40s_pkg::CSR_CPUCTRL_MASK)
  ) else `uvm_error(info_tag, "cpuctrl cs and shadow register missmatch does not result in major alert.\n");

  //DCSR:
  a_xsecure_hardened_CSRs_missmatch_dcsr: assert property (
    p_xsecure_hardned_csr_missmatch_sets_alert_major(
      xsecure_if.core_i_cs_registers_i_dcsr_csr_i_rdata_q,
      xsecure_if.core_cs_registers_dcsr_csr_gen_hardened_shadow_q,
      cv32e40s_pkg::CSR_DCSR_MASK)
  ) else `uvm_error(info_tag, "dcsr cs and shadow register missmatch does not result in major alert.\n");

  //MEPC:
  a_xsecure_hardened_CSRs_missmatch_mepc: assert property (
    p_xsecure_hardned_csr_missmatch_sets_alert_major(
      xsecure_if.core_i_cs_registers_i_mepc_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mepc_csr_gen_hardened_shadow_q,
      cv32e40s_pkg::CSR_MEPC_MASK)
  ) else `uvm_error(info_tag, "mepc cs and shadow register missmatch does not result in major alert.\n");

  //MSCRATCH:
  a_xsecure_hardened_CSRs_missmatch_mscratch: assert property (
    p_xsecure_hardned_csr_missmatch_sets_alert_major(
      xsecure_if.core_i_cs_registers_i_mscratch_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mscratch_csr_gen_hardened_shadow_q,
      cv32e40s_pkg::CSR_MSCRATCH_MASK)
  ) else `uvm_error(info_tag, "mscratch cs and shadow register missmatch does not result in major alert.\n");

  generate
    if(PMP_NUM_REGIONS > 0) begin

      //MSECCFG:
      a_xsecure_hardened_CSRs_missmatch_mseccfg: assert property (
        p_xsecure_hardned_csr_missmatch_sets_alert_major(
          xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_pmp_mseccfg_csr_i_rdata_q,
          xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_pmp_mseccfg_csr_gen_hardened_shadow_q,
          cv32e40s_pkg::CSR_MSECCFG_MASK)
      ) else `uvm_error(info_tag, "mseccfg cs and shadow register missmatch does not result in major alert.\n");

    end
  endgenerate


  generate for (genvar n = 0; n < PMP_NUM_REGIONS; n++) begin
    //PMPNCFG:
    a_xsecure_hardened_CSRs_missmatch_pmpncfg: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_csr_pmp_gen_pmp_csr_n_pmp_region_pmpncfg_csr_i_rdata_q[n],
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_gen_pmp_csr_n_pmp_region_pmpncfg_csr_i_gen_hardened_shadow_q[n],
        cv32e40s_pkg::CSR_PMPNCFG_MASK)
    ) else `uvm_error(info_tag, $sformatf("pmp%0dcfg cs and shadow register missmatch does not result in major alert.\n", n));

    //PMPADDR:
    a_xsecure_hardened_CSRs_missmatch_pmpaddr: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_csr_pmp_gen_pmp_csr_n_pmp_region_pmp_addr_csr_i_rdata_q[n],
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_gen_pmp_csr_n_pmp_region_pmp_addr_csr_gen_hardened_shadow_q[n],
        cv32e40s_pkg::CSR_PMPADDR_MASK)
    ) else `uvm_error(info_tag, $sformatf("pmpaddr[%0d] cs and shadow register missmatch does not result in major alert.\n",n));

  end endgenerate


  if(SMCLIC) begin
    //MTVT:
    a_xsecure_hardened_CSRs_missmatch_mtvt: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        //Make sure it is possible to vary the lenght of the mtvt_addr signal
        xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mtvt_csr_i_rdata_q,
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mtvt_csr_gen_hardened_shadow_q,
        cv32e40s_pkg::CSR_MTVT_MASK)
    ) else `uvm_error(info_tag, "mtvt cs and shadow register missmatch does not result in major alert.\n");

    //MTVEC:
    a_xsecure_hardened_CSRs_missmatch_mtvec: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mtvec_csr_i_rdata_q,
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mtvec_csr_gen_hardened_shadow_q,
        cv32e40s_pkg::CSR_MTVEC_CLIC_MASK)
    ) else `uvm_error(info_tag, "mtvec cs and shadow register missmatch does not result in major alert.\n");

    //MINTSTATUS:
    a_xsecure_hardened_CSRs_missmatch_mintstatus: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mintstatus_csr_i_rdata_q,
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mintstatus_csr_gen_hardened_shadow_q,
        cv32e40s_pkg::CSR_MINTSTATUS_MASK)
    ) else `uvm_error(info_tag, "mintstatus cs and shadow register missmatch does not result in major alert.\n");

    //MINTTHRESH:
    a_xsecure_hardened_CSRs_missmatch_mintthresh: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mintthresh_csr_i_rdata_q,
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mintthresh_csr_gen_hardened_shadow_q,
        CSR_MINTTHRESH_MASK)
    ) else `uvm_error(info_tag, "mintthresh cs and shadow register missmatch does not result in major alert.\n");

  end else begin

    //MTVEC:
    a_xsecure_hardened_CSRs_missmatch_mtvec: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mtvec_csr_rdata_q,
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mtvec_csr_gen_hardened_shadow_q,
        cv32e40s_pkg::CSR_MTVEC_BASIC_MASK)
    ) else `uvm_error(info_tag, "mtvec cs and shadow register missmatch does not result in major alert.\n");

    //MIE:
    a_xsecure_hardened_CSRs_missmatch_mie: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mie_csr_rdata_q,
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mie_csr_gen_hardened_shadow_q,
        cv32e40s_pkg::IRQ_MASK)
    ) else `uvm_error(info_tag, "mie cs and shadow register missmatch does not result in major alert.\n");

  end

  /////////////////////////////////////////////////////////////////////
  ///////////////////////// REGISTER FILE ECC /////////////////////////
  /////////////////////////////////////////////////////////////////////

  ////////// GENERAL PURPOSE REGISTERS ARE ZERO WHEN EXITING RESET //////////

  //Check that the gpr is reset to 0 when exiting reset stage:
  property p_xsecure_gpr_reset(integer register_addr);
    //Make sure we are going out of reset
    $rose(rst_ni)

    //Make sure the general purpose register of addres "register_addr" is reset to zero
    |->
    xsecure_if.core_register_file_wrapper_register_file_mem[register_addr][31:0] == 32'h0000_0000

    //Make sure the ecc score of the general purpose register of address "register_addr" is the ecc encoding of the value zero
    && xsecure_if.core_register_file_wrapper_register_file_mem[register_addr][37:32] == 6'h2a;

  endproperty


  //Use RVFI to check that rs1 has value 0 when exiting reset stage:
  property p_xsecure_gpr_reset_rvfi_rs1(integer register_addr);

    //Make sure we checkout the first instruction after reset stage
    $rose(rst_ni) ##0 rvfi_if.rvfi_valid[->1]

    //Make sure the instruction reads the rs1 value
    ##0 rvfi_if.rvfi_rs1_addr == register_addr

    //Make sure the rs1 value is 0
    |->
    rvfi_if.rvfi_rs1_rdata == 32'h0000_0000;

  endproperty


//Use RVFI to check that rs2 has value 0 when exiting reset stage:
  property p_xsecure_gpr_reset_rvfi_rs2(integer register_addr);

    //Make sure we checkout the first instruction after reset stage
    $rose(rst_ni) ##0 rvfi_if.rvfi_valid[->1]

    //Make sure the instruction reads the rs1 value
    ##0 rvfi_if.rvfi_rs2_addr == register_addr

    //Make sure the rs2 value is 0
    |->
    rvfi_if.rvfi_rs2_rdata == 32'h0000_0000;

  endproperty


  //Make reset assertions for each gpr:
  generate for (genvar gpr_addr = 0; gpr_addr < 32; gpr_addr++) begin

    a_xsecure_register_file_ecc_gpr_reset_value: assert property (
      p_xsecure_gpr_reset(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("General purpose register %0d is not set to 0 when exiting reset stage.\n", gpr_addr));

    a_xsecure_register_file_ecc_gpr_reset_value_rvfi_rs1: assert property (
      p_xsecure_gpr_reset_rvfi_rs1(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("General purpose register %0d is not set to 0 when exiting reset stage, because rs2 is not 0.\n", gpr_addr));

    a_xsecure_register_file_ecc_gpr_reset_value_rvfi_rs2: assert property (
      p_xsecure_gpr_reset_rvfi_rs2(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("General purpose register %0d is not set to 0 when exiting reset stage, because rs2 is not 0.\n", gpr_addr));

  end endgenerate


  ////////// ECC DECODING MISSMATCH ON EVERY READ SETS MAJOR ALERT //////////

  /****************************************
  Support logic:

  The support logic creates a local gpr memory
  In this local gpr memory we insert data in the same manner as for the actuall gpr memory
  We detect bit flip in the gp registers by comparing the gpr with the local memory


  Method for inserting errors:
  - Add cutpoints

  ****************************************/

  //Local memory for the support logic
  logic [31:0][31:0] gpr_memory_region_shadow = '0;

  //Make sure the local memory is updated whenever the gpr memory is updated
  always @(posedge clk_i) begin
    if(!rst_ni) begin
      gpr_memory_region_shadow = '0;
    end else if (xsecure_if.core_rf_we_wb && xsecure_if.core_rf_waddr_wb != 5'b00000) begin
      gpr_memory_region_shadow[xsecure_if.core_rf_waddr_wb] = xsecure_if.core_rf_wdata_wb;
    end
  end


  //Make sure the support logic works as excpected when updating the memory
  a_xsecure_register_file_ecc_no_supression_by_comparing_ecc_scores_support_logic: assert property (

    //Make sure we update the gpr memory
    xsecure_if.core_rf_we_wb

    //Make sure the adress is not x0
    && xsecure_if.core_rf_waddr_wb != 5'b00000

    //Make sure the local memory is updated in the same manner as the gpr memory
    |=>
    gpr_memory_region_shadow[$past(xsecure_if.core_rf_waddr_wb)] == $past(xsecure_if.core_rf_wdata_wb)

  ) else `uvm_error(info_tag, "The support logic does not update the local memory in the same manner as the gpr memory.\n");


  //Make sure the support logic works as excpected when exiting reset mode
  a_xsecure_register_file_ecc_no_supression_by_comparing_ecc_scores_support_logic_start_at_zero: assert property (

    //Exit reset mode
    $rose(rst_ni)

    //Check that the local memory is set to 0s
    |->
    gpr_memory_region_shadow == '0

  ) else `uvm_error(info_tag, "The local support memory is not set to 0s when exiting reset.\n");


  property p_xsecure_register_file_ecc_no_supression_reading_rs1(rs1_addr);
    @(posedge xsecure_if.core_clk)

    //Make sure there is a non compressed instructions
    !xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed

    //Specify rs1 adress
    && xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[19:15] == rs1_addr

    //Make sure the gpr memory and the local memory differs in one or two bits
    && ($countbits(xsecure_if.core_register_file_wrapper_register_file_mem[rs1_addr][31:0] ^ gpr_memory_region_shadow[rs1_addr], '1) inside {1,2})

    //Make sure the alert major signal is set
    |=>
    xsecure_if.core_alert_major_o;
  endproperty


  property p_xsecure_register_file_ecc_no_supression_reading_rs2(rs2_addr);
    @(posedge xsecure_if.core_clk)

    //Make sure there is a non compressed instructions
    !xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed

    //Specify rs2 adress
    && xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[24:20] == rs2_addr

    //Make sure the gpr memory and the local memory differs in one or two bits
    && ($countbits(xsecure_if.core_register_file_wrapper_register_file_mem[rs2_addr][31:0] ^ gpr_memory_region_shadow[rs2_addr], '1) inside {1,2})

    //Make sure the alert major signal is set
    |=>
    xsecure_if.core_alert_major_o;
  endproperty


  property p_xsecure_register_file_ecc_no_supression_reading_rs1_cmpr(rs1_addr);
    @(posedge xsecure_if.core_clk)

    //Make sure there is a non compressed instructions
    xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed

    //Specify rs1 adress
    && xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[19:15] == rs1_addr

    //Make sure the gpr memory and the local memory differs in one or two bits
    && ($countbits(xsecure_if.core_register_file_wrapper_register_file_mem[rs1_addr][31:0] ^ gpr_memory_region_shadow[rs1_addr], '1) inside {1,2})

    //Make sure the alert major signal is set
    |=>
    xsecure_if.core_alert_major_o;
  endproperty


  property p_xsecure_register_file_ecc_no_supression_reading_rs2_cmpr(rs2_addr);
    @(posedge xsecure_if.core_clk)

    //Make sure there is a non compressed instructions
    xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed

    //Specify rs2 adress
    && xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[24:20] == rs2_addr

    //Make sure the gpr memory and the local memory differs in one or two bits
    && ($countbits(xsecure_if.core_register_file_wrapper_register_file_mem[rs2_addr][31:0] ^ gpr_memory_region_shadow[rs2_addr], '1) inside {1,2})

    //Make sure the alert major signal is set
    |=>
    xsecure_if.core_alert_major_o;
  endproperty

  generate for (genvar gpr_addr = 1; gpr_addr < 32; gpr_addr++) begin

    a_xsecure_register_file_ecc_no_supression_reading_rs1: assert property (
      p_xsecure_register_file_ecc_no_supression_reading_rs1(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("1 or 2 bit error when reading noncompressed rs1 (address %0d) does not set alert major.\n", gpr_addr));

    a_xsecure_register_file_ecc_no_supression_reading_rs2: assert property (
      p_xsecure_register_file_ecc_no_supression_reading_rs2(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("1 or 2 bit error when reading noncompressed rs2 (address %0d) does not set alert major.\n", gpr_addr));

    a_xsecure_register_file_ecc_no_supression_reading_rs1_cmpr: assert property (
      p_xsecure_register_file_ecc_no_supression_reading_rs1_cmpr(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("1 or 2 bit error when reading compressed rs1 (address %0d) does not set alert major.\n", gpr_addr));

    a_xsecure_register_file_ecc_no_supression_reading_rs2_cmpr: assert property (
      p_xsecure_register_file_ecc_no_supression_reading_rs2_cmpr(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("1 or 2 bit error when reading compressed rs2 (address %0d) does not set alert major.\n", gpr_addr));

  end endgenerate


  ///////////////////////////////////////////////////////////////
  ///////////////////////// HARDENED PC /////////////////////////
  ///////////////////////////////////////////////////////////////

  //Signal determing if the core clock is active or not.
  logic core_clock_cycles;

  always @(posedge clk_i) begin
    if(!rst_ni) begin
      core_clock_cycles <= 0;
    end else begin
      core_clock_cycles <= xsecure_if.clk_en;
    end
  end


  ////////// PC HARDENING SEQUENTIAL INSTRUCTION: NORMAL BEHAVIOUR WHEN THERE ARE NO GLITCHES //////////

  sequence seq_dummy_if_id;

    //Generate a dummy instruction
    xsecure_if.core_if_stage_instr_meta_n_dummy

    //Make sure the PC of ID and IF stage is equal when there is a dummy instruction in the ID stage
    ##1 (xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc)[*1:$];
  endsequence

  sequence seq_pc_set_stable;

    //Set the PC value to a given address
    xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_ctrl_fsm_i_pc_set

    //Make sure the PC in if stage remains the same untill it is forwarded to the id stage (and then either incremented or set of a new valid PC jump)
    //(Uses ##2 because: On the first ##1 the FSM signal has "reached" IF, and on the next one its stability can be checked)
    ##2 $stable(xsecure_if.core_i_if_stage_i_pc_if_o)[*1:$];
  endsequence


  property p_xsecure_pc_hardening_sequential_no_glitch_behaviour(cmpr_instruction_in_id_stage, increment);
    @(posedge xsecure_if.core_clk)

    //Make sure we look at valid cycles
    core_clock_cycles

    //Make sure the PC hardening setting is on
    && xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening

    //Check if it is a compressed instructions
    && cmpr_instruction_in_id_stage

    |->
    //Correct behaviour requires that one of the following behaviours are true:

    //Icremental behaviour
    xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc + increment

    //Initalization after reset
    or xsecure_if.core_i_if_stage_i_pc_if_o == 0 && xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc == 0

    //Insertion of dummy instruction
    or seq_dummy_if_id.triggered

    //PC jumping
    or seq_pc_set_stable.triggered

    //PC jumping
    or $past(xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_ctrl_fsm_i_pc_set);

  endproperty


  a_xsecure_pc_hardening_sequential_no_glitch_behaviour_non_cmpr_instruction: assert property (
    p_xsecure_pc_hardening_sequential_no_glitch_behaviour(!xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed, NON_CMPR_INSTRUCTION_INCREMENT)
  ) else `uvm_error(info_tag, "There is a PC fault in IF stage for a non-compressed instruction.\n");

  a_xsecure_pc_hardening_sequential_no_glitch_behaviour_cmpr_instruction: assert property (
    p_xsecure_pc_hardening_sequential_no_glitch_behaviour(xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed, CMPR_INSTRUCTION_INCREMENT)
  ) else `uvm_error(info_tag, "There is a PC fault in IF stage for a compressed instruction.\n");


  ////////// PC HARDENING ON SEQUENTIAL INSTRUCTION: SET MAJOR ALERT //////////

  sequence seq_xsecure_pc_hardening_sequential_instructions_with_glitch(cmpr_instruction_in_id_stage, increment);

    @(posedge xsecure_if.core_clk)

    //Make sure we look at valid cycles
    core_clock_cycles

    //Make sure the PC hardening setting is on
    && xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening

    //Check if it is a compressed instructions
    && cmpr_instruction_in_id_stage

    //Checkout the non-incremental
    && xsecure_if.core_i_if_stage_i_pc_if_o != xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc + increment

    //Make sure we look at a valid instruction
    && $past(xsecure_if.core_if_stage_if_valid_o)
    && $past(xsecure_if.core_if_stage_id_ready_i)

    //Make sure the non-incremental is not caused by any of the following reasons:

    //Initalization after reset
    and !(xsecure_if.core_i_if_stage_i_pc_if_o == 0 && xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc == 0)

    //Insertion of dummy instruction
    and !(seq_dummy_if_id.triggered)

    //PC jumping
    and !(seq_pc_set_stable.triggered)

    //PC jumping
    and !($past(xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_ctrl_fsm_i_pc_set));

  endsequence


  a_xsecure_pc_hardening_sequential_non_compressed_instruction_sets_alert_major: assert property (

    seq_xsecure_pc_hardening_sequential_instructions_with_glitch(!xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed, NON_CMPR_INSTRUCTION_INCREMENT)

    |=>
    //Make sure the alert major is set
    xsecure_if.core_alert_major_o

  ) else `uvm_error(info_tag, "A PC fault in IF stage, for a non-compressed instruction, does not set major alert when PC hardening is on.\n");


  a_xsecure_pc_hardening_sequential_compressed_instruction_sets_alert_major: assert property (

    seq_xsecure_pc_hardening_sequential_instructions_with_glitch(xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed, CMPR_INSTRUCTION_INCREMENT)

    |=>
    //Make sure the alert major is set
    xsecure_if.core_alert_major_o

  ) else `uvm_error(info_tag, "A PC fault in IF stage, for a compressed instruction, does not set major alert when PC hardening is on.\n");


  ////////// PC HARDENING OFF SEQUENTIAL INSTRUCTION: DONT SET MAJOR ALERT //////////

  //TODO: recheck this assertion when the rtl code related to pc_hadening=0 is implemented

  a_xsecure_pc_hardening_off_non_compressed_sequential_instruction_alert_major: assert property (

    seq_xsecure_pc_hardening_sequential_instructions_with_glitch(!xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed, NON_CMPR_INSTRUCTION_INCREMENT)

    |=>
    //Make sure the alert major is not set
    !xsecure_if.core_alert_major_o

  ) else `uvm_error(info_tag, "A PC fault in IF stage, for a non-compressed instruction, set major alert when PC hardening is off.\n");


  a_xsecure_pc_hardening_off_compressed_sequential_instruction_alert_major: assert property (

    seq_xsecure_pc_hardening_sequential_instructions_with_glitch(xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed, CMPR_INSTRUCTION_INCREMENT)

    |=>
    //Make sure the alert major is not set
    !xsecure_if.core_alert_major_o

  ) else `uvm_error(info_tag, "A PC fault in IF stage, for a compressed instruction, set major alert when PC hardening is off.\n");


  ////////// PC HARDENING ON NON-SEQUENTIAL INSTRUCTION: SET MAJOR ALERT IF GLITCH IN PC TARGET //////////

  sequence seq_pc_hardening_non_sequential_instruction_with_glitch(pc_hardening, fsm_state, calculated_signal);

    //Make sure pc hardening setting is set
    pc_hardening

    //Make sure the fsm is in a given state
    && xsecure_if.core_i_if_stage_i_pc_check_i_ctrl_fsm_i_pc_mux == fsm_state

    //Make sure PC is set
    ##1 xsecure_if.core_i_if_stage_i_pc_check_i_pc_set_q

    //Make sure the calculated signal differs in the hardened cycles
    && calculated_signal != $past(calculated_signal);

  endsequence

  property p_xsecure_hardened_pc_non_sequential_set_major_alert(pc_hardening, fsm_state, calculated_signal);

    seq_pc_hardening_non_sequential_instruction_with_glitch(pc_hardening, fsm_state, calculated_signal)

    |=>
    //Make sure alert major is set
    xsecure_if.core_alert_major_o;

  endproperty

  a_xsecure_pc_hardening_branch_set_alert_major: assert property(
    p_xsecure_hardened_pc_non_sequential_set_major_alert(xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening, BRANCH_STATE, xsecure_if.core_i_ex_stage_i_branch_target_o)
  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed branch instruction does not set alert major.\n");

  a_xsecure_pc_hardening_jump_set_alert_major: assert property(
    p_xsecure_hardened_pc_non_sequential_set_major_alert(xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening, JUMP_STATE, xsecure_if.core_i_jump_target_id)
  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed jump instruction does not set alert major.\n");

  a_xsecure_pc_hardening_mret_set_alert_major: assert property(
    p_xsecure_hardened_pc_non_sequential_set_major_alert(xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening, MRET_STATE, xsecure_if.core_i_cs_registers_i_mepc_o)
  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed mret instruction does not set alert major.\n");


  ////////// PC HARDENING ON NON-SEQUENTIAL INSTRUCTION: SET MAJOR ALERT IF GLITCH IN BRANCH DECISION //////////

  sequence seq_pc_hardening_branch_decision_glitch(pc_hardening);

    //Make sure pc hardening setting is set
    xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening

    //Make sure the fsm is in branching state
    && xsecure_if.core_i_if_stage_i_pc_check_i_ctrl_fsm_i_pc_mux == BRANCH_STATE

    //Make sure the branch decision differs in the hardened cycles
    ##1 xsecure_if.core_i_ex_stage_i_alu_i_cmp_result_o != $past(xsecure_if.core_i_ex_stage_i_alu_i_cmp_result_o)

    //Make sure the branch decision is not automatically set to taken
    && !xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming;

  endsequence


  a_xsecure_pc_hardening_branch_decision_set_alert_major: assert property(

    seq_pc_hardening_branch_decision_glitch(xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening)

    |=>

    //Make sure alert major was/is set
    xsecure_if.core_alert_major_o
    || $past(xsecure_if.core_alert_major_o)

  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed branch decision does not set alert major.\n");


  ////////// PC HARDENING OFF NON-SEQUENTIAL INSTRUCTION: DONT SET MAJOR ALERT IF GLITCH IN PC TARGET //////////

  //TODO: recheck property when rtl for PC_hardnine == 0 is imoplemented

  property p_xsecure_hardened_pc_non_sequential_dont_set_major_alert(pc_hardening, fsm_state, calculated_signal);

    seq_pc_hardening_non_sequential_instruction_with_glitch(pc_hardening, fsm_state, calculated_signal)

    |=>
    //Make sure alert major is not set
    !xsecure_if.core_alert_major_o;

  endproperty

  a_xsecure_pc_hardening_off_branch_set_alert_major: assert property(
    p_xsecure_hardened_pc_non_sequential_dont_set_major_alert(!xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening, BRANCH_STATE, xsecure_if.core_i_ex_stage_i_branch_target_o)
  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed mret instruction set alert major even though PC hardening is off.\n");

  a_xsecure_pc_hardening_off_jump_set_alert_major: assert property(
    p_xsecure_hardened_pc_non_sequential_dont_set_major_alert(!xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening, JUMP_STATE, xsecure_if.core_i_jump_target_id)
  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed mret instruction set alert major even though PC hardening is off.\n");

  a_xsecure_pc_hardening_off_mret_set_alert_major: assert property(
    p_xsecure_hardened_pc_non_sequential_dont_set_major_alert(!xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening, MRET_STATE, xsecure_if.core_i_cs_registers_i_mepc_o)
  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed mret instruction set alert major even though PC hardening is off.\n");


  ////////// PC HARDENING OFF NON-SEQUENTIAL INSTRUCTION: DONT SET MAJOR ALERT IF GLITCH IN BRANCH DECISION //////////

  a_xsecure_pc_hardening_off_branch_decision_set_alert_major: assert property(

    seq_pc_hardening_branch_decision_glitch(!xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening)

    |=>
    //Make sure alert major was/is not set
    !xsecure_if.core_alert_major_o
    && !$past(xsecure_if.core_alert_major_o)

  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed branch decision set alert major even though PC hardening is off.\n");

endmodule : uvmt_cv32e40s_xsecure_assert
