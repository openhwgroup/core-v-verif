`default_nettype none

module uvmt_cv32e40s_xsecure_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
   uvmt_cv32e40s_xsecure_if xsecure_if,
   uvma_rvfi_instr_if rvfi_if
  );

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
  localparam FUNC3_DIV_REM_INSTRUCTION = 3'b1xx;

  localparam FUNC3_BLTU_INSTRUCTION = 3'b110;

  localparam OPCODE_BIT_15_TO_13_COMPR_BRANCH = 3'b11x;
  localparam OPCODE_BIT_1_TO_0_COMPR_BRANCH = 2'b01;

  localparam REGISTER_MHPMCOUNTER_MCYCLE_FULL = 64'hFFFFFFFFFFFFFFFF;

  localparam REGISTER_x0 = 5'b00000;

  localparam FREQ_SETTING_4 = 4'b0000;
  localparam FREQ_SETTING_8 = 4'b0001;
  localparam FREQ_SETTING_16 = 4'b001x;
  localparam FREQ_SETTING_32 = 4'b01xx;
  localparam FREQ_SETTING_64 = 4'b1xxx;


  // Default settings:
  default clocking @(posedge xsecure_if.clk_i); endclocking
  default disable iff (!(xsecure_if.rst_ni) | !(SECURE));
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
    $rose(xsecure_if.rst_ni)
    |->
    !xsecure_setting;
  endproperty

  property p_xsecure_setting_default_on(logic xsecure_setting);

    //Make sure that when exiting reset mode the xsecure setting is off
    $rose(xsecure_if.rst_ni)
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

  ) else `uvm_error(info_tag, "Exception errors do not set minor alret\n");


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
  ) else `uvm_error(info_tag, "Data independent timing is not on when exiting reset\n");


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
  ) else `uvm_error(info_tag, "Branch timing does not stall the pipeline (given no load/store instruction before the branch instruction)\n");


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

  ) else `uvm_error(info_tag, "We generate dummy instructions even though the dummy setting is off\n");


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
  ) else `uvm_error(info_tag, "Dummy instructions are not inserted in if stage\n");


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
  ) else `uvm_error(info_tag, "Dummy branch instructions do not jump to the next non-dummy instructions\n");


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

  ) else `uvm_error(info_tag, "Dummy instructions do not fetch data from LFSR1 and LFSR2\n");


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

  ) else `uvm_error(info_tag, "The results of the dummy instructions are not stored in the x0 register\n");


  ////////// DUMMY INSTRUCTION UPDATES MCYCLE //////////

  a_xsecure_dummy_instruction_updates_mcycle: assert property (

    //Make sure the gated clock is active
    @(posedge xsecure_if.core_clk_gated)

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

  ) else `uvm_error(info_tag, "Dummy instructions do not update the mcycle register\n");


  ////////// DUMMY INSTRUCTION DO NOT UPDATE MINSTRET //////////

  a_xsecure_dummy_instruction_do_not_update_minstret: assert property (

    //Make sure the gated clock is active
    @(posedge xsecure_if.core_clk_gated)

    //Make sure that minstret is on (not inhibit)
    !xsecure_if.core_cs_registers_mcountinhibit_q_minstret_inhibit

    //Make sure we have an dummy instruction
    && xsecure_if.core_wb_stage_ex_wb_pipe_instr_meta_dummy

    //Make sure the dummy instruction is ready to retire
    && xsecure_if.core_wb_stage_wb_valid_o

    //Make sure the minstret counter ignore the retired dummy instruction
    |=>
    xsecure_if.core_cs_registers_mhpmcounter_minstret == $past(xsecure_if.core_cs_registers_mhpmcounter_minstret)

  ) else `uvm_error(info_tag, "Dummy instructions updates the minstret register\n");


  ////////// DUMMY INSTRUCTION FREQUENCY //////////

  sequence seq_dummy_instruction_within_normal_valid_instructions (num_normal_valid_instructions);
    //Make sure we detect a dummy instruction inbetween the x valid instructions

    //Make sure we detect 0 to x number of normal valid instrctions in the if stage
    (xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i)[->0:(num_normal_valid_instructions)]

    //Make sure we detect a dummy instruction
    ##0 xsecure_if.core_if_stage_instr_meta_n_dummy

    //Make sure we detect 0 to x number of normal valid instruction in the if stage
    ##0 (xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i)[->0:(num_normal_valid_instructions)];
  endsequence


  property p_xsecure_dummy_instruction_frequency(num_normal_valid_instructions_per_dummy_instruction, logic [3:0] rnddummyfreq_value);

    //Make sure the dummy setting is on
    (xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy

    //Make sure the frequency of dummy instructions is set to correct value
    && xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummyfreq == rnddummyfreq_value

    //Make sure there are no lockup errors
    && xsecure_if.core_cs_registers_xsecure_lfsr_lockup == NO_LOCKUP_ERRORS

    //Make sure the controller is not in debug mode
    && !xsecure_if.core_controller_controller_fsm_debug_mode_q

    //Make sure the dummy instructions are allways enabled
    && xsecure_if.core_if_stage_gen_dummy_instr_dummy_instr_dummy_en)

    //Make sure we detect new instructions in the if id pipe
    throughout (xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i)[->(num_normal_valid_instructions_per_dummy_instruction + 1)]

    //Make sure that we detect one valid dummy instruction inbetween the number of normal valid instructions
    |->
    seq_dummy_instruction_within_normal_valid_instructions(num_normal_valid_instructions_per_dummy_instruction + 1).triggered;

  endproperty


  //FREQ = 4
  a_xsecure_dummy_instruction_frequency_4: assert property (
	  p_xsecure_dummy_instruction_frequency(
      4,
      FREQ_SETTING_4)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-4\n");

  //FREQ = 8
  a_xsecure_dummy_instruction_frequency_8: assert property (
	  p_xsecure_dummy_instruction_frequency(
      8,
      FREQ_SETTING_8)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-8 or higher\n");

  //FREQ = 16
  a_xsecure_dummy_instruction_frequency_16: assert property (
	  p_xsecure_dummy_instruction_frequency(
      16,
      FREQ_SETTING_16)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-16 or higher\n");

  //FREQ = 32
  a_xsecure_dummy_instruction_frequency_32: assert property (
	  p_xsecure_dummy_instruction_frequency(
      32,
      FREQ_SETTING_32)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-32 or higher\n");

  //FREQ = 64
  a_xsecure_dummy_instruction_frequency_64: assert property (
	  p_xsecure_dummy_instruction_frequency(
      64,
      FREQ_SETTING_64)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-64 or higher\n");


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
  ) else `uvm_error(info_tag, "LFSR0 does not reset to default value when when there is a lookup error (given that we do not write to the register)\n");

  //LFSR1
  a_xsecure_dummy_instruction_LFSR1_lockup_reset: assert property (
	  p_xsecure_dummy_instruction_LFSRx_lockup_reset(
      1,
      xsecure_if.core_cs_registers_xsecure_lfsr1_seed_we,
	    xsecure_if.core_xsecure_ctrl_lfsr1,
      xsecure_if.core_LFSR1_CFG_default_seed)
  ) else `uvm_error(info_tag, "LFSR1 does not reset to default value when when there is a lookup error (given that we do not write to the register)\n");

  //LFSR2
  a_xsecure_dummy_instruction_LFSR2_lockup_reset: assert property (
	  p_xsecure_dummy_instruction_LFSRx_lockup_reset(
      2,
      xsecure_if.core_cs_registers_xsecure_lfsr2_seed_we,
	    xsecure_if.core_xsecure_ctrl_lfsr2,
      xsecure_if.core_LFSR2_CFG_default_seed)
  ) else `uvm_error(info_tag, "LFSR2 does not reset to default value when when there is a lookup error (given that we do not write to the register)\n");


  /////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////// REDUCTION OF PROFILING INFRASTRUCTURE /////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////////


  a_xsecure_reduction_of_profiling_infrastructure_mhpmevent_31_to_3_are_zero: assert property (

    //Make sure the mhpmevent 3 to 31 are hardwired to zero
    |xsecure_if.core_cs_registers_mhpmevent_31_to_3 == 1'b0

  ) else `uvm_error(info_tag, "The mhpmevent registers 31 to 3 is not hardwired to zero\n");


  a_xsecure_reduction_of_profiling_infrastructure_mhpmcounter_31_to_3_are_zero: assert property (

    //Make sure the mhpmcounter 3 to 31 are hardwired to zero
    //(we include mhpmcounterh in the mhpmcounter signal)
    |xsecure_if.core_cs_registers_mhpmcounter_31_to_3 == 1'b0

  ) else `uvm_error(info_tag, "The mhpmcounter registers 31 to 3 is not hardwired to zero\n");

endmodule : uvmt_cv32e40s_xsecure_assert

`default_nettype wire



