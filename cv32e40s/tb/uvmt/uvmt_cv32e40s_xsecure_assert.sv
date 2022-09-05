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

  //TODO: change rvfi_trap and rvfi_intr from using bit position to struct fields when the rvfi interface is updated

  // Local parameters:
  localparam no_lockup_errors = 3'b000;
  localparam lockup_error = 1'b1;
  
  localparam error_code_instruction_access_fault = 6'd1;
  localparam error_code_illegal_instruction_fault = 6'd2;
  localparam error_code_load_access_fault = 6'd5;
  localparam error_code_store_AMO_access_fault = 6'd7;
  localparam error_code_instruction_bus_fault = 6'd24;
  localparam error_code_load_bus_fault_nmi = 11'd1024;
  localparam error_code_store_bus_fault_nmi = 11'd1025;

  localparam func7_branch_instruction = 7'bxxxxxxx;
  localparam func3_branch_instruction = 3'bxxx;

  localparam func7_div_rem_instruction = 7'b0000001;
  localparam func3_div_rem_instruction = 3'b1xx;

  localparam func3_bltu_instruction = 3'b110;

  localparam register_mhpmcounter_mcycle_full = 32'hFFFFFFFF;

  localparam register_x0 = 5'b00000;

  localparam freq_setting_4 = 4'b0000;
  localparam freq_setting_8 = 4'b0001;
  localparam freq_setting_16 = 4'b001x;
  localparam freq_setting_32 = 4'b01xx;
  localparam freq_setting_64 = 4'b1xxx;  
  
  
  // Default settings:
  default clocking @(posedge xsecure_if.clk_i); endclocking
  default disable iff (!(xsecure_if.rst_ni) | !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT";


  /////////////////////////////////////////////////////////////////////
  ///////////////////////// GENERAL SEQUENCES /////////////////////////
  /////////////////////////////////////////////////////////////////////
  

  sequence s_rvfi_normal_instruction (logic [6:0] func7, logic [2:0] func3, logic [6:0] opcode);
    
    //Make sure there is no traped instruction
    !rvfi_if.rvfi_trap[0]

    //Make sure the instruction is valid
    && rvfi_if.rvfi_valid

    //Explicitly state what instruction we work with by using the opcode, func3 and func7
    && rvfi_if.rvfi_insn[6:0] == opcode
    && rvfi_if.rvfi_insn[14:12] == func3
    && rvfi_if.rvfi_insn[31:25] == func7;
  endsequence


  property p_xsecure_setting_default_off(logic xsecure_setting);
    
    //Make sure that when exiting reset mode the xsecure setting is off
    $rose(xsecure_if.rst_ni)
    |->
    !xsecure_setting;
  endproperty


  ///////////////////////////////////////////////////////////////////
  ///////////////////////// SECURITY ALERTS /////////////////////////
  ///////////////////////////////////////////////////////////////////


  ////////// SECURITY ALERTS MINOR //////////
  a_xsecure_security_alert_minor_1: assert property (
    
    //Make sure we detect a lockup error
    xsecure_if.core_cs_registers_xsecure_lfsr_lockup != no_lockup_errors

    //Make sure alert minor is set
    |=>
    xsecure_if.core_alert_minor_o

  ) else `uvm_error(info_tag, "Lookup errors do not set minor alert.\n");


  a_xsecure_security_alert_minor_2_to_6: assert property (
    
    //Make sure we look at a valid instruction
    rvfi_if.rvfi_valid

    //Make sure the instruction is associated with a trap and an exception error and not an interrupt error
    && rvfi_if.rvfi_trap[0]
    && rvfi_if.rvfi_trap[1]

    //Instruction access fault
    && (rvfi_if.rvfi_trap[8:3] == error_code_instruction_access_fault

    //Illegal instruction fault
    || rvfi_if.rvfi_trap[8:3] == error_code_illegal_instruction_fault
    
    //Load access fault
    || rvfi_if.rvfi_trap[8:3] == error_code_load_access_fault
    
    //Store/AMO access fault
    || rvfi_if.rvfi_trap[8:3] == error_code_store_AMO_access_fault
    
    //Instruction bus fault
    || rvfi_if.rvfi_trap[8:3] == error_code_instruction_bus_fault)

    //The error is handled in WB stage, and notify the alert minor signal in the next stage (the current/rvfi stage)
    |-> 
    xsecure_if.core_alert_minor_o

  ) else `uvm_error(info_tag, "Exception errors do not set minor alret\n");


  //TODO: Not passing because of possibly rtl bug
  //TODO: Need to check this after bug is fixed
  //TODO: Comment when passing
  a_xsecure_security_alert_minor_7_and_8_rvfi: assert property (
    
    rvfi_if.rvfi_valid

    && rvfi_if.rvfi_intr[0]
    
    && !rvfi_if.rvfi_intr[1]
    
    && rvfi_if.rvfi_intr[2]
    
    && (rvfi_if.rvfi_intr[13:3] == error_code_load_bus_fault_nmi

    || rvfi_if.rvfi_intr[13:3] == error_code_store_bus_fault_nmi)

    |=>
    xsecure_if.core_alert_minor_o

  ) else `uvm_error(info_tag, "NMI errors do not set minor alert\n");


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
    s_rvfi_normal_instruction(func7_branch_instruction, func3_branch_instruction, cv32e40s_pkg::OPCODE_BRANCH)

    //Make sure the data independent timing was off when executing the branch (ex stage):
    and $past(!xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)

    //Make sure it is possible that the branch instruction is directly followed by another instruction (as the branch is not taken)
    ##1 rvfi_if.rvfi_valid
  );
  

  c_xsecure_core_div_rem_timing_clk: cover property (

    //Make sure we detect an DIV or REM instruction in rvfi
    s_rvfi_normal_instruction(func7_div_rem_instruction, func3_div_rem_instruction, cv32e40s_pkg::OPCODE_OP)

    //Make dure data independent timing was off when the DIV/REM instruction was in EX stage
    and $past(!xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)
    
    //Make sure that it is possible that the instruction was directly followed by another instruction
    && $past(rvfi_if.rvfi_valid)

  );


  ////////// DATA INDEPENDENT TIMING DEFAULT OFF //////////
  
  a_xsecure_dataindtiming_default_off: assert property (
	  p_xsecure_setting_default_off(
	  xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming) //Sjekker jeg sekvens 1? Det kan hende at den roser i første syklusindtiming)
  ) else `uvm_error(info_tag, "Data independent timing is not off when exiting reset\n");
 

  ////////// BRANCH TIMING //////////

  a_xsecure_branch_timing: assert property (

    //Make sure a branch instruction is executed (rvfi stage):
    s_rvfi_normal_instruction(func7_branch_instruction, func3_branch_instruction, cv32e40s_pkg::OPCODE_BRANCH)

    //Make sure the data independent timing was on when executing the branch (ex stage):
    and $past(xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)

    //Make sure that the instruction before the branch instruction was not a load or a store (rvfi stage):
    //We use past 2 because branching needs two cycles to complete execution due to PC harning safety.
    && $past(!|rvfi_if.rvfi_mem_rmask,2)
    && $past(!|rvfi_if.rvfi_mem_wmask,2)

    //Make sure there are at least one instruction stall after every branch, because a branch is allways taken.
    //We would expect 2 instruction stalls, but since the branch instruction is recalculated in id stage we have only one stall, instead of two.
    |=>
    !rvfi_if.rvfi_valid
  ) else `uvm_error(info_tag, "Branch timing does not stall the pipeline (given no load/store instruction before the branch instruction)\n");


  ////////// DIV/REM TIMING //////////

  a_xsecure_core_div_rem_timing_clk: assert property (
    
    //Make sure we detect an DIV or REM instruction in rvfi
    s_rvfi_normal_instruction(func7_div_rem_instruction, func3_div_rem_instruction, cv32e40s_pkg::OPCODE_OP)

    //Make dure data independent timing was on when the DIV/REM instruction was in EX stage
    //(Checks only the last cycle it is in EX stage because if it is it indecate that it always was (certaint(?) CSR instruction changes invalidate instruction))
    and $past(xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming,2)
    
    //Make sure that there are at least 35 cycles from the last retired instruction, or the retired instructions are loads or stores.
    |->
    ($past(!rvfi_if.rvfi_valid, 34) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 34))
    && ($past(!rvfi_if.rvfi_valid, 33) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 33))
    && ($past(!rvfi_if.rvfi_valid, 32) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 32))
    && ($past(!rvfi_if.rvfi_valid, 31) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 31))
    && ($past(!rvfi_if.rvfi_valid, 30) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 30))
    && ($past(!rvfi_if.rvfi_valid, 29) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 29))
    && ($past(!rvfi_if.rvfi_valid, 28) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 28))
    && ($past(!rvfi_if.rvfi_valid, 27) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 27))
    && ($past(!rvfi_if.rvfi_valid, 26) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 26))
    && ($past(!rvfi_if.rvfi_valid, 25) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 25))
    && ($past(!rvfi_if.rvfi_valid, 24) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 24))
    && ($past(!rvfi_if.rvfi_valid, 23) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 23))
    && ($past(!rvfi_if.rvfi_valid, 22) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 22))
    && ($past(!rvfi_if.rvfi_valid, 21) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 21))
    && ($past(!rvfi_if.rvfi_valid, 20) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 20))
    && ($past(!rvfi_if.rvfi_valid, 19) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 19))
    && ($past(!rvfi_if.rvfi_valid, 18) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 18))
    && ($past(!rvfi_if.rvfi_valid, 17) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 17))
    && ($past(!rvfi_if.rvfi_valid, 16) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 16))
    && ($past(!rvfi_if.rvfi_valid, 15) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 15))
    && ($past(!rvfi_if.rvfi_valid, 14) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 14))
    && ($past(!rvfi_if.rvfi_valid, 13) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 13))
    && ($past(!rvfi_if.rvfi_valid, 12) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 12))
    && ($past(!rvfi_if.rvfi_valid, 11) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 11))
    && ($past(!rvfi_if.rvfi_valid, 10) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 10))
    && ($past(!rvfi_if.rvfi_valid, 9) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 9))
    && ($past(!rvfi_if.rvfi_valid, 8) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 8))
    && ($past(!rvfi_if.rvfi_valid, 7) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 7))
    && ($past(!rvfi_if.rvfi_valid, 6) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 6))
    && ($past(!rvfi_if.rvfi_valid, 5) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 5))
    && ($past(!rvfi_if.rvfi_valid, 4) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 4))
    && ($past(!rvfi_if.rvfi_valid, 3) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 3))
    && ($past(!rvfi_if.rvfi_valid, 2) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask), 2))
    && ($past(!rvfi_if.rvfi_valid) | $past(rvfi_if.rvfi_valid & (|rvfi_if.rvfi_mem_rmask | |rvfi_if.rvfi_mem_wmask)))

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

    //Make sure the dummy instruction settings is on when fetching the instruction    
    && xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy

    //Make sure the detected instruction is an dummy instruction
    && xsecure_if.core_id_ex_pipe_instr_meta_dummy

    //Make sure we have BLTU dummy instruction
    && xsecure_if.core_id_ex_pipe_instr_bus_resp_rdata[6:0] == cv32e40s_pkg::OPCODE_BRANCH
    && xsecure_if.core_id_ex_pipe_instr_bus_resp_rdata[14:12] == func3_bltu_instruction
    
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
    xsecure_if.core_if_id_pipe_instr_bus_resp_rdata[11:7] == register_x0
    
  ) else `uvm_error(info_tag, "The results of the dummy instructions are not stored in the x0 register\n");


  ////////// DUMMY INSTRUCTION UPDATES MCYCLE //////////

  a_xsecure_dummy_instruction_updates_mcycle: assert property (
    
    //Make sure the gated clock is active 
    @(posedge xsecure_if.core_clk_gated)

    //Make sure that mcycle is on (not inhibit)
    !xsecure_if.core_cs_registers_mcountinhibit_q_mcycle_inhibit
     
    //Make sure we do not write to the mcycle csr register
    and ($past(!xsecure_if.core_cs_registers_csr_en_gated)
    && $past(xsecure_if.core_cs_registers_csr_waddr != cv32e40s_pkg::CSR_MCYCLE))
    
    |->
    //Make sure the mcycle counts every cycle (including the clock cycles dummy instruction occurs)
    xsecure_if.core_cs_registers_mhpmcounter_mcycle == ($past(xsecure_if.core_cs_registers_mhpmcounter_mcycle) + 1)
    
    //But make sure it resets in case of overflow
    or xsecure_if.core_cs_registers_mhpmcounter_mcycle == '0 && $past(xsecure_if.core_cs_registers_mhpmcounter_mcycle) == register_mhpmcounter_mcycle_full

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

  sequence seq_consecuent_dummy_freq_dot_triggered(integer frequency_of_dummy_instructions_plus_one);
    //Make sure we start in a valid clock cycle
    1
    
    //Make sure we detect a dummy instruction as one out of the 0 to x valid instructions

    //Make sure we detect 0 to x number of valid instrctions in the if stage
    ##0 (xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i)[->0:(frequency_of_dummy_instructions_plus_one)]

    //Make sure we detect a dummy instruction
    ##0 xsecure_if.core_if_stage_instr_meta_n_dummy

    //Make sure we detect 0 to x number of valid instruction in the if stage
    ##0 (xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i)[->0:(frequency_of_dummy_instructions_plus_one)]
    
    //Make sure we end in a valid clock cycle
    ##0 1;

  endsequence
  
  
  property p_xsecure_dummy_instruction_frequency(integer frequency_of_dummy_instructions, logic [3:0] rnddummyfreq_value);
    
    //Make sure the dummy setting is on
    (xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy
    
    //Make sure the frequency of dummy instructions is set to correct value
    && xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummyfreq == rnddummyfreq_value

    //Make sure there are no lockup errors
    && xsecure_if.core_cs_registers_xsecure_lfsr_lockup == no_lockup_errors
    
    //Make sure the controller is not in debug mode
    && !xsecure_if.core_controller_controller_fsm_debug_mode_q

    //Make sure the dummy instructions are allways enabled
    && xsecure_if.core_if_stage_gen_dummy_instr_dummy_instr_dummy_en)
    
    //Make sure we detect new instructions in the if id pipe
    throughout (xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i)[->(frequency_of_dummy_instructions + 1)]

    //Make sure that we detect one valid dummy instruction inbetween the x number of normal instructions
    |-> 
    seq_consecuent_dummy_freq_dot_triggered(frequency_of_dummy_instructions + 1).triggered;
  
  endproperty


  //FREQ = 4
  a_xsecure_dummy_instruction_frequency_4: assert property (
	  p_xsecure_dummy_instruction_frequency(
      4,
      freq_setting_4)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-4\n");
 
  //FREQ = 8
  a_xsecure_dummy_instruction_frequency_8: assert property (
	  p_xsecure_dummy_instruction_frequency(
      8,
      freq_setting_8)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-8 or higher\n");

  //FREQ = 16
  a_xsecure_dummy_instruction_frequency_16: assert property (
	  p_xsecure_dummy_instruction_frequency(
      16,
      freq_setting_16)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-16 or higher\n");

  //FREQ = 32
  a_xsecure_dummy_instruction_frequency_32: assert property (
	  p_xsecure_dummy_instruction_frequency(
      32,
      freq_setting_32)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-32 or higher\n");

  //FREQ = 64
  a_xsecure_dummy_instruction_frequency_64: assert property (
	  p_xsecure_dummy_instruction_frequency(
      64,
      freq_setting_64)
  ) else `uvm_error(info_tag, "Frequency of dummy instructions are not 1-64 or higher\n");


  ////////// DUMMY INSTRUCTION RESET SEED AT LOCKUP ERRORS //////////
 
  property p_xsecure_dummy_instruction_LFSRx_lockup_reset(integer x, logic core_cs_registers_xsecure_lfsrx_seed_we, logic [31:0] core_xsecure_ctrl_lfsrx, logic [31:0] core_LFSRx_CFG_default_seed);
    
    //Make sure the dummy setting is on
    xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy
    
    //Make sure there is a lockup error on register x
    && xsecure_if.core_cs_registers_xsecure_lfsr_lockup[x] == lockup_error

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
    |xsecure_if.core_cs_registers_mhpmevent_31_to_3 == '0
  
  ) else `uvm_error(info_tag, "The mhpmevent registers 31 to 3 is not hardwired to zero\n");


  a_xsecure_reduction_of_profiling_infrastructure_mhpmcounter_31_to_3_are_zero: assert property (
    
    //Make sure the mhpmcounter 3 to 31 are hardwired to zero
    //(we include mhpmcounterh in the mhpmcounter signal)
    |xsecure_if.core_cs_registers_mhpmcounter_31_to_3 == '0

  ) else `uvm_error(info_tag, "The mhpmcounter registers 31 to 3 is not hardwired to zero\n");

endmodule : uvmt_cv32e40s_xsecure_assert

`default_nettype wire



