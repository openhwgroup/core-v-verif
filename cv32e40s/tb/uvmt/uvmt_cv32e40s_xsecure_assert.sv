//TODO: make header

module uvmt_cv32e40s_xsecure_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1,
    parameter logic     SMCLIC = 0,
    parameter int       PMP_NUM_REGIONS = 2,
    parameter int       MTVT_ADDR_WIDTH = 5,
    parameter int CSR_MINTTHRESH_MASK = 32,
    parameter int PMP_ADDR_WIDTH = 6
  )
  (
   uvmt_cv32e40s_xsecure_if xsecure_if,
   uvma_rvfi_instr_if rvfi_if,
   uvmt_cv32e40s_support_logic_for_assert_coverage_modules_if.slave support_if,
   input rst_ni,
   input clk_i
  );

  //TODO: update hardened CSR documentation as these CSRs are no longer hardened mclicbase, mscratchcsw, mscratchcswl

  // Local parameters:
  localparam NO_LOCKUP_ERRORS = 3'b000;
  localparam LOCKUP_ERROR = 1'b1;

  localparam ERROR_CODE_INSTRUCTION_ACCESS_FAULT = 6'd1;
  localparam ERROR_CODE_ILLEGAL_INSTRUCTION_FAULT = 6'd2;
  localparam ERROR_CODE_LOAD_ACCESS_FAULT = 6'd5;
  localparam ERROR_CODE_STORE_AMO_ACCESS_FAULT = 6'd7;
  localparam ERROR_CODE_INSTRUCTION_BUS_FAULT = 6'd24;

  localparam FUNCT7_DIV_REM_INSTRUCTION = 7'b0000001;
  localparam FUNCT3_DIV_REM_INSTRUCTION_MSB = 1'b1;

  localparam FUNCT3_COMPR_BRANCH_2_MSBS = 2'b11;
  localparam OPCODE_COMPR_BRANCH = 2'b01;

  localparam FUNCT3_COMPR_SLLI = 3'b000;
  localparam OPCODE_COMPR_SLLI = 2'b10;

  localparam REGISTER_MHPMCOUNTER_MCYCLE_FULL = 64'hFFFFFFFFFFFFFFFF;

  localparam REGISTER_x0 = 5'b00000;


  localparam FREQ_SETTING_64_MIN = 4'b1000;
  localparam FREQ_SETTING_64_MAX = 4'b1111;

  localparam FREQ_SETTING_32_MIN = 4'b0100;
  localparam FREQ_SETTING_32_MAX = FREQ_SETTING_64_MIN -1;

  localparam FREQ_SETTING_16_MIN = 4'b0010;
  localparam FREQ_SETTING_16_MAX = FREQ_SETTING_32_MIN -1;

  localparam FREQ_SETTING_8_MIN = 4'b0001;
  localparam FREQ_SETTING_8_MAX = FREQ_SETTING_16_MIN -1;

  localparam FREQ_SETTING_4_MIN = 4'b0000;
  localparam FREQ_SETTING_4_MAX = FREQ_SETTING_8_MIN -1;


  localparam BRANCH_STATE = 4'b0101;
  localparam JUMP_STATE = 4'b0100;
  localparam MRET_STATE = 4'b0001;

  localparam NON_CMPR_INSTRUCTION_INCREMENT = 4;
  localparam CMPR_INSTRUCTION_INCREMENT = 2;

  localparam DUMMY_INCREMENT = 0;
  localparam HINT_INCREMENT = 2;

  //Sticky bit that indicates if the major alert has been set.
  logic alert_major_was_set;

  //Support logic that sets the sticky alert_major_was_set bit when the major alert goes high.
  //When alert_major_was_set is 1, the only way to clear the bit is to do a reset.
  always @(posedge clk_i) begin
    if(!rst_ni) begin
      alert_major_was_set <= 0;
    end else if (xsecure_if.core_alert_major_o) begin
      alert_major_was_set <= xsecure_if.core_alert_major_o;
    end
  end

  //Descriptive signal names
  logic [5:0] rvfi_c_slli_shamt;
  assign rvfi_c_slli_shamt = {rvfi_if.rvfi_insn[12], rvfi_if.rvfi_insn[6:2]};

  logic [4:0] if_id_pipe_instr_rs1;
  logic [4:0] if_id_pipe_instr_rs2;
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

  //Signal used to check if the core clock is active or not.
  logic core_clock_cycles;

  always @(posedge clk_i) begin
    if(!rst_ni) begin
      core_clock_cycles <= 0;
    end else begin
      core_clock_cycles <= xsecure_if.clk_en;
    end
  end

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) | !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT";


  //////////////////////////////////////////////////////////////////////
  ///////////////////////// GENERAL PROPERTIES /////////////////////////
  //////////////////////////////////////////////////////////////////////

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

    //Make sure the alert minor is set
    |=>
    xsecure_if.core_alert_minor_o

  ) else `uvm_error(info_tag, "Lookup errors do not set the minor alert.\n");


  a_xsecure_security_alert_minor_2_to_6: assert property (

    //Make sure we look at a valid instruction
    rvfi_if.rvfi_valid

    //Make sure the instruction is associated with a trap and an exception error
    && rvfi_if.rvfi_trap.trap
    && rvfi_if.rvfi_trap.exception

    //Instruction access fault
    && (rvfi_if.rvfi_trap.exception_cause == ERROR_CODE_INSTRUCTION_ACCESS_FAULT

    //Illegal instruction fault
    || rvfi_if.rvfi_trap.exception_cause == ERROR_CODE_ILLEGAL_INSTRUCTION_FAULT

    //Load access fault
    || rvfi_if.rvfi_trap.exception_cause == ERROR_CODE_LOAD_ACCESS_FAULT

    //Store/AMO access fault
    || rvfi_if.rvfi_trap.exception_cause == ERROR_CODE_STORE_AMO_ACCESS_FAULT

    //Instruction bus fault
    || rvfi_if.rvfi_trap.exception_cause == ERROR_CODE_INSTRUCTION_BUS_FAULT)

    ///TODO: The error is handled in the WB stage and notifies the alert minor signal in the next stage (the current/rvfi stage)
    |->
    xsecure_if.core_alert_minor_o

  ) else `uvm_error(info_tag, "Exception errors do not set the minor alert.\n");


  ///////////////////////////////////////////////////////////////////////////
  ///////////////////////// DATA iNDEPENDENT TIMING /////////////////////////
  ///////////////////////////////////////////////////////////////////////////


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

    //Make sure rvfi_valid is off for 34 cycles
    !rvfi_if.rvfi_valid[*34] ##1 1;

  endsequence

  sequence seq_set_rvfi_valid_once_as_memory_instruction_during_the_past_34_cycles;

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


  /////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////// REDUCTION OF PROFILING INFRASTRUCTURE /////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////////


  a_xsecure_reduction_of_profiling_infrastructure_mhpmevent_31_to_3_are_zero: assert property (

    //Make sure the MHPMEVENT 3 to 31 are hardwired to zero
    |xsecure_if.core_cs_registers_mhpmevent_31_to_3 == 1'b0

  ) else `uvm_error(info_tag, "The MHPMEVENT registers 31 to 3 are not hardwired to zero.\n");


  a_xsecure_reduction_of_profiling_infrastructure_mhpmcounter_31_to_3_are_zero: assert property (

    //Make sure the MHPMCOUNTER 3 to 31 are hardwired to zero
    //(we include MHPMCOUNTERH in the MHPMCOUNTER signal)
    |xsecure_if.core_cs_registers_mhpmcounter_31_to_3 == 1'b0

  ) else `uvm_error(info_tag, "The MHPMCOUNTER registers 31 to 3 are not hardwired to zero.\n");


  ////////////////////////////////////////////////////////////////
  ///////////////////////// CSR HARDENING /////////////////////////
  ////////////////////////////////////////////////////////////////


  ////////// SOME CSR ARE SHADOWED //////////

  /****************************************
  The following 4 assertions make sure the CSRs are shadowed at all times:
  The shadow registers are the compliments of the CSRs
  ****************************************/

  a_xsecure_hardened_CSRs_no_missmatch_static_registers: assert property (
    //Make sure the following CSRs are shadowed at all times:

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

  ) else `uvm_error(info_tag, "One or several of the CSRs JVT, MSTATUS, CPUCTRL, DCSR, MEPC, MSCRATCH are not shadowed.\n");

  generate
    if(PMP_NUM_REGIONS > 0) begin
      a_xsecure_hardened_CSRs_no_missmatch_pmp_register: assert property (
      //Make sure the MSECCFG CSR is shadowed at all times (given that we use PMP regions)

      //MSECCFG
      xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_pmp_mseccfg_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_pmp_mseccfg_csr_i_rdata_q & cv32e40s_pkg::CSR_MSECCFG_MASK)

      ) else `uvm_error(info_tag, "The CSR MSECCFG is not shadowed.\n");

    end
  endgenerate

  generate for (genvar n = 0; n < PMP_NUM_REGIONS; n++) begin

    a_xsecure_hardened_CSRs_no_missmatch_pmp_region_registers: assert property (
      //Make sure the existing PMP CSRs are shadowed at all times

      //PMPNCFG
      xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_gen_pmp_csr_n_pmp_region_pmpncfg_csr_i_gen_hardened_shadow_q[n] == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_csr_pmp_gen_pmp_csr_n_pmp_region_pmpncfg_csr_i_rdata_q[n] & cv32e40s_pkg::CSR_PMPNCFG_MASK)

      //PMPADDR
      and xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_gen_pmp_csr_n_pmp_region_pmp_addr_csr_gen_hardened_shadow_q[n] == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_csr_pmp_gen_pmp_csr_n_pmp_region_pmp_addr_csr_i_rdata_q[n] & cv32e40s_pkg::CSR_PMPADDR_MASK[PMP_ADDR_WIDTH-1:0])

    ) else `uvm_error(info_tag, $sformatf("One or several of the CSRs PMP%0dCFG or PMPADDR[%0d] are not shadowed.\n", n, n));

  end endgenerate

  generate
    if(SMCLIC) begin
      a_xsecure_hardened_CSRs_no_missmatch_smclic_registers: assert property (
        //Make sure the smclic CSRs are shadowed at all times if smclic is enabled

        //MTVT
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mtvt_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mtvt_csr_i_rdata_q & cv32e40s_pkg::CSR_MTVT_MASK)

        //MTVEC
        and xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mtvec_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mtvec_csr_i_rdata_q & cv32e40s_pkg::CSR_MTVEC_CLIC_MASK)

        //MINTSTATUS
        and xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mintstatus_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mintstatus_csr_i_rdata_q & cv32e40s_pkg::CSR_MINTSTATUS_MASK)

        //MINTTHRESH
        and xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mintthresh_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mintthresh_csr_i_rdata_q & CSR_MINTTHRESH_MASK)

      ) else `uvm_error(info_tag, "One or several of the CSRs MTVT, MTVEC, MINTSTATUS or MINTTHRESH are not shadowed.\n");

    end else begin

      a_xsecure_hardened_CSRs_no_missmatch_basic_mode_registers: assert property (
        //Make sure the CSRs used when smclic is disabled are shadowed at all times

        //MTVEC
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mtvec_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mtvec_csr_rdata_q & cv32e40s_pkg::CSR_MTVEC_BASIC_MASK)

        //MIE
        and xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mie_csr_gen_hardened_shadow_q == ~(xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mie_csr_rdata_q & cv32e40s_pkg::IRQ_MASK)

      ) else `uvm_error(info_tag, "The CSRs MTVEC or MIE are not shadowed.\n");

    end
  endgenerate


  ////////// SET THE MAJOR ALERT IF A CSR IS NOT SHADOWED //////////

  property p_xsecure_hardned_csr_missmatch_sets_alert_major(csr, shadow, MASK);
    //Make sure we only set the major alert if we are in the operating mode (use the gated clock)
    @(posedge xsecure_if.core_clk)

    //csr & mask: make sure the bits we are not interested in are set to 0s, which is determined by the mask
    //(shadow | ~MASK): this operation turns the unmasked bits of the shadow register to 1s (so they will become compliments of the unmasked bits of the CSR (which are all 0s))
    //~(shadow | ~MASK) != (CSR & MASK): this operation checks if the shadow register (and its unmasked bits) are compliments of the CSR (and its unmasked bits)
    ~(shadow | ~MASK) != (csr & MASK)

    //Make sure the alert major is set if there is a mismatch of the CSR and shadow register
    |=>
    xsecure_if.core_alert_major_o;

  endproperty

  /****************************************
  The following assertions check whether a mismatch between a CSR and its corresponding shadow register results in the major alert being set.
  ****************************************/

  //JVT:
  a_xsecure_hardened_CSRs_missmatch_jvt: assert property (
    p_xsecure_hardned_csr_missmatch_sets_alert_major(
      xsecure_if.core_i_cs_registers_i_jvt_csr_i_rdata_q,
      xsecure_if.core_cs_registers_jvt_csr_gen_hardened_shadow_q,
      cv32e40s_pkg::CSR_JVT_MASK)
  ) else `uvm_error(info_tag, "A mismatch between the JVT CSR and its shadow register does not result in the major alert being set.\n");

  //MSTATUS:
  a_xsecure_hardened_CSRs_missmatch_mstatus: assert property (
    p_xsecure_hardned_csr_missmatch_sets_alert_major(
      xsecure_if.core_i_cs_registers_i_mstatus_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mstatus_csr_gen_hardened_shadow_q,
      cv32e40s_pkg::CSR_MSTATUS_MASK)
  ) else `uvm_error(info_tag, "A mismatch between the MSTATUS CSR and its shadow register does not result in the major alert being set.\n");

  //CPUCTRL:
  a_xsecure_hardened_CSRs_missmatch_cpuctrl: assert property (
    p_xsecure_hardned_csr_missmatch_sets_alert_major(
      xsecure_if.core_i_cs_registers_i_xsecure_cpuctrl_csr_i_rdata_q,
      xsecure_if.core_cs_registers_xsecure_cpuctrl_csr_gen_hardened_shadow_q,
      cv32e40s_pkg::CSR_CPUCTRL_MASK)
  ) else `uvm_error(info_tag, "A mismatch between the CPUCTRL CSR and its shadow register does not result in the major alert being set.\n");

  //DCSR:
  a_xsecure_hardened_CSRs_missmatch_dcsr: assert property (
    p_xsecure_hardned_csr_missmatch_sets_alert_major(
      xsecure_if.core_i_cs_registers_i_dcsr_csr_i_rdata_q,
      xsecure_if.core_cs_registers_dcsr_csr_gen_hardened_shadow_q,
      cv32e40s_pkg::CSR_DCSR_MASK)
  ) else `uvm_error(info_tag, "A mismatch between the DCSR CSR and its shadow register does not result in the major alert being set.\n");

  //MEPC:
  a_xsecure_hardened_CSRs_missmatch_mepc: assert property (
    p_xsecure_hardned_csr_missmatch_sets_alert_major(
      xsecure_if.core_i_cs_registers_i_mepc_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mepc_csr_gen_hardened_shadow_q,
      cv32e40s_pkg::CSR_MEPC_MASK)
  ) else `uvm_error(info_tag, "A mismatch between the MEPC CSR and its shadow register does not result in the major alert being set.\n");

  //MSCRATCH:
  a_xsecure_hardened_CSRs_missmatch_mscratch: assert property (
    p_xsecure_hardned_csr_missmatch_sets_alert_major(
      xsecure_if.core_i_cs_registers_i_mscratch_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mscratch_csr_gen_hardened_shadow_q,
      cv32e40s_pkg::CSR_MSCRATCH_MASK)
  ) else `uvm_error(info_tag, "A mismatch between the MSCRATCH CSR and its shadow register does not result in the major alert being set.\n");

  generate
    if(PMP_NUM_REGIONS > 0) begin

      //MSECCFG:
      a_xsecure_hardened_CSRs_missmatch_mseccfg: assert property (
        p_xsecure_hardned_csr_missmatch_sets_alert_major(
          xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_pmp_mseccfg_csr_i_rdata_q,
          xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_pmp_mseccfg_csr_gen_hardened_shadow_q,
          cv32e40s_pkg::CSR_MSECCFG_MASK)
      ) else `uvm_error(info_tag, "A mismatch between the MSECCFG CSR and its shadow register does not result in the major alert being set.\n");

    end
  endgenerate


  generate for (genvar n = 0; n < PMP_NUM_REGIONS; n++) begin
    //PMPNCFG:
    a_xsecure_hardened_CSRs_missmatch_pmpncfg: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_csr_pmp_gen_pmp_csr_n_pmp_region_pmpncfg_csr_i_rdata_q[n],
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_gen_pmp_csr_n_pmp_region_pmpncfg_csr_i_gen_hardened_shadow_q[n],
        cv32e40s_pkg::CSR_PMPNCFG_MASK)
    ) else `uvm_error(info_tag, $sformatf("The mismatch between the PMP%0dCFG CSR and its shadow register does not result in the major alert being set.\n", n));

    //PMPADDR:
    a_xsecure_hardened_CSRs_missmatch_pmpaddr: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_csr_pmp_gen_pmp_csr_n_pmp_region_pmp_addr_csr_i_rdata_q[n],
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_csr_pmp_gen_pmp_csr_n_pmp_region_pmp_addr_csr_gen_hardened_shadow_q[n],
        cv32e40s_pkg::CSR_PMPADDR_MASK[PMP_ADDR_WIDTH-1:0])
    ) else `uvm_error(info_tag, $sformatf("The mismatch between the PMPADDR[%0d] CSR and its shadow register does not result in the major alert being set.\n", n));

  end endgenerate


  if(SMCLIC) begin
    //MTVT:
    a_xsecure_hardened_CSRs_missmatch_mtvt: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mtvt_csr_i_rdata_q,
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mtvt_csr_gen_hardened_shadow_q,
        cv32e40s_pkg::CSR_MTVT_MASK)
    ) else `uvm_error(info_tag, "A mismatch between the MTVT CSR and its shadow register does not result in the major alert being set.\n");

    //MTVEC:
    a_xsecure_hardened_CSRs_missmatch_mtvec: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mtvec_csr_i_rdata_q,
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mtvec_csr_gen_hardened_shadow_q,
        cv32e40s_pkg::CSR_MTVEC_CLIC_MASK)
    ) else `uvm_error(info_tag, "A mismatch between the MTVEC CSR and its shadow register does not result in the major alert being set.\n");

    //MINTSTATUS:
    a_xsecure_hardened_CSRs_missmatch_mintstatus: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mintstatus_csr_i_rdata_q,
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mintstatus_csr_gen_hardened_shadow_q,
        cv32e40s_pkg::CSR_MINTSTATUS_MASK)
    ) else `uvm_error(info_tag, "A mismatch between the MINTSTATUS CSR and its shadow register does not result in the major alert being set.\n");

    //MINTTHRESH:
    a_xsecure_hardened_CSRs_missmatch_mintthresh: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_i_core_i_cs_registers_i_smclic_csrs_mintthresh_csr_i_rdata_q,
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_smclic_csrs_mintthresh_csr_gen_hardened_shadow_q,
        CSR_MINTTHRESH_MASK)
    ) else `uvm_error(info_tag, "A mismatch between the MINTTHRESH CSR and its shadow register does not result in the major alert being set.\n");

  end else begin

    //MTVEC:
    a_xsecure_hardened_CSRs_missmatch_mtvec: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mtvec_csr_rdata_q,
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mtvec_csr_gen_hardened_shadow_q,
        cv32e40s_pkg::CSR_MTVEC_BASIC_MASK)
    ) else `uvm_error(info_tag, "A mismatch between the MTVEC CSR and its shadow register does not result in the major alert being set.\n");

    //MIE:
    a_xsecure_hardened_CSRs_missmatch_mie: assert property (
      p_xsecure_hardned_csr_missmatch_sets_alert_major(
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mie_csr_rdata_q,
        xsecure_if.dut_wrap_cv32e40s_wrapper_core_cs_registers_basic_mode_csrs_mie_csr_gen_hardened_shadow_q,
        cv32e40s_pkg::IRQ_MASK)
    ) else `uvm_error(info_tag, "A mismatch between the MIE CSR and its shadow register does not result in the major alert being set.\n");

  end

  /////////////////////////////////////////////////////////////////////
  ///////////////////////// REGISTER FILE ECC /////////////////////////
  /////////////////////////////////////////////////////////////////////

  ////////// GENERAL PURPOSE REGISTERS ARE ZERO WHEN EXITING RESET //////////

  //Check that the GPR is reset to 0 when exiting the reset stage:
  property p_xsecure_gpr_reset(integer register_addr);
    //Make sure we are going out of reset
    $rose(rst_ni)

    //Make sure the general purpose register of address <register_addr> is reset to zero
    |->
    xsecure_if.core_register_file_wrapper_register_file_mem[register_addr][31:0] == 32'h0000_0000

    //Make sure the ECC score of the general purpose register of address "register_addr" is the ECC encoding of the value zero
    && xsecure_if.core_register_file_wrapper_register_file_mem[register_addr][37:32] == 6'h2a;

  endproperty


  //Use RVFI to check that RS1 has a value of 0 when exiting the reset stage:
  property p_xsecure_gpr_reset_rvfi_rs1(integer register_addr);

    //Make sure we check out the first instruction after the reset stage
    $rose(rst_ni) ##0 rvfi_if.rvfi_valid[->1]

    //Make sure the instruction reads the RS1 value
    ##0 rvfi_if.rvfi_rs1_addr == register_addr

    //Make sure the RS1 value is 0
    |->
    rvfi_if.rvfi_rs1_rdata == 32'h0000_0000;

  endproperty


  //Use RVFI to check that RS2 has a value of 0 when exiting the reset stage:
  property p_xsecure_gpr_reset_rvfi_rs2(integer register_addr);

    //Make sure we check out the first instruction after the reset stage
    $rose(rst_ni) ##0 rvfi_if.rvfi_valid[->1]

    //Make sure the instruction reads the RS1 value
    ##0 rvfi_if.rvfi_rs2_addr == register_addr

    //Make sure the RS2 value is 0
    |->
    rvfi_if.rvfi_rs2_rdata == 32'h0000_0000;

  endproperty


  //Make reset assertions for each GPR:
  generate for (genvar gpr_addr = 0; gpr_addr < 32; gpr_addr++) begin

    a_xsecure_register_file_ecc_gpr_reset_value: assert property (
      p_xsecure_gpr_reset(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("GPR %0d is not set to 0 when exiting reset stage.\n", gpr_addr));

    a_xsecure_register_file_ecc_gpr_reset_value_rvfi_rs1: assert property (
      p_xsecure_gpr_reset_rvfi_rs1(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("GPR %0d is not set to 0 when exiting reset stage because RS1 is not 0.\n", gpr_addr));

    a_xsecure_register_file_ecc_gpr_reset_value_rvfi_rs2: assert property (
      p_xsecure_gpr_reset_rvfi_rs2(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("GPR %0d is not set to 0 when exiting reset stage because RS2 is not 0.\n", gpr_addr));

  end endgenerate


  ////////// GENERAL PURPOSE REGISTERS AND ECC ATTACHMENTS ARE NEVER ALL ZEROS OR ONES //////////

  //Make assertions for each GPR:
  generate for (genvar gpr_addr = 0; gpr_addr < 32; gpr_addr++) begin

  a_xsecure_register_file_ecc_gprecc_never_all_zeros: assert property (

    //Verify that register and ECC score never is all zeros
    xsecure_if.core_register_file_wrapper_register_file_mem[gpr_addr] != 38'h00_0000_0000

  ) else `uvm_error(info_tag, $sformatf("GPR %0d with attached ECC score is all zeros.\n", gpr_addr));


  a_xsecure_register_file_ecc_gprecc_never_all_ones: assert property (

    //Verify that register and ECC score never is all ones
    xsecure_if.core_register_file_wrapper_register_file_mem[gpr_addr] != 38'h3F_FFFF_FFFF

  ) else `uvm_error(info_tag, $sformatf("GPR %0d with attached ECC score is all ones.\n", gpr_addr));

  end endgenerate


  ////////// IF GENERAL PURPOSE REGISTERS AND ECC ATTACHMENTS ARE ALL ZEROS OR ONES MAJOR ALERT MUST BE SET //////////

  property p_xsecure_register_file_ecc_gprecc_set_major_alert_if_reg_is_all_zeros_or_ones(if_id_pipe_rs_addr);
    logic [4:0] gpr_addr = 0;

    @(posedge xsecure_if.core_clk)

    //Store the source register address in a GPR address variable
    (1, gpr_addr = if_id_pipe_rs_addr)

    //Make sure the source register is not x0 (because GPR x0 behaves different than the other source registers)
    ##0 if_id_pipe_rs_addr != 0

    //Make sure the source registers data and ECC score are all ones or zeros
    ##0 (xsecure_if.core_register_file_wrapper_register_file_mem[gpr_addr] == 38'h00_0000_0000
    || xsecure_if.core_register_file_wrapper_register_file_mem[gpr_addr] == 38'h3F_FFFF_FFFF)

    |=>
    //Verify that the major alert is set
    xsecure_if.core_alert_major_o;

  endproperty


  a_xsecure_register_file_ecc_gprecc_set_major_alert_if_rs1_is_all_zeros_or_ones: assert property (
    p_xsecure_register_file_ecc_gprecc_set_major_alert_if_reg_is_all_zeros_or_ones(if_id_pipe_instr_rs1)
  ) else `uvm_error(info_tag, "The data of RS1 (and the attached ECC score) is all ones or zeros but does not set the major alert.\n");


  a_xsecure_register_file_ecc_gprecc_set_major_alert_if_rs2_is_all_zeros_or_ones: assert property (
    p_xsecure_register_file_ecc_gprecc_set_major_alert_if_reg_is_all_zeros_or_ones(if_id_pipe_instr_rs2)
  ) else `uvm_error(info_tag, "The data of RS2 (and the attached ECC score) is all ones or zeros but does not set the major alert.\n");


  ////////// ECC DECODING MISMATCH ON EVERY READ SETS MAJOR ALERT //////////

  /****************************************
  Support logic:
  The support logic creates a local memory that shadowes the GPR
  In the local memory, we insert data in the same manner as for the GPRs.
  We detect bit flip in the GPRs by comparing them with the local memory
  ****************************************/

  //Local memory for the support logic
  logic [31:0][31:0] gpr_shadow = '0;

  //Make sure the local memory is updated whenever the GPR memory is updated
  always @(posedge clk_i) begin
    if(!rst_ni) begin
      gpr_shadow = '0;
    end else if (xsecure_if.core_rf_we_wb && xsecure_if.core_rf_waddr_wb != 5'b00000) begin
      gpr_shadow[xsecure_if.core_rf_waddr_wb] = xsecure_if.core_rf_wdata_wb;
    end
  end


  //Make sure the support logic works as expected when updating the memory
  a_xsecure_register_file_ecc_no_supression_by_comparing_ecc_scores_support_logic: assert property (

    //Make sure we update the GPR memory
    xsecure_if.core_rf_we_wb

    //Make sure the address is not x0
    && xsecure_if.core_rf_waddr_wb != 5'b00000

    |=>
    //Make sure the local memory is updated in the same manner as the gpr memory
    gpr_shadow[$past(xsecure_if.core_rf_waddr_wb)] == $past(xsecure_if.core_rf_wdata_wb)

  ) else `uvm_error(info_tag, "The support logic does not update the local memory in the same manner as the GPRs.\n");


  //Make sure the support logic works as expected when exiting reset mode
  a_xsecure_register_file_ecc_no_supression_by_comparing_ecc_scores_support_logic_start_at_zero: assert property (

    //Exit reset mode
    $rose(rst_ni)

    //Check that the local memory is set to 0s
    |->
    gpr_shadow == '0

  ) else `uvm_error(info_tag, "The local support memory is not set to 0s when exiting reset.\n");


  property p_xsecure_register_file_ecc_no_supression_reading_rs1(rs1_addr);
    @(posedge xsecure_if.core_clk)

    //Make sure there is a noncompressed instruction
    !xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed

    //Specify the RS1 address
    && if_id_pipe_instr_rs1 == rs1_addr

    //Make sure the GPR memory and the local memory differ in one or two bits
    && ($countbits(xsecure_if.core_register_file_wrapper_register_file_mem[rs1_addr][31:0] ^ gpr_shadow[rs1_addr], '1) inside {1,2})

    |=>
    //Make sure the alert major is set
    xsecure_if.core_alert_major_o;
  endproperty


  property p_xsecure_register_file_ecc_no_supression_reading_rs2(rs2_addr);
    @(posedge xsecure_if.core_clk)

    //Make sure there is a noncompressed instruction
    !xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed

    //Specify the RS2 address
    && if_id_pipe_instr_rs2 == rs2_addr

    //Make sure the GPR memory and the local memory differ in one or two bits
    && ($countbits(xsecure_if.core_register_file_wrapper_register_file_mem[rs2_addr][31:0] ^ gpr_shadow[rs2_addr], '1) inside {1,2})

    |=>
    //Make sure the alert major is set
    xsecure_if.core_alert_major_o;
  endproperty


  property p_xsecure_register_file_ecc_no_supression_reading_rs1_cmpr(rs1_addr);
    @(posedge xsecure_if.core_clk)

    //Make sure there is a noncompressed instruction
    xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed

    //Specify the RS1 address
    && if_id_pipe_instr_rs1 == rs1_addr

    //Make sure the GPR memory and the local memory differ in one or two bits
    && ($countbits(xsecure_if.core_register_file_wrapper_register_file_mem[rs1_addr][31:0] ^ gpr_shadow[rs1_addr], '1) inside {1,2})

    |=>
    //Make sure the alert major is set
    xsecure_if.core_alert_major_o;
  endproperty


  property p_xsecure_register_file_ecc_no_supression_reading_rs2_cmpr(rs2_addr);
    @(posedge xsecure_if.core_clk)

    //Make sure there is a noncompressed instruction
    xsecure_if.core_id_stage_if_id_pipe_instr_meta_compressed

    //Specify the RS2 address
    && if_id_pipe_instr_rs2 == rs2_addr

    //Make sure the GPR memory and the local memory differ in one or two bits
    && ($countbits(xsecure_if.core_register_file_wrapper_register_file_mem[rs2_addr][31:0] ^ gpr_shadow[rs2_addr], '1) inside {1,2})

    |=>
    //Make sure the alert major is set
    xsecure_if.core_alert_major_o;
  endproperty

  generate for (genvar gpr_addr = 1; gpr_addr < 32; gpr_addr++) begin

    a_xsecure_register_file_ecc_no_supression_reading_rs1: assert property (
      p_xsecure_register_file_ecc_no_supression_reading_rs1(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("1 or 2 bit errors when reading noncompressed RS1 (address %0d) do not set the alert major.\n", gpr_addr));

    a_xsecure_register_file_ecc_no_supression_reading_rs2: assert property (
      p_xsecure_register_file_ecc_no_supression_reading_rs2(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("1 or 2 bit errors when reading noncompressed RS2 (address %0d) do not set the alert major.\n", gpr_addr));

    a_xsecure_register_file_ecc_no_supression_reading_rs1_cmpr: assert property (
      p_xsecure_register_file_ecc_no_supression_reading_rs1_cmpr(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("1 or 2 bit errors when reading compressed RS1 (address %0d) do not set the alert major.\n", gpr_addr));

    a_xsecure_register_file_ecc_no_supression_reading_rs2_cmpr: assert property (
      p_xsecure_register_file_ecc_no_supression_reading_rs2_cmpr(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("1 or 2 bit errors when reading compressed RS2 (address %0d) do not set the alert major.\n", gpr_addr));

  end endgenerate


  ///////////////////////////////////////////////////////////////
  ///////////////////////// HARDENED PC /////////////////////////
  ///////////////////////////////////////////////////////////////

  ////////// PC HARDENING BEHAVIOUR WHEN THERE ARE NO GLITCHES //////////

  sequence seq_dummy_if_id;

    //Generate a dummy instruction
    xsecure_if.core_if_stage_instr_meta_n_dummy

    //Make sure the PC of ID and IF stage is equal when there is a dummy instruction in the ID stage
    ##1 (xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc)[*1:$];
  endsequence

  sequence seq_pc_set_stable;

    //Set the PC value to a given address
    xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_ctrl_fsm_i_pc_set

    //Make sure the PC in the IF stage remains the same until it is forwarded to the id stage (and then either incremented or set of a new valid PC jump)
    //(Uses ##2 because: In the first clock cycle the FSM signal has "reached" IF, while in the second clock cycle its stability can be checked)
    ##2 $stable(xsecure_if.core_i_if_stage_i_pc_if_o)[*1:$];
  endsequence


  a_xsecure_pc_hardening_no_glitch: assert property (
    @(posedge xsecure_if.core_clk)

    //Make sure we look at valid cycles
    core_clock_cycles

    //Make sure the PC hardening setting is on
    && xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening

    //Make sure the inspected instruction is valid
    && $past(xsecure_if.core_if_stage_if_valid_o)
    && $past(xsecure_if.core_if_stage_id_ready_i)

    //In case of multi cycled instructions, make sure the instruction is the last operation
    && xsecure_if.core_i_if_id_pipe_last_op

    //Make sure the instruction is not a pointer (as pointers insert a non-incremental PC)
    && !xsecure_if.core_i_if_stage_i_ptr_in_if_o

    |->
    //Correct behavior requires that one of the following behaviors are true:

    //Incremental behavior as compressed or non-compressed instruction
    xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc + CMPR_INSTRUCTION_INCREMENT && $past(xsecure_if.core_i_if_stage_i_compressed_decoder_i_is_compressed_o)
    or xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc + NON_CMPR_INSTRUCTION_INCREMENT && $past(!xsecure_if.core_i_if_stage_i_compressed_decoder_i_is_compressed_o)

    //Initialization after reset
    or xsecure_if.core_i_if_stage_i_pc_if_o == 0 && xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc == 0

    //Insertion of a dummy instruction
    or seq_dummy_if_id.triggered

    //PC jumping
    or seq_pc_set_stable.triggered

    //PC jumping
    or $past(xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_ctrl_fsm_i_pc_set)

  ) else `uvm_error(info_tag, "There is a PC fault in the IF stage.\n");


  ////////// PC HARDENING SET THE MAJOR ALERT IF GLITCH //////////

  sequence seq_xsecure_pc_hardening_with_glitch;
    @(posedge xsecure_if.core_clk)

    //Make sure we look at valid cycles
    core_clock_cycles

    //Make sure the inspected instruction is valid
    && $past(xsecure_if.core_if_stage_if_valid_o)
    && $past(xsecure_if.core_if_stage_id_ready_i)

    //In case of multi cycled instructions, make sure the instruction is the last operation
    && xsecure_if.core_i_if_id_pipe_last_op

    //Make sure the instruction is not a pointer
    && !xsecure_if.core_i_if_stage_i_ptr_in_if_o

    //Make sure it is not icremental behaviour
    and !(xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc + CMPR_INSTRUCTION_INCREMENT && $past(xsecure_if.core_i_if_stage_i_compressed_decoder_i_is_compressed_o))

    and !(xsecure_if.core_i_if_stage_i_pc_if_o == xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc + NON_CMPR_INSTRUCTION_INCREMENT && $past(!xsecure_if.core_i_if_stage_i_compressed_decoder_i_is_compressed_o))

    //Make sure the non-incremental pc is not caused by any of the following reasons:

    //Initialization after reset
    and !(xsecure_if.core_i_if_stage_i_pc_if_o == 0 && xsecure_if.core_i_id_stage_i_if_id_pipe_i_pc == 0)

    //Insertion of a dummy instruction
    and !(seq_dummy_if_id.triggered)

    //PC jumping
    and !(seq_pc_set_stable.triggered)

    //PC jumping
    and !($past(xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_ctrl_fsm_i_pc_set));

  endsequence

  //TODO: look into this assertion after a potential RTL fix
  /*
  a_xsecure_pc_hardening_sets_alert_major: assert property (
    //Make sure the PC hardening setting is on
    xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening
    ##0 seq_xsecure_pc_hardening_with_glitch
    |=>
    //Make sure the alert major is set
    xsecure_if.core_alert_major_o
  ) else `uvm_error(info_tag, "A PC fault in the IF stage does not set the major alert when PC hardening is on.\n");
  */

  ////////// PC HARDENING OFF: DO NOT SET THE MAJOR ALERT IF GLITCH //////////

  //TODO: recheck this assertion when the RTL code related to pc_hadening=0 is implemented
  /*
  a_xsecure_pc_hardening_off_dont_set_alert_major: assert property (
    //Make sure the PC hardening setting is off
    !xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening
    ##0 seq_xsecure_pc_hardening_with_glitch
    |=>
    //Make sure the alert major is not set
    !xsecure_if.core_alert_major_o
  ) else `uvm_error(info_tag, "A PC fault in the IF stage does set the major alert when PC hardening is off.\n");
  */

  ////////// PC HARDENING ON: SET THE MAJOR ALERT IF GLITCH IN PC TARGET //////////

  sequence seq_pc_hardening_jump_instruction_with_glitch(pc_hardening, fsm_state, calculated_signal);

    //Make sure pc hardening setting is set
    pc_hardening

    //Make sure the FSM is in a given state
    && xsecure_if.core_i_if_stage_i_pc_check_i_ctrl_fsm_i_pc_mux == fsm_state

    //Make sure the PC is set
    ##1 xsecure_if.core_i_if_stage_i_pc_check_i_pc_set_q

    //Make sure the calculated signal differs in the hardened cycles
    && calculated_signal != $past(calculated_signal);

  endsequence


  a_xsecure_pc_hardening_branch_set_alert_major: assert property(
    seq_pc_hardening_jump_instruction_with_glitch(xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening, BRANCH_STATE, xsecure_if.core_i_ex_stage_i_branch_target_o)
    |->
    xsecure_if.core_alert_major_o
  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed branch instruction does not set the major alert.\n");

  a_xsecure_pc_hardening_jump_set_alert_major: assert property(
    seq_pc_hardening_jump_instruction_with_glitch(xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening, JUMP_STATE, xsecure_if.core_i_jump_target_id)
    |->
    xsecure_if.core_alert_major_o
  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed jump instruction does not set the major alert.\n");

  a_xsecure_pc_hardening_mret_set_alert_major: assert property(
    seq_pc_hardening_jump_instruction_with_glitch(xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening, MRET_STATE, xsecure_if.core_i_cs_registers_i_mepc_o)
    |->
    xsecure_if.core_alert_major_o
  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed mret instruction does not set the major alert.\n");


  ////////// PC HARDENING ON: SET THE MAJOR ALERT IF GLITCH IN BRANCH DECISION //////////

  sequence seq_pc_hardening_branch_decision_glitch(pc_hardening);

    //Make sure pc hardening setting is on
    xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening

    //Make sure the FSM is doing a branching operation
    && xsecure_if.core_i_if_stage_i_pc_check_i_ctrl_fsm_i_pc_mux == BRANCH_STATE

    //Make sure the branch decision differs in the hardened cycles
    ##1 xsecure_if.core_i_ex_stage_i_alu_i_cmp_result_o != $past(xsecure_if.core_i_ex_stage_i_alu_i_cmp_result_o)

    //Make sure the branch decision is not always taken
    && !xsecure_if.core_xsecure_ctrl_cpuctrl_dataindtiming;

  endsequence


  a_xsecure_pc_hardening_branch_decision_set_alert_major: assert property(

    seq_pc_hardening_branch_decision_glitch(xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening)

    |=>

    //Make sure the alert major was/is set
    xsecure_if.core_alert_major_o
    || $past(xsecure_if.core_alert_major_o)

  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed branch decision does not set the major alert.\n");


  ////////// PC HARDENING OFF: DO NOT SET THE MAJOR ALERT IF GLITCH IN PC TARGET //////////

  //TODO: recheck property when RTL for PC_hardnine == 0 is implemented

  property p_xsecure_hardened_pc_non_sequential_dont_set_major_alert(pc_hardening, fsm_state, calculated_signal);

    seq_pc_hardening_jump_instruction_with_glitch(pc_hardening, fsm_state, calculated_signal)

    |=>
    //Make sure the alert major is not set
    !xsecure_if.core_alert_major_o;

  endproperty

  a_xsecure_pc_hardening_off_branch_set_alert_major: assert property(
    p_xsecure_hardened_pc_non_sequential_dont_set_major_alert(!xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening, BRANCH_STATE, xsecure_if.core_i_ex_stage_i_branch_target_o)
  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed branch instruction (jump location) sets the major alert even though PC hardening is off.\n");

  a_xsecure_pc_hardening_off_jump_set_alert_major: assert property(
    p_xsecure_hardened_pc_non_sequential_dont_set_major_alert(!xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening, JUMP_STATE, xsecure_if.core_i_jump_target_id)
  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed jump instruction sets the major alert even though PC hardening is off.\n");

  a_xsecure_pc_hardening_off_mret_set_alert_major: assert property(
    p_xsecure_hardened_pc_non_sequential_dont_set_major_alert(!xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening, MRET_STATE, xsecure_if.core_i_cs_registers_i_mepc_o)
  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed mret instruction sets the major alert even though PC hardening is off.\n");


  ////////// PC HARDENING OFF: DO NOT SET THE ALERT MAJOR IF GLITCH IN THE BRANCH DECISION //////////

  a_xsecure_pc_hardening_off_branch_decision_set_alert_major: assert property(

    seq_pc_hardening_branch_decision_glitch(!xsecure_if.core_xsecure_ctrl_cpuctrl_pc_hardening)

    |=>
    //Make sure the alert major was/is not set
    !xsecure_if.core_alert_major_o
    && !$past(xsecure_if.core_alert_major_o)

  ) else `uvm_error(info_tag, "Mismatch between the computed and the recomputed branch instruction (decision calculation) sets the major alert even though PC hardening is off.\n");


  //////////////////////////////////////////////////////////////////////////////
  ///////////////////////// DUMMY AND HINT INSTRUCTION /////////////////////////
  //////////////////////////////////////////////////////////////////////////////

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
    //Make sure the gated clock is active
    @(posedge xsecure_if.core_clk)

    //Make sure that mcycle is operative (not inhibited)
    !xsecure_if.core_cs_registers_mcountinhibit_q_mcycle_inhibit

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
    //Make sure the gated clock is active
    @(posedge xsecure_if.core_clk)

    //Make sure minstret is operative (not inhibited)
    !xsecure_if.core_cs_registers_mcountinhibit_q_minstret_inhibit

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
    //Make sure the gated clock is active
    @(posedge xsecure_if.core_clk)

    //Make sure that minstret is operative (not inhibited)
    !xsecure_if.core_cs_registers_mcountinhibit_q_minstret_inhibit

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
    //Make sure the gated clock is active
    @(posedge xsecure_if.core_clk)

    //Make sure there is a hint instruction in the WB stage
    xsecure_if.core_ex_wb_pipe_instr_meta_hint

    //Make sure we retire the hint instruction in the next cycle
    ##1 rvfi_if.rvfi_valid

    |->
    //Verify that the hint instruction appears as c.slli instruction with rd=x0 and shamt != 0
    rvfi_insn_cmpr_funct3 == FUNCT3_COMPR_SLLI
    && rvfi_insn_cmpr_opcode == OPCODE_COMPR_SLLI
    && rvfi_if.rvfi_rd1_addr == REGISTER_x0
    && rvfi_c_slli_shamt != '0

  ) else `uvm_error(info_tag, "Hint instruction do not appears as a c.slli instruction with rd=x0 and shamt != 0 on RVFI.\n");



  //////////////////////////////////////////////////////////////////////////
  ///////////////////////// BUS PROTOCOL HARDENING /////////////////////////
  //////////////////////////////////////////////////////////////////////////

  ////////// BUS PROTOCOL HARDENING BEHAVIOUR WHEN THERE ARE NO GLITCHES //////////

  property p_resp_after_addr_no_glitch(obi_rvalid, resp_ph_cont, v_addr_ph_cnt);
    @(posedge xsecure_if.core_clk)

    //Make sure the core is in an operative state
    core_clock_cycles

    //Make sure there is a response phase transfer
    && obi_rvalid

    //Make sure the response phase transfer is finished
    && !resp_ph_cont

    |->
    //Check that the response phase transfer is indeed a response to an address transfer (in other words, that there at least exists one active address transfer)
    v_addr_ph_cnt > 0;

  endproperty;

  a_xsecure_bus_hardening_resp_after_addr_no_glitch_data: assert property (
    p_resp_after_addr_no_glitch(
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid,
      support_if.data_bus_resp_ph_cont,
      support_if.data_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "There is a response before a request in the OBI data bus handshake.\n");

  a_xsecure_bus_hardening_resp_after_addr_no_glitch_instr: assert property (
    p_resp_after_addr_no_glitch(
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalid,
      support_if.instr_bus_resp_ph_cont,
      support_if.instr_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "There is a response before a request in the OBI instruction bus handshake.\n");

  a_xsecure_bus_hardening_resp_after_addr_no_glitch_abiim: assert property (
    p_resp_after_addr_no_glitch(
      xsecure_if.core_i_if_stage_i_prefetch_resp_valid,
      support_if.abiim_bus_resp_ph_cont,
      support_if.abiim_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "There is a response before a request in the handshake between alignmentbuffer (ab) and instructoin (i) interface (i) mpu (m).\n");

  a_xsecure_bus_hardening_resp_after_addr_no_glitch_lml: assert property (
    p_resp_after_addr_no_glitch(
      xsecure_if.core_i_load_store_unit_i_resp_valid,
      support_if.lml_bus_resp_ph_cont,
      support_if.lml_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "There is a response before a request in the handshake between LSU (l) MPU (m) and LSU (l).\n");

  a_xsecure_bus_hardening_resp_after_addr_no_glitch_lrfodi: assert property (
    p_resp_after_addr_no_glitch(
      xsecure_if.core_i_load_store_unit_i_bus_resp_valid,
      support_if.lrfodi_bus_resp_ph_cont,
      support_if.lrfodi_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "There is a response before a request in the handshake between LSU (l) respons (r) filter (f) and the OBI (o) data (d) interface (i).\n");


  ////////// BUS PROTOCOL HARDENING BEHAVIOUR COUNTER DO NOT UNDERFLOW //////////

  a_xsecure_bus_hardening_counter_dont_underflow: assert property (

    //Make sure the counter is in a position where it can underflow
    xsecure_if.core_i_load_store_unit_i_response_filter_i_core_cnt_q == 0

    |=>
    //Make sure the counter either stays 0
    xsecure_if.core_i_load_store_unit_i_response_filter_i_core_cnt_q == 0

    //Or count upwards
    || xsecure_if.core_i_load_store_unit_i_response_filter_i_core_cnt_q == 1

  ) else `uvm_error(info_tag, "The counter underflows.\n");


  ////////// BUS PROTOCOL HARDENING BEHAVIOUR WHEN THERE ARE GLITCHES //////////

  property p_resp_after_addr_glitch(obi_rvalid, resp_ph_cont, v_addr_ph_cnt);
    @(posedge xsecure_if.core_clk)

    //Make sure the core is in an operative state
    core_clock_cycles

    //Make sure major alert is not or has not been set
    && !alert_major_was_set && !xsecure_if.core_alert_major_o

    //Make sure there is a response phase transfer
    && obi_rvalid

    //Make sure the response phase transfer is finished
    && !resp_ph_cont

    //Make sure there are no active address transfers the response transfer could be correlated with
    && v_addr_ph_cnt == 0

    |=>
    //Check the major alert is set
    xsecure_if.core_alert_major_o;
  endproperty;

  a_xsecure_bus_hardening_resp_after_addr_glitch_data: assert property (
    p_resp_after_addr_glitch(
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid,
      support_if.data_bus_resp_ph_cont,
      support_if.data_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "A response before a request in the OBI data bus handshake does not set the major alert.\n");

  a_xsecure_bus_hardening_resp_after_addr_glitch_instr: assert property (
    p_resp_after_addr_glitch(
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalid,
      support_if.instr_bus_resp_ph_cont,
      support_if.instr_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "A response before a request in the OBI instruction bus handshake does not set the major alert.\n");

  a_xsecure_bus_hardening_resp_after_addr_glitch_abiim: assert property (
    p_resp_after_addr_glitch(
      xsecure_if.core_i_if_stage_i_prefetch_resp_valid,
      support_if.abiim_bus_resp_ph_cont,
      support_if.abiim_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "A response before a request in the handshake between alignmentbuffer (ab) and instructoin (i) interface (i) mpu (m) does not set the major alert.\n");

  a_xsecure_bus_hardening_resp_after_addr_glitch_lml: assert property (
    p_resp_after_addr_glitch(
      xsecure_if.core_i_load_store_unit_i_resp_valid,
      support_if.lml_bus_resp_ph_cont,
      support_if.lml_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "A response before a request in the handshake between LSU (l) MPU (m) and LSU (l) does not set the major alert.\n");

  a_xsecure_bus_hardening_resp_after_addr_glitch_lrfodi: assert property (
    p_resp_after_addr_glitch(
      xsecure_if.core_i_load_store_unit_i_bus_resp_valid,
      support_if.lrfodi_bus_resp_ph_cont,
      support_if.lrfodi_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "A response before a request in the handshake between LSU (l) respons (r) filter (f) and the OBI (o) data (d) interface (i) does not set the major alert.\n");


  ////////// BUS PROTOCOL HARDENING BEHAVIOUR COUNTER UNDERFLOW SET THE MAJOR ALERT //////////

  a_xsecure_bus_hardening_counter_overflow_set_major_alert: assert property (

    //Make sure the core is in an operative state
    core_clock_cycles

    //Make sure the counter is in a position where it can underflow
    && (xsecure_if.core_i_load_store_unit_i_response_filter_i_core_cnt_q == 0)

    //Make sure the counter underflows
    ##1 xsecure_if.core_i_load_store_unit_i_response_filter_i_core_cnt_q != 0
    && xsecure_if.core_i_load_store_unit_i_response_filter_i_core_cnt_q != 1

    |->
    //Verify that alert major is set
    xsecure_if.core_alert_major_o
  ) else `uvm_error(info_tag, "The counter underflows but does not set the major alert.\n");



endmodule : uvmt_cv32e40s_xsecure_assert
