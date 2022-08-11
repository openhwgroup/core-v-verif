module uvmt_cv32e40s_xsecure_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
   uvmt_cv32e40s_xsecure_cov_assert_if cov_assert_if
   //uvma_rvfi_instr_if rvfi
  // Standard inputs to an assertion module 

  // Data independent timing:
  // input csr_data_independent_timing_i,
  // input logic [6:0] instr_rdata_opcode_i,
  // inout logic intr_rdata_valid
  );

  // SPEC: v1.0_draft00
  // To know what rvfi signals to use: https://github.com/openhwgroup/cv32e40s/blob/master/bhv/cv32e40s_rvfi.sv
  
  // Default settings:
  default clocking @(posedge cov_assert_if.clk_i); endclocking 
  string info_tag = "CV32E40S_XSECURE_ASSERT";
  
  //sequences:
  sequence operation (logic [7:0] func7, logic [3:0] func3, logic [6:0] opcode);
    cov_assert_if.rvfi_insn[6:0] == opcode
    && cov_assert_if.rvfi_insn[14:12] == func3
    && cov_assert_if.rvfi_insn[31:25] == func7;
  endsequence
  
  // Assertions:

  // Data independent timing:
  
  // Default off:
  // R-92.1
  // I: data independent timing setting should be off at default.
  // Q: can SECURE parameter be 1 and 0 in this case?

  property p_xsecure_setting_default_off(logic xsecure_setting);
    $rose(cov_assert_if.rst_ni) 
    |->
    !xsecure_setting;
  endproperty

  a_xsecure_dataindtiming_default_off: assert property (
	  p_xsecure_setting_default_off(
	  cov_assert_if.core_csr_cpuctrl_rdata_dataindtiming)
  ) else `uvm_error(info_tag, "data independent timing should be off when resetting");
 

  a_xsecure_dummy_instruction_default_off: assert property (
	  p_xsecure_setting_default_off(
	  cov_assert_if.core_csr_cpuctrl_rdata_rnddummy)
  ) else `uvm_error(info_tag, "dummy instruction should be off when resetting");

  
  a_xsecure_hint_instruction_default_off: assert property (
	  p_xsecure_setting_default_off(
	  cov_assert_if.core_csr_cpuctrl_rdata_rndhint)
  ) else `uvm_error(info_tag, "hint instruction should be off when resetting");
    
  
  // Branch timing:

    //cov_assert_if.rvfi_csr_mcountinhibit_rdata[0] && 
    //cov_assert_if.rvfi_csr_mcycle_wmask && 

  a_xsecure_branch_timing: assert property (
    ($past(cov_assert_if.core_csr_cpuctrl_rdata_dataindtiming,3)
    || $past(cov_assert_if.core_csr_cpuctrl_rdata_dataindtiming,4))
    && !cov_assert_if.rvfi_trap  
    && cov_assert_if.rvfi_valid  
    && cov_assert_if.rvfi_insn[6:0] == cv32e40s_pkg::OPCODE_BRANCH
    && cov_assert_if.rvfi_csr_mcycle_wmask 
    //&& cov_assert_if.rvfi_csr_mcountinhibit_rdata //Vacuous??
    
    |->  
    //!cov_assert_if.rst_ni //failing
    (cov_assert_if.rvfi_csr_mcycle_wdata[31:0] - cov_assert_if.rvfi_csr_mcycle_rdata[31:0] == 2) 
    || (cov_assert_if.rvfi_csr_mcycle_wdata[31:0] - cov_assert_if.rvfi_csr_mcycle_rdata[31:0] == 3) 

  ) else `uvm_error(info_tag, "General branch timing is not 3 cycles");
/*

  a_xsecure_div_rem_timing: assert property (
    cov_assert_if.core_csr_cpuctrl_rdata_dataindtiming //vacuous
    //&& !cov_assert_if.rvfi_trap  
    //&& cov_assert_if.rvfi_valid  
    //&& cov_assert_if.rvfi_insn[6:0] == cv32e40s_pkg::OPCODE_OP
    //&& cov_assert_if.rvfi_insn[14:12] == 3b'1xx //func3 (DIV and REM)
    //&& cov_assert_if.rvfi_insn[31:..] == 7b'0000001 //func7
    //&& cov_assert_if.rvfi_csr_mcycle_wmask  
    |->  
    //!cov_assert_if.rst_ni //failing
     (cov_assert_if.rvfi_csr_mcycle_wdata - cov_assert_if.rvfi_csr_mcycle_rdata == 35) 

  ) else `uvm_error(info_tag, "General division and remainder timing is not 35 cycles");


  // Tankegang: mcycle skal uansett oppdateres!
  a_xsecure_dummy_instruction_update_mcycle: assert property (
    cov_assert_if.core_csr_cpuctrl_rdata_rnddummy
    && cov_assert_if.rvfi_valid
    && (operation(7b'0000000, 3'b000, cv32e40s_pkg::OPCODE_OP) //ADD
    || operation(7b'0000001, 3'b000, cv32e40s_pkg::OPCODE_OP) //MUL
    || operation(7b'xxxxxxx, 3'b110, cv32e40s_pkg::OPCODE_BRANCH)) //BLTU
    && cov_assert_if.rvfi_csr_mcycle_wmask
    && cov_assert_if.rvfi_csr_mcountinhibit_rdata[0]
    |->  
    cov_assert_if.rvfi_csr_mcycle_wdata != cov_assert_if.rvfi_csr_mcycle_rdata

  ) else `uvm_error(info_tag, "General division and remainder timing is not 35 cycles");
*/

endmodule : uvmt_cv32e40s_xsecure_assert

