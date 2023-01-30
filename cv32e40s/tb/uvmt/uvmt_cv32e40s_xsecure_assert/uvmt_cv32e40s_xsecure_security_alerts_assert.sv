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


module uvmt_cv32e40s_xsecure_security_alerts_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
   uvmt_cv32e40s_xsecure_if xsecure_if,
   uvma_rvfi_instr_if rvfi_if,
   uvmt_cv32e40s_support_logic_for_assert_coverage_modules_if.slave_mp support_if,
   input rst_ni,
   input clk_i
  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) | !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";
  string info_tag_glitch = "CV32E40S_XSECURE_ASSERT_COVERPOINTS (GLITCH BEHAVIOR)";

    // Local parameters:
  localparam NO_LOCKUP_ERRORS = 3'b000;

  localparam ERROR_CODE_INSTRUCTION_ACCESS_FAULT = 6'd1;
  localparam ERROR_CODE_ILLEGAL_INSTRUCTION_FAULT = 6'd2;
  localparam ERROR_CODE_LOAD_ACCESS_FAULT = 6'd5;
  localparam ERROR_CODE_STORE_AMO_ACCESS_FAULT = 6'd7;
  localparam ERROR_CODE_INSTRUCTION_BUS_FAULT = 6'd24;


  ////////// THE SECURITY ALERT MINOR IS SET DUE TO LFSR LOCKUP DETECTION //////////

  sequence p_xsecure_dummy_hint_instruction_LFSRx_lockup_detection(logic get_new_lfsr_value, logic seed_we, logic [31:0] seed_value, logic [31:0] lfsrx_n);

    (xsecure_if.core_xsecure_ctrl_cpuctrl_rnddummy || xsecure_if.core_xsecure_ctrl_cpuctrl_rndhint)
    throughout
    (get_new_lfsr_value
    && ((!seed_we && lfsrx_n == '0)
    || (seed_we && seed_value == '0)));
  endsequence

  //LFSR0
  a_xsecure_dummy_hint_instruction_LFSR0_lockup_set_minor_alert: assert property (
	  p_xsecure_dummy_hint_instruction_LFSRx_lockup_detection(
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_clock_en,
      xsecure_if.core_cs_registers_xsecure_lfsr0_seed_we,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_seed_i,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_lfsr_n)

    |=>
	  //Make sure the the alert minor is set
    xsecure_if.core_alert_minor_o
  ) else `uvm_error(info_tag, "Lookup error on LFSR0 does not set the minor alert.\n");

  //LFSR1
  a_xsecure_dummy_hint_instruction_LFSR1_lockup_set_minor_alert: assert property (
	  p_xsecure_dummy_hint_instruction_LFSRx_lockup_detection(
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_clock_en,
      xsecure_if.core_cs_registers_xsecure_lfsr1_seed_we,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_seed_i,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_lfsr_n)

    |=>
	  //Make sure the the alert minor is set
    xsecure_if.core_alert_minor_o
  ) else `uvm_error(info_tag, "Lookup error on LFSR1 does not set the minor alert.\n");


  //LFSR2
  a_xsecure_dummy_hint_instruction_LFSR2_lockup_set_minor_alert: assert property (
	  p_xsecure_dummy_hint_instruction_LFSRx_lockup_detection(
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_clock_en,
      xsecure_if.core_cs_registers_xsecure_lfsr2_seed_we,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_seed_i,
      xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_lfsr_n)

    |=>
	  //Make sure the the alert minor is set
    xsecure_if.core_alert_minor_o
  ) else `uvm_error(info_tag, "Lookup error on LFSR2 does not set the minor alert.\n");


  ////////// SECURITY ALERTS MINOR DUE TO NMI FAULTS //////////

  sequence seq_exceptions_that_set_minor_alert;
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
    || rvfi_if.rvfi_trap.exception_cause == ERROR_CODE_INSTRUCTION_BUS_FAULT);
    endsequence

  a_xsecure_security_alert_minor_access_bus_and_illegal_instruction_faults: assert property (
    //Make sure we have encoutntered an exception that sets minor alert
    seq_exceptions_that_set_minor_alert

    |->
    //The error is handled in the WB stage and notifies the alert minor signal in the next stage (which is the current/rvfi stage)
    xsecure_if.core_alert_minor_o

  ) else `uvm_error(info_tag, "Exception does not set the minor alert.\n");


  //Added check for corner case:
  a_xsecure_security_alert_minor_is_not_set_when_entering_debug_instead_of_triggering_exceptions: assert property (

    //Make sure we look at a valid instruction
    rvfi_i.rvfi_valid == 1'b1

    //Make sure the instruction is not executed but rather sends the core into debug mode
    && rvfi_i.rvfi_trap.debug_cause == 3'd2

    |->
    //Verify that minor alert is not set as we have not triggered any exceptions
    xsecure_if.core_alert_minor_o == 1'b0

    //Exlpination of why there is no need to exclude other reasons that set minor alert.
    //We have entered debug mode. This means that all pipeline stages are killed.
    //- LFSR will therefore not be updated
    //- NMIs will not be handeld
    //- And exceptions will not be handled

  ) else `uvm_error(info_tag, "The alert minor is set eventhoug we have entered debug mode, and should not have triggered any exceptions.\n");


  ////////// THE SECURITY ALERT MINOR IS SET DUE TO HANDELED STORE/LOAD NMI FAULTS //////////

  property p_obi_data_error_set_dcsr_nmip;

    //Make sure we receive a valid data packet on the OBI data bus
    xsecure_if.core_i_data_rvalid_i

    //Make sure there the OBI data bus indicates that there is an error related to the received packet
    && xsecure_if.core_i_data_err_i

    //Make sure the received packet does not have integrity
    && !support_if.data_req_had_integrity

    |=>
    //Verify that the pending NMI signal is set
    xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip

    //Or that it was already set
    || $past(xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip);

  endproperty


  property p_dcsr_nmip_set_minor_alert_when_handeled_and_without_integrity;

    //Make sure we receive a valid instruction packet on the OBI instruction bus
    xsecure_if.core_i_data_rvalid_i

    //Make sure there the OBI instruction bus indicates that there is an error related to the received packet
    && xsecure_if.core_i_data_err_i

    //Make sure the received packet does not have integrity
    && !support_if.data_req_had_integrity

    //Make sure we investigate a scene where the NMI signal gets set
    ##1 xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip

    |=>
    //Verify that minor alert is set high when the NMI is handeled
    xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip[*0:$]
    ##1 !xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip && xsecure_if.core_alert_minor_o;

  endproperty

  a_xsecure_security_set_nmi_when_obi_data_error: assert property (
    p_obi_data_error_set_dcsr_nmip
  ) else `uvm_error(info_tag, "A store/load bus fault NMI does not set the alert minor when the NMI is handeled.\n");

  a_xsecure_security_set_minor_alert_when_handling_obi_data_error_nmi: assert property (
    p_dcsr_nmip_set_minor_alert_when_handeled_and_without_integrity
  ) else `uvm_error(info_tag, "A store/load bus fault NMI does not set the alert minor when the NMI is handeled.\n");


  ////////// THE SECURITY ALERT MINOR IS ONLY SET DUE TO THE REASONS INVESTIGATED ABOVE //////////

  a_xsecure_security_alert_minor_reasons: assert property (

    //Make sure we detect a minor alert
    xsecure_if.core_alert_minor_o

    |->
    //Verify that minor alert is set only due to the reasons specified in the specification:

    //We are detection potensial lockup error
    ($past(xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_lfsr_n) == '0
    || $past(xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_lfsr_n) == '0
    || $past(xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_lfsr_n) == '0
    || $past(xsecure_if.core_i_cs_registers_i_xsecure_lfsr0_i_seed_i) == '0
    || $past(xsecure_if.core_i_cs_registers_i_xsecure_lfsr1_i_seed_i) == '0
    || $past(xsecure_if.core_i_cs_registers_i_xsecure_lfsr2_i_seed_i) == '0)

    //Exception
    or seq_exceptions_that_set_minor_alert

    //NMI fault
    or $past(xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip)

  ) else `uvm_error(info_tag, "Lookup errors do not set the minor alert.\n");


  ////////// THE SECURITY ALERT MAJOR IS CLEARD IF THERE ARE NO GLITCHES //////////

  a_xsecure_security_alert_major_is_off_when_no_glitches: assert property (
    !xsecure_if.core_alert_major_o
  ) else `uvm_error(info_tag, "MThe mjor alert is set even though there should be no glitches.\n");

  endmodule : uvmt_cv32e40s_xsecure_security_alerts_assert