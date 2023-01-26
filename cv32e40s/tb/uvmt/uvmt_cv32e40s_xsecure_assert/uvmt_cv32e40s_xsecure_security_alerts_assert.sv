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

    // Local parameters:
  localparam NO_LOCKUP_ERRORS = 3'b000;

  localparam ERROR_CODE_INSTRUCTION_ACCESS_FAULT = 6'd1;
  localparam ERROR_CODE_ILLEGAL_INSTRUCTION_FAULT = 6'd2;
  localparam ERROR_CODE_LOAD_ACCESS_FAULT = 6'd5;
  localparam ERROR_CODE_STORE_AMO_ACCESS_FAULT = 6'd7;
  localparam ERROR_CODE_INSTRUCTION_BUS_FAULT = 6'd24;


  ////////// SECURITY ALERTS MINOR DUE TO LFSR LOCKUPS //////////

  a_xsecure_security_alert_minor_LFSR_lockups: assert property (

    //Make sure we detect LFSR lockup
    xsecure_if.core_cs_registers_xsecure_lfsr_lockup != NO_LOCKUP_ERRORS

    |=>
    //Make sure the alert minor is set
    xsecure_if.core_alert_minor_o

  ) else `uvm_error(info_tag, "Lookup errors do not set the minor alert.\n");


  ////////// SECURITY ALERTS MINOR DUE TO NMI FAULTS //////////

  a_xsecure_security_alert_minor_access_bus_and_illegal_instruction_faults: assert property (

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

    |->
    //The error is handled in the WB stage and notifies the alert minor signal in the next stage (which is the current/rvfi stage)
    xsecure_if.core_alert_minor_o

  ) else `uvm_error(info_tag, "Exception errors do not set the minor alert.\n");


  ////////// SECURITY ALERTS MINOR DUE TO NMI FAULTS //////////

  //This assertion proves that the pending NMI signal is set whenever there is a bus fault on the OBI data bus
  //Or that alert minor is already set due to a previous bus fault on the OBI data bus
  a_xsecure_security_alert_minor_nmi_fault_helper_assertion: assert property (

    //Make sure we receive a valid instruction packet on the OBI instruction bus
    xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid

    //Make sure there the OBI instruction bus indicates that there is an error related to the received packet
    && xsecure_if.core_i_data_err_i

    //Make sure the received packet does not have integrity
    && !support_if.data_req_had_integrity

    |=>
    //Verify that the pending NMI signal is set
    xsecure_if.core_i_controller_i_controller_fsm_i_pending_nmi

    //Or that the minor alert is set due to a previous bus fault
    || ($past(xsecure_if.core_i_controller_i_controller_fsm_i_pending_nmi) && xsecure_if.core_alert_minor_o)

  ) else `uvm_error(info_tag, "A bus fault on the data OBI bus does not set the pending NMI signal high (in the case where the minor alert is not already high due to a previous bus error).\n");


  //Helper signal that specifies that the core is in a state where interrupts are enabled
  //In other words, making sure the core is not in debug mode or single stepping mode where interrupts are disabled
  logic core_state_with_interrupts_enabled;
  assign core_state_with_interrupts_enabled = !xsecure_if.core_controller_controller_fsm_debug_mode_q && ((!xsecure_if.core_i_controller_i_controller_fsm_i_dcsr_i_step) || (xsecure_if.core_i_controller_i_controller_fsm_i_dcsr_i_step && xsecure_if.core_i_controller_i_controller_fsm_i_dcsr_i_stepie));

  a_xsecure_security_alert_minor_nmi_fault: assert property (

    //Make sure we receive a valid instruction packet on the OBI instruction bus
    xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid

    //Make sure there the OBI instruction bus indicates that there is an error related to the received packet
    && xsecure_if.core_i_data_err_i

    //Make sure the received packet does not have integrity
    && !support_if.data_req_had_integrity

    //Make sure we investigate a scene where the core is not already handling a previous bus fault (see the helper assertion above)
    ##1 xsecure_if.core_i_controller_i_controller_fsm_i_pending_nmi

    |=>
    //Verify that the minor alert is set after a maximum of two instructions have retired in an interruptable operating mode (not debug mode or single stepping mode without interrupts)

    //Allow a maximum of two instructions to retire when the core is in an interruptable operating state
    (core_state_with_interrupts_enabled && rvfi_if.rvfi_valid)[->0:2]

    //Verify that there are no more instructions that retire when the core is in in interruptable operating state before the minor alert is set
    ##1 !(core_state_with_interrupts_enabled && rvfi_if.rvfi_valid)[*0:$]
    ##1 xsecure_if.core_alert_minor_o

  ) else `uvm_error(info_tag, "A bus fault on the OBI data bus does not set the minor alert in non-debug and non-single-stepping mode.\n");


  endmodule : uvmt_cv32e40s_xsecure_security_alerts_assert