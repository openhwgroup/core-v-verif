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


module uvmt_cv32e40s_xsecure_security_alerts_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
    uvma_rvfi_instr_if_t rvfi_if,
    uvmt_cv32e40s_support_logic_module_o_if_t.slave_mp support_if,
    input rst_ni,
    input clk_i,

    //alerts:
    input logic alert_minor,
    input logic alert_major,

    //wb:
    input wb_valid,
    input exception_in_wb,
    input [10:0] exception_cause_wb,

    //dummy and hint:
    input logic dummy_en,
    input logic hint_en,
    input logic lfsr0_clock_en,
    input logic lfsr1_clock_en,
    input logic lfsr2_clock_en,
    input logic seed0_we,
    input logic seed1_we,
    input logic seed2_we,
    input logic [31:0]seed0_i,
    input logic [31:0]seed1_i,
    input logic [31:0]seed2_i,
    input logic [31:0]lfsr0_n,
    input logic [31:0]lfsr1_n,
    input logic [31:0]lfsr2_n,

    //OBI:
    input logic obi_data_rvalid,
    input logic obi_data_err,

    //NMI:
    input logic nmip,

    //debug:
    input logic debug_mode
  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) || !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";

  // Local parameters:
  localparam NO_LOCKUP_ERRORS = 3'b000;

  localparam INSTRUCTION_ACCESS_FAULT = 11'd1;
  localparam ILLEGAL_INSTRUCTION_FAULT = 11'd2;
  localparam LOAD_ACCESS_FAULT = 11'd5;
  localparam STORE_AMO_ACCESS_FAULT = 11'd7;
  localparam INSTRUCTION_BUS_FAULT = 11'd24;

  function logic detect_lockup_error;
    input logic dummy_en, hint_en, clock_en, seed_we;
    input logic [31:0] seed_i, lfsr_n;

    detect_lockup_error = (dummy_en || hint_en) && clock_en && ((!seed_we && lfsr_n == '0) || (seed_we && seed_i == '0));
  endfunction

  logic lfsr0_lockup_error_detected;
  logic lfsr1_lockup_error_detected;
  logic lfsr2_lockup_error_detected;

  assign lfsr0_lockup_error_detected = detect_lockup_error(dummy_en, hint_en, lfsr0_clock_en, seed0_we, seed0_i, lfsr0_n);
  assign lfsr1_lockup_error_detected = detect_lockup_error(dummy_en, hint_en, lfsr1_clock_en, seed1_we, seed1_i, lfsr1_n);
  assign lfsr2_lockup_error_detected = detect_lockup_error(dummy_en, hint_en, lfsr2_clock_en, seed2_we, seed2_i, lfsr2_n);

  logic triggering_minor_alert_due_to_non_nmi_exceptions;
  assign triggering_minor_alert_due_to_non_nmi_exceptions = wb_valid && exception_in_wb
    && (exception_cause_wb == INSTRUCTION_ACCESS_FAULT
    || exception_cause_wb == ILLEGAL_INSTRUCTION_FAULT
    || exception_cause_wb == LOAD_ACCESS_FAULT
    || exception_cause_wb == STORE_AMO_ACCESS_FAULT
    || exception_cause_wb == INSTRUCTION_BUS_FAULT);


  //Verify that LFSR lockups set the minor alert:

  a_xsecure_security_alert_lfsr0_lockup: assert property (
    lfsr0_lockup_error_detected
    |=>
    alert_minor
  ) else `uvm_error(info_tag, "LFSR0 Lookup error does not set the minor alert.\n");

  a_xsecure_security_alert_lfsr1_lockup: assert property (
    lfsr1_lockup_error_detected
    |=>
    alert_minor
  ) else `uvm_error(info_tag, "LFSR0 Lookup error does not set the minor alert.\n");

  a_xsecure_security_alert_lfsr2_lockup: assert property (
    lfsr2_lockup_error_detected
    |=>
    alert_minor
  ) else `uvm_error(info_tag, "LFSR0 Lookup error does not set the minor alert.\n");


  //Verify that the minor alert is set when triggering (non-NMI) exceptions:
  //- instruction access fault
  //- illegal instruction fault
  //- load access fault
  //- store/AMO access fault
  //- instruction bus fault

  a_xsecure_security_alert_non_nmi_exceptions: assert property (
    triggering_minor_alert_due_to_non_nmi_exceptions
    |=>
    alert_minor

    //By entering debug we will not trigger exceptions
    || $rose(debug_mode)

  ) else `uvm_error(info_tag, "Exception does not set the minor alert.\n");


  //Verify that minor alert is set when handeling a triggered store/load bus fault NMI
  //If there is an NMI fault, but there is a NMI that is not yet handeld, the NMI-status is not updated.

  property p_set_nmip_no_integrity;

    obi_data_rvalid
    && obi_data_err
    && !support_if.data_req_had_integrity

    |=>
    $rose(nmip) || $past(nmip);

  endproperty

  property p_nmip_no_integrity;

    obi_data_rvalid
    && obi_data_err
    && !support_if.data_req_had_integrity
    ##1 $rose(nmip)

    //Wait for the pending NMI to be handeled
    ##1 (!nmip)[->1]

    |->
    alert_minor;

  endproperty

  a_xsecure_security_alert_nmi_no_integrity: assert property (
    p_set_nmip_no_integrity
    and p_nmip_no_integrity
  ) else `uvm_error(info_tag, "A store/load bus fault NMI does not set the alert minor when the NMI is handeled.\n");


  //Verify that minor alert is set only due to the LFSR lockup detections, the exceptions listed above, and NMI fault due to buss error without integrity

  a_xsecure_security_alert_minor_reasons: assert property (

    alert_minor

    |->
    ($past(lfsr0_n) == '0
    || $past(lfsr1_n) == '0
    || $past(lfsr2_n) == '0
    || $past(seed0_i) == '0
    || $past(seed1_i) == '0
    || $past(seed2_i) == '0)

    or $past(triggering_minor_alert_due_to_non_nmi_exceptions)

    or $past(nmip)

  ) else `uvm_error(info_tag, "TODO!.\n");


  //Verify that the major alert is never set

  a_xsecure_security_alert_major: assert property (
    !alert_major
  ) else `uvm_error(info_tag, "The mjor alert is set even though there should be no glitches.\n");

  endmodule : uvmt_cv32e40s_xsecure_security_alerts_assert
