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


module uvmt_cv32e40s_xsecure_interface_integrity_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
   uvmt_cv32e40s_xsecure_if xsecure_if,
   uvmt_cv32e40s_support_logic_for_assert_coverage_modules_if.slave_mp support_if,
   input rst_ni,
   input clk_i
  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) | !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";
  string info_tag_glitch = "CV32E40S_XSECURE_ASSERT_COVERPOINTS (GLITCH BEHAVIOR)";

  property p_xsecure_setting_default_on(logic xsecure_setting);

    //Make sure that when exiting reset mode the xsecure setting is off
    $rose(rst_ni)
    |->
    xsecure_setting;
  endproperty

  //Sticky bit that indicates if the major alert has been set.
  logic alert_major_was_set;

  //Sticky bit that indicates if major alert has been set.
  always @(posedge clk_i) begin
    if(!rst_ni) begin
      alert_major_was_set <= 0;
    end else if (xsecure_if.core_alert_major_o) begin
      alert_major_was_set <= xsecure_if.core_alert_major_o;
    end
  end

  // Local parameters:
  localparam ASSUMED_VALUE_BE = 4'b1111;
  localparam ASSUMED_VALUE_WE = 1'b0;
  localparam ASSUMED_VALUE_ATOP = 6'b00_0000;
  localparam ASSUMED_VALUE_WDATA = 32'h0000_0000;
  localparam EXOKAY_TIE_OFF_VALUE = 1'b0;

  // Functions:
  function logic f_achk_error (logic [11:0] achk, logic [31:0] addr, logic [2:0] prot, logic [1:0] memtype, logic [3:0] be, logic we, logic dbg, logic [5:0] atop, logic [31:0] wdata);
    f_achk_error = !(
      achk[0] == ^addr[7:0]
      && achk[1] == ^addr[15:8]
      && achk[2] == ^addr[23:16]
      && achk[3] == ^addr[31:24]
      && achk[4] == ~^{prot[2:0], memtype[1:0]}
      && achk[5] == ~^{be[3:0], we}
      && achk[6] == ~^dbg
      && achk[7] == ^atop[5:0]
      && achk[8] == ^wdata[7:0]
      && achk[9] == ^wdata[15:8]
      && achk[10] == ^wdata[23:16]
      && achk[11] == ^wdata[31:24]);
  endfunction

  function logic f_rchk_error (logic [4:0] rchk, logic err, logic exokay, logic [31:0] rdata);
    f_rchk_error = !(
      rchk[0] == ^rdata[7:0]
      && rchk[1] == ^rdata[15:8]
      && rchk[2] == ^rdata[23:16]
      && rchk[3] == ^rdata[31:24]
      && rchk[4] == ^{err, exokay});
  endfunction

  logic achk_error_data;
  assign achk_error_data = f_achk_error(
    xsecure_if.core_i_m_c_obi_data_if_req_payload.achk,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.addr,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.prot,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.memtype,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.be,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.we,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.dbg,
    ASSUMED_VALUE_ATOP,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.wdata);

  logic achk_error_instr;
  assign achk_error_instr = f_achk_error(
    xsecure_if.core_i_m_c_obi_instr_if_req_payload.achk,
    xsecure_if.core_i_m_c_obi_instr_if_req_payload.addr,
    xsecure_if.core_i_m_c_obi_instr_if_req_payload.prot,
    xsecure_if.core_i_m_c_obi_instr_if_req_payload.memtype,
    ASSUMED_VALUE_BE,
    ASSUMED_VALUE_WE,
    xsecure_if.core_i_m_c_obi_instr_if_req_payload.dbg,
    ASSUMED_VALUE_ATOP,
    ASSUMED_VALUE_WDATA);

  logic rchk_error_instr_read;
  assign rchk_error_instr_read = f_rchk_error(
    xsecure_if.core_i_m_c_obi_instr_if_resp_payload.rchk,
    xsecure_if.core_i_m_c_obi_instr_if_resp_payload.err,
    EXOKAY_TIE_OFF_VALUE,
    xsecure_if.core_i_m_c_obi_instr_if_resp_payload.rdata);

  logic rchk_error_data_read;
  assign rchk_error_data_read = f_rchk_error(
    xsecure_if.core_i_m_c_obi_data_if_resp_payload.rchk,
    xsecure_if.core_i_m_c_obi_data_if_resp_payload.err,
    EXOKAY_TIE_OFF_VALUE,
    xsecure_if.core_i_m_c_obi_data_if_resp_payload.rdata);

  logic rchk_error_data_write;
  assign rchk_error_data_write = (xsecure_if.core_i_m_c_obi_data_if_resp_payload.rchk[4] != ^{xsecure_if.core_i_m_c_obi_data_if_resp_payload.err, EXOKAY_TIE_OFF_VALUE});

  logic rchk_error_instr;
  logic rchk_error_data;

  assign rchk_error_instr = rchk_error_instr_read;
  assign rchk_error_data = ((support_if.req_was_store && rchk_error_data_write) || (!support_if.req_was_store && rchk_error_data_read));

  logic instr_rvalid_parity_error;
  assign instr_rvalid_parity_error = xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalid == xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalidpar;

  logic data_rvalid_parity_error;
  assign data_rvalid_parity_error = xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid == xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalidpar;


  ////////// INTERFACE INTEGRITY CHECKING IS ENABLED BY DEFAULT //////////

  a_xsecure_interface_integrity_default_on: assert property (
    p_xsecure_setting_default_on(
        xsecure_if.core_xsecure_ctrl_cpuctrl_integrity)
  ) else `uvm_error(info_tag, "Interface integrity checking is not enabled when exiting reset.\n");


  ////////// INTERFACE INTEGRITY PARITY BITS ARE COMPLEMENT BITS AT ALL TIMES GIVEN THERE IS NO GLITCH //////////

  property p_parity_signal_is_invers_of_signal(signal, parity_signal);
    @(posedge clk_i)

    //Make sure the parity bit is always the complement of the non-parity bit
    parity_signal == ~signal;

  endproperty

  a_xsecure_interface_integrity_obi_data_req_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      xsecure_if.core_i_m_c_obi_data_if_s_req_req,
      xsecure_if.core_i_m_c_obi_data_if_s_req_reqpar)
  ) else `uvm_error(info_tag, "The OBI data bus request parity bit is not inverse of the request bit.\n");

  a_xsecure_interface_integrity_obi_data_gnt_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      xsecure_if.core_i_m_c_obi_data_if_s_gnt_gnt,
      xsecure_if.core_i_m_c_obi_data_if_s_gnt_gntpar)
  ) else `uvm_error(info_tag, "The OBI data bus grant parity bit is not inverse of the grant bit.\n");

  a_xsecure_interface_integrity_obi_data_rvalid_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid,
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalidpar)
  ) else `uvm_error(info_tag, "The OBI data bus rvalid parity bit is not inverse of the rvalid bit.\n");

  a_xsecure_interface_integrity_obi_instr_req_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      xsecure_if.core_i_m_c_obi_instr_if_s_req_req,
      xsecure_if.core_i_m_c_obi_instr_if_s_req_reqpar)
  ) else `uvm_error(info_tag, "The OBI instruction bus request parity bit is not inverse of the request bit.\n");

  a_xsecure_interface_integrity_obi_instr_gnt_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      xsecure_if.core_i_m_c_obi_instr_if_s_gnt_gnt,
      xsecure_if.core_i_m_c_obi_instr_if_s_gnt_gntpar)
  ) else `uvm_error(info_tag, "The OBI instruction bus grant parity bit is not inverse of the grant bit.\n");

  a_xsecure_interface_integrity_obi_instr_rvalid_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalid,
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalidpar)
  ) else `uvm_error(info_tag, "The OBI instruction bus rvalid parity bit is not inverse of the rvalid bit.\n");


////////// INTERFACE INTEGRITY PARITY BIT ERRORS DUE TO GLITCHES SET ALERT MAJOR //////////

property p_parity_signal_is_not_invers_of_signal_set_major_alert(signal, parity_signal);
    //Make sure the parity bit is not the complement of the non-parity bit
    parity_signal != ~signal

    |=>
    //Verify that the major alert is set
    xsecure_if.core_alert_major_o;

  endproperty

  a_xsecure_interface_integrity_obi_data_gnt_parity_error_set_major_alert: assert property (
    p_parity_signal_is_not_invers_of_signal_set_major_alert(
      xsecure_if.core_i_m_c_obi_data_if_s_gnt_gnt,
      xsecure_if.core_i_m_c_obi_data_if_s_gnt_gntpar)
  ) else `uvm_error(info_tag, "A OBI data bus grant parity error does not set the major alert.\n");

  a_xsecure_interface_integrity_obi_data_rvalid_parity_error_set_major_alert: assert property (
    p_parity_signal_is_not_invers_of_signal_set_major_alert(
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid,
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalidpar)
  ) else `uvm_error(info_tag, "A OBI data bus rvalid parity error does not set the major alert.\n");

  a_xsecure_interface_integrity_obi_instr_gnt_parity_error_set_major_alert: assert property (
    p_parity_signal_is_not_invers_of_signal_set_major_alert(
      xsecure_if.core_i_m_c_obi_instr_if_s_gnt_gnt,
      xsecure_if.core_i_m_c_obi_instr_if_s_gnt_gntpar)
  ) else `uvm_error(info_tag, "A OBI instruction bus grant parity error does not set the major alert.\n");

  a_xsecure_interface_integrity_obi_instr_rvalid_parity_error_set_major_alert: assert property (
    p_parity_signal_is_not_invers_of_signal_set_major_alert(
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalid,
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalidpar)
  ) else `uvm_error(info_tag, "A OBI instruction bus rvalid parity error does not set the major alert.\n");


  ////////// INTERFACE INTEGRITY RESPONSE CHECKSUMS FOR INSTRUCTIONS ARE GENERATED CORRECTLY //////////

  property p_check_that_response_checksum_is_generated_correctly(rvalid, is_checksum_error);

    //Make sure the interface integrity checking is enabled
    xsecure_if.core_xsecure_ctrl_cpuctrl_integrity

    //Make sure we receive a response packet
    && rvalid

    |->
    //Check that there is no checksum errors
    !is_checksum_error;

  endproperty

  a_xsecure_interface_integrity_rchk_instr_no_glitch: assert property (
    p_check_that_response_checksum_is_generated_correctly(
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalid,
      rchk_error_instr)
  ) else `uvm_error(info_tag, "The OBI instruction response packet's checksum is not as expected.\n");


  ////////// INTERFACE INTEGRITY RESPONSE CHECKSUMS FOR DATA ARE GENERATED CORRECTLY //////////

  a_xsecure_interface_integrity_rchk_data_no_glitch: assert property (
    p_check_that_response_checksum_is_generated_correctly(
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid,
      rchk_error_data)
  ) else `uvm_error(info_tag, "The OBI data response packet's checksum is not as expected.\n");


  ////////// INTERFACE INTEGRITY RESPONSE CHECKSUM ERRORS FOR INSTRUCTIONS SET ALERT MAJOR //////////

  property p_will_checksum_error_set_major_alert(is_integrity_checking_enabled, rvalid, req_had_integrity, is_checksum_error, is_major_alert_set);

    //If integrity checking is enabled the major alert should be set if there is a checksum error
    //However, if integrity checking is disabled the major alert should not be set even though there is a checksum error
    is_integrity_checking_enabled

    //Make sure we receive a response packet
    && rvalid

    //Make sure the response's request had integrity
    && req_had_integrity

    //Make sure there is a checksum error
    && is_checksum_error

    //Make sure major alert is not, and has not, been set
    && !alert_major_was_set && !xsecure_if.core_alert_major_o

    |=>
    //If the integrity checkup is enabled, verify that the major alert is set
    //but is the integrity checkup is disabled, verify that the major alert is not set
    is_major_alert_set;

  endproperty

  a_xsecure_interface_integrity_rchk_instr_glitch: assert property (
    p_will_checksum_error_set_major_alert(
      xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalid,
      support_if.instr_req_had_integrity,
      rchk_error_instr,
      xsecure_if.core_alert_major_o)
  ) else `uvm_error(info_tag, "An error in the OBI instruction bus's response packet's checksum does not set the major alert.\n");


  ////////// INTERFACE INTEGRITY RESPONSE CHECKSUM ERRORS FOR DATA SET ALERT MAJOR //////////

  a_xsecure_interface_integrity_rchk_data_glitch: assert property (
    p_will_checksum_error_set_major_alert(
      xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid,
      support_if.data_req_had_integrity,
      rchk_error_data,
      xsecure_if.core_alert_major_o)
  ) else `uvm_error(info_tag, "An error in the OBI data bus's response packet's checksum does not set the major alert.\n");


  ////////// INTERFACE INTEGRITY RESPONSE CHECKSUM ERRORS FOR INSTRUCTION DO NOT SET ALERT MAJOR IF THE INTEGRITY CHECKING IS DISABLED //////////

  a_xsecure_interface_integrity_off_rchk_instr_glitch: assert property (
    p_will_checksum_error_set_major_alert(
      !xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalid,
      support_if.instr_req_had_integrity,
      rchk_error_instr,
      !xsecure_if.core_alert_major_o)
  ) else `uvm_error(info_tag, "An error in the OBI instruction bus's response packet's checksum sets the major alert even though interface integrity checking is disabled.\n");


  ////////// INTERFACE INTEGRITY RESPONSE CHECKSUM ERRORS FOR DATA DO NOT SET ALERT MAJOR IF THE INTEGRITY CHECKING IS DISABLED //////////

  a_xsecure_interface_integrity_off_rchk_data_glitch: assert property (
    p_will_checksum_error_set_major_alert(
      !xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid,
      support_if.data_req_had_integrity,
      rchk_error_data,
      !xsecure_if.core_alert_major_o)
  ) else `uvm_error(info_tag, "An error in the OBI data bus's response packet's checksum sets the major alert even though interface integrity checking is disabled.\n");


 ////////// INTERFACE INTEGRITY ADDRESS CHECKSUM FOR INSTRUCTIONS IS GENERATED CORRECTLY //////////

  property p_check_that_request_checsum_does_not_contain_erros(req, is_checksum_error);

    //Make sure the interface integrity checking is enabled
    xsecure_if.core_xsecure_ctrl_cpuctrl_integrity

    //Make sure there is a packet ready to be sent
    && req

    |->
    //Make sure the checksum is generated correctly
    !is_checksum_error;

  endproperty

/*
  // TODO: this one fails due to rtl bug
  a_xsecure_interface_integrity_achk_instr_no_glitch: assert property (
    p_check_that_request_checsum_does_not_contain_erros(
      xsecure_if.core_i_m_c_obi_instr_if_s_req_req,
      achk_error_instr)
  ) else `uvm_error(info_tag, "The request checksum for the OBI instructions bus is not as expected.\n");
*/

  ////////// INTERFACE INTEGRITY ADDRESS CHECKSUM FOR DATA IS GENERATED CORRECTLY //////////

  a_xsecure_interface_integrity_achk_data_no_glitch: assert property (
    p_check_that_request_checsum_does_not_contain_erros(
      xsecure_if.core_i_m_c_obi_data_if_s_req_req,
      achk_error_data)
  ) else `uvm_error(info_tag, "The request checksum for the OBI data bus is not as expected.\n");


  ////////// INTERFACE INTEGRITY INSTRUCTION GNT PARITY ERROR SETS INTEGRITY ERROR BIT //////////

  property p_check_integrity_error_bit(rvalid, error, resp_integrity_error_bit);

    //Make sure the interface integrity checking is enabled
    xsecure_if.core_xsecure_ctrl_cpuctrl_integrity

    //Make sure we receive a valid packet
    && rvalid

    //Make sure there was an error that should set the response packet's integrity error bit high
    && error

    |->
    //Verify that the instruction packet's integrity error bit is set
    resp_integrity_error_bit;

  endproperty

  a_xsecure_interface_integrity_instr_error_set_if_gnt_error: assert property (
    p_check_integrity_error_bit(
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalid,
      support_if.gntpar_error_in_response_instr,
      xsecure_if.core_i_if_stage_i_bus_resp.integrity_err)
  ) else `uvm_error(info_tag, "The integrity error bit is not set in the OBI instruction bus's response packet, even though there was grant parity error when generating the request packet.\n");


  ////////// INTERFACE INTEGRITY DATA GNT PARITY ERROR SETS INTEGRITY ERROR BIT //////////

  a_xsecure_interface_integrity_data_error_set_if_gnt_error: assert property (
    p_check_integrity_error_bit(
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid,
      support_if.gntpar_error_in_response_data,
      xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err)
  ) else `uvm_error(info_tag, "The integrity error bit is not set in the OBI data bus's response packet, even though there was grant parity error when generating the request packet.\n");


  ////////// INTERFACE INTEGRITY INSTRUCTION RVALID PARITY ERROR SETS INTEGRITY ERROR BIT //////////

  a_xsecure_interface_integrity_instr_error_set_if_rvalid_error: assert property (
    p_check_integrity_error_bit(
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalid,
      instr_rvalid_parity_error,
      xsecure_if.core_i_if_stage_i_bus_resp.integrity_err)
  ) else `uvm_error(info_tag, "The integrity error bit is not set in the OBI instruction bus's response packet, even though there was a rvalid parity error.\n");


  ////////// INTERFACE INTEGRITY DATA RVALID PARITY ERROR SETS INTEGRITY ERROR BIT //////////

  a_xsecure_interface_integrity_data_error_set_if_rvalid_error: assert property (
    p_check_integrity_error_bit(
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid,
      data_rvalid_parity_error,
      xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err)
  ) else `uvm_error(info_tag, "The integrity error bit is not set in the OBI data bus's response packet, even though there was a rvalid parity error.\n");


  ////////// INTERFACE INTEGRITY INSTRUCTION CHECKSUM ERROR SETS INTEGRITY ERROR BIT //////////

  property p_check_integrity_error_bit_when_checksum_error(rvalid, error, req_had_integrity, resp_integrity_error_bit);

    //Make sure the interface integrity checking is enabled
    xsecure_if.core_xsecure_ctrl_cpuctrl_integrity

    //Make sure we receive a valid packet
    && rvalid

    //Make sure there was an error that should set the response packet's integrity error bit high
    && error

    //Make sure the response's request had integrity
    && req_had_integrity

    |->
    //Verify that the instruction packet's integrity error bit is set
    resp_integrity_error_bit;

  endproperty


  a_xsecure_interface_integrity_instr_error_set_if_checksum_error: assert property (
    p_check_integrity_error_bit_when_checksum_error(
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalid,
      rchk_error_instr,
      support_if.instr_req_had_integrity,
      xsecure_if.core_i_if_stage_i_bus_resp.integrity_err)
  ) else `uvm_error(info_tag, "The integrity error bit is not set in the OBI instruction bus's response packet, even though there was a checksum error.\n");


  ////////// INTERFACE INTEGRITY DATA CHECKSUM ERROR SETS INTEGRITY ERROR BIT //////////

  a_xsecure_interface_integrity_data_error_set_if_checksum_error: assert property (
    p_check_integrity_error_bit_when_checksum_error(
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid,
      rchk_error_data,
      support_if.data_req_had_integrity,
      xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err)
  ) else `uvm_error(info_tag, "The integrity error bit is not set in the OBI data bus's response packet, even though there was a checksum error.\n");


  endmodule : uvmt_cv32e40s_xsecure_interface_integrity_assert