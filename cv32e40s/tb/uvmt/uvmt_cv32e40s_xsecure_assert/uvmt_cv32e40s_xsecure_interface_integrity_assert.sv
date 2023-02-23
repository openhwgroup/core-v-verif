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
  localparam ASSUMED_VALUE_BE = 4'b1111;
  localparam ASSUMED_VALUE_WE = 1'b0;
  localparam ASSUMED_VALUE_ATOP = 6'b00_0000;
  localparam ASSUMED_VALUE_WDATA = 32'h0000_0000;
  localparam EXOKAY_TIE_OFF_VALUE = 1'b0;
  localparam REQ_WAS_READ = 1'b1;

  function logic [11:0] f_achk (logic [31:0] addr, logic [2:0] prot, logic [1:0] memtype, logic [3:0] be, logic we, logic dbg, logic [5:0] atop, logic [31:0] wdata);
    f_achk = {
      ^wdata[31:24],
      ^wdata[23:16],
      ^wdata[15:8],
      ^wdata[7:0],
      ^atop[5:0],
      ~^dbg,
      ~^{be[3:0], we},
      ~^{prot[2:0], memtype[1:0]},
      ^addr[31:24],
      ^addr[23:16],
      ^addr[15:8],
      ^addr[7:0]};
  endfunction


  function logic [4:0] f_rchk (logic err, logic exokay, logic [31:0] rdata);
    f_rchk = {
      ^{err, exokay},
      ^rdata[31:24],
      ^rdata[23:16],
      ^rdata[15:8],
      ^rdata[7:0]};
  endfunction


  //Sticky bit that indicates if the major alert has been set.
  logic alert_major_was_set;

  logic [11:0] achk_data;
  logic [11:0] achk_instr;
  logic [4:0] rchk_instr;
  logic [4:0] rchk_data;

  logic instr_rvalid_parity_error;
  logic data_rvalid_parity_error;
  logic compressed_aligned;
  logic [2:0][4:0] rchk_instr_alinmentbuffer;
  logic integrity_err_parity_rchk_alignmentbuffer;
  logic integrity_err_parity_rchk_obi_input;
  logic [1:0] rptr2;
  logic unaligned_integrity_error_parity_alignmentbuffer;
  logic unaligned_integrity_error_parity_alignmentbuffer_obi_input;
  logic unaligned_integrity_error_parity_rchk_alignmentbuffer;
  logic unaligned_integrity_error_parity_rchk_alignmentbuffer_obi_input;

  always @(posedge clk_i) begin
    if(!rst_ni) begin
      alert_major_was_set <= 0;
    end else if (xsecure_if.core_alert_major_o) begin
      alert_major_was_set <= xsecure_if.core_alert_major_o;
    end
  end

  //Independent generation of the checksum based on the outputted data

  assign achk_data = f_achk(
    xsecure_if.core_i_m_c_obi_data_if_req_payload.addr,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.prot,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.memtype,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.be,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.we,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.dbg,
    ASSUMED_VALUE_ATOP,
    xsecure_if.core_i_m_c_obi_data_if_req_payload.wdata);

  assign achk_instr = f_achk(
    xsecure_if.core_i_m_c_obi_instr_if_req_payload.addr,
    xsecure_if.core_i_m_c_obi_instr_if_req_payload.prot,
    xsecure_if.core_i_m_c_obi_instr_if_req_payload.memtype,
    ASSUMED_VALUE_BE,
    ASSUMED_VALUE_WE,
    xsecure_if.core_i_m_c_obi_instr_if_req_payload.dbg,
    ASSUMED_VALUE_ATOP,
    ASSUMED_VALUE_WDATA);

  assign rchk_instr = f_rchk(
    xsecure_if.core_i_m_c_obi_instr_if_resp_payload.err,
    EXOKAY_TIE_OFF_VALUE,
    xsecure_if.core_i_m_c_obi_instr_if_resp_payload.rdata);

  assign rchk_data = f_rchk(
    xsecure_if.core_i_m_c_obi_data_if_resp_payload.err,
    EXOKAY_TIE_OFF_VALUE,
    xsecure_if.core_i_m_c_obi_data_if_resp_payload.rdata);


  property p_xsecure_setting_default_on(logic xsecure_setting);

    //Make sure that when exiting reset mode the xsecure setting is off
    $rose(rst_ni)
    |->
    xsecure_setting;
  endproperty


  ////////// INTERFACE INTEGRITY CHECKING IS ENABLED BY DEFAULT //////////

  a_xsecure_interface_integrity_default_on: assert property (
    p_xsecure_setting_default_on(
        xsecure_if.core_xsecure_ctrl_cpuctrl_integrity)
  ) else `uvm_error(info_tag, "Interface integrity checking is not enabled when exiting reset.\n");


  ////////// INTERFACE INTEGRITY PARITY BITS ARE COMPLEMENT BITS AT ALL TIMES GIVEN THERE IS NO GLITCH //////////

  property p_parity_signal_is_invers_of_signal(signal, parity_signal);
    @(posedge clk_i)
    //Make sure we are not in reset mode
    rst_ni

    //Make sure the parity bit is always the complement of the non-parity bit
    && parity_signal == ~signal;

  endproperty

  a_xsecure_interface_integrity_obi_data_req_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      xsecure_if.core_i_data_req_o,
      xsecure_if.core_i_data_reqpar_o)
  ) else `uvm_error(info_tag, "The OBI data bus request parity bit is not inverse of the request bit.\n");

    a_xsecure_interface_integrity_obi_instr_req_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      xsecure_if.core_i_instr_req_o,
      xsecure_if.core_i_instr_reqpar_o)
  ) else `uvm_error(info_tag, "The OBI instruction bus request parity bit is not inverse of the request bit.\n");

  a_xsecure_interface_integrity_obi_data_gnt_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      xsecure_if.core_i_data_gnt_i,
      xsecure_if.core_i_data_gntpar_i)
  ) else `uvm_error(info_tag, "The OBI data bus grant parity bit is not inverse of the grant bit.\n");

  a_xsecure_interface_integrity_obi_data_rvalid_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      xsecure_if.core_i_data_rvalid_i,
      xsecure_if.core_i_data_rvalidpar_i)
  ) else `uvm_error(info_tag, "The OBI data bus rvalid parity bit is not inverse of the rvalid bit.\n");

  a_xsecure_interface_integrity_obi_instr_gnt_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      xsecure_if.core_i_instr_gnt_i,
      xsecure_if.core_i_instr_gntpar_i)
  ) else `uvm_error(info_tag, "The OBI instruction bus grant parity bit is not inverse of the grant bit.\n");

  a_xsecure_interface_integrity_obi_instr_rvalid_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      xsecure_if.core_i_instr_rvalid_i,
      xsecure_if.core_i_instr_rvalidpar_i)
  ) else `uvm_error(info_tag, "The OBI instruction bus rvalid parity bit is not inverse of the rvalid bit.\n");


  ////////// INTERFACE INTEGRITY INSTRUCTION AND DATA ACHK GENERATION //////////

  property p_checksum_generation(generation_condition, chk_signal, chk_calculated);
    xsecure_if.core_if_stage_if_valid_o
    && generation_condition
    |->
    chk_signal == chk_calculated;
  endproperty

  a_xsecure_interface_integrity_data_achk_generation: assert property (
    p_checksum_generation(
      xsecure_if.core_i_data_req_o,
      xsecure_if.core_i_data_achk_o,
      achk_data)
  ) else `uvm_error(info_tag, "The request checksum for the OBI data bus is not as expected.\n");

  //TODO: This one fails because the CLIC non-alignment issue is not implemented in the RTL yet
  /*
  a_xsecure_interface_integrity_instr_achk_generation: assert property (
    p_checksum_generation(
      xsecure_if.core_i_instr_req_o,
      xsecure_if.core_i_instr_achk_o,
      achk_instr)
  ) else `uvm_error(info_tag_rtl_bug, "The request checksum for the OBI instructions bus is not as expected.\n");
  */

  ////////// INTERFACE INTEGRITY INSTRUCTION AND DATA RCHK CHECKING //////////


  a_xsecure_interface_integrity_instr_rchk_generation: assert property (
    p_checksum_generation(
      xsecure_if.core_i_instr_rvalid_i,
      xsecure_if.core_i_instr_rchk_i,
      rchk_instr)
  );

  property p_checksum_generation_data_rchk(is_store, generation_condition, chk_signal, chk_calculated);
    is_store
    && generation_condition
    |->
    chk_signal == chk_calculated;
  endproperty

  a_xsecure_interface_integrity_store_data_rchk_generation: assert property (
    p_checksum_generation_data_rchk(
      support_if.req_was_store,
      xsecure_if.core_i_data_rvalid_i,
      xsecure_if.core_i_data_rchk_i[4],
      rchk_data[4])
  );

  a_xsecure_interface_integrity_read_data_rchk_generation: assert property (
    p_checksum_generation_data_rchk(
    !support_if.req_was_store,
    xsecure_if.core_i_data_rvalid_i,
    xsecure_if.core_i_data_rchk_i,
    rchk_data)
  );


  ////////// INTERFACE INTEGRITY ATTEMPT EXECUTION OF INSTRUCTION WITH INTEGRITY ERROR //////////


  a_glitch_xsecure_interface_integrity_execution_attempt_on_instruction_with_integrity_error_set_exception_and_major_alert: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.debug
    && $past(xsecure_if.core_i_ex_wb_pipe_instr_bus_resp_integrity_err)
    |->
    rvfi_if.rvfi_trap
    && rvfi_if.rvfi_trap.exception
    && (rvfi_if.rvfi_trap.exception_cause == 5'h19
    || rvfi_if.rvfi_trap.exception_cause == 5'h1)
    && xsecure_if.core_alert_major_o
  ) else `uvm_error(info_tag_glitch, "Attempted execution of an instruction with integrity error does not give correct exception cause, and dont set the major alert.\n");


  ////////// INTERFACE INTEGRITY PARITY BIT ERRORS DUE TO GLITCHES SET ALERT MAJOR //////////

  property p_parity_signal_is_not_invers_of_signal_set_major_alert(signal, parity_signal);

    //Make sure we are not in reset mode
    rst_ni

    //Make sure the parity bit is not the complement of the non-parity bit
    && parity_signal != ~signal

    |=>
    //Verify that the major alert is set
    xsecure_if.core_alert_major_o;

  endproperty

  a_glitch_xsecure_interface_integrity_obi_data_gnt_parity_error_set_major_alert: assert property (
    p_parity_signal_is_not_invers_of_signal_set_major_alert(
      xsecure_if.core_i_data_gnt_i,
      xsecure_if.core_i_data_gntpar_i)
  ) else `uvm_error(info_tag_glitch, "A OBI data bus grant parity error does not set the major alert.\n");

  a_glitch_xsecure_interface_integrity_obi_data_rvalid_parity_error_set_major_alert: assert property (
    p_parity_signal_is_not_invers_of_signal_set_major_alert(
      xsecure_if.core_i_data_rvalid_i,
      xsecure_if.core_i_data_rvalidpar_i)
  ) else `uvm_error(info_tag_glitch, "A OBI data bus rvalid parity error does not set the major alert.\n");

  a_glitch_xsecure_interface_integrity_obi_instr_gnt_parity_error_set_major_alert: assert property (
    p_parity_signal_is_not_invers_of_signal_set_major_alert(
      xsecure_if.core_i_instr_gnt_i,
      xsecure_if.core_i_instr_gntpar_i)
  ) else `uvm_error(info_tag_glitch, "A OBI instruction bus grant parity error does not set the major alert.\n");

  a_glitch_xsecure_interface_integrity_obi_instr_rvalid_parity_error_set_major_alert: assert property (
    p_parity_signal_is_not_invers_of_signal_set_major_alert(
      xsecure_if.core_i_instr_rvalid_i,
      xsecure_if.core_i_instr_rvalidpar_i)
  ) else `uvm_error(info_tag_glitch, "A OBI instruction bus rvalid parity error does not set the major alert.\n");


  ////////// INTERFACE INTEGRITY RESPONSE CHECKSUM ERRORS FOR INSTRUCTIONS AND DATA SET ALERT MAJOR //////////

  property p_will_checksum_error_set_major_alert(is_integrity_checking_enabled, rvalid, req_had_integrity, was_req_store_or_read, rchk_calculated, rchk_recived, is_major_alert_set);

    //If integrity checking is enabled the major alert should be set if there is a checksum error
    //However, if integrity checking is disabled the major alert should not be set even though there is a checksum error
    is_integrity_checking_enabled

    //Make sure we receive a response packet
    && rvalid

    //Make sure the response's request had integrity
    && req_had_integrity

    //Check if the request was a store or a read
    && was_req_store_or_read

    //Make sure there was an error that could set the response packet's integrity error bit high
    && rchk_calculated != rchk_recived

    |=>
    //If the integrity checkup is enabled, verify that the major alert is set
    //but is the integrity checkup is disabled, verify that the major alert is not set
    is_major_alert_set;

  endproperty

  a_glitch_xsecure_interface_integrity_rchk_instr: assert property (
    p_will_checksum_error_set_major_alert(
      xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
      xsecure_if.core_i_instr_rvalid_i,
      support_if.instr_req_had_integrity,
      REQ_WAS_READ,
      rchk_instr,
      xsecure_if.core_i_m_c_obi_instr_if_resp_payload.rchk,
      xsecure_if.core_alert_major_o)
  ) else `uvm_error(info_tag_glitch, "An error in the OBI instruction bus's response packet's checksum does not set the major alert.\n");

  a_glitch_xsecure_interface_integrity_rchk_data_store: assert property (
    p_will_checksum_error_set_major_alert(
      xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
      xsecure_if.core_i_data_rvalid_i,
      support_if.data_req_had_integrity,
      support_if.req_was_store,
      rchk_data[4],
      xsecure_if.core_i_m_c_obi_data_if_resp_payload.rchk[4],
      xsecure_if.core_alert_major_o)
  ) else `uvm_error(info_tag_glitch, "An error in the OBI data bus's response packet's checksum does not set the major alert.\n");

  a_glitch_xsecure_interface_integrity_rchk_data_read: assert property (
    p_will_checksum_error_set_major_alert(
      xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
      xsecure_if.core_i_data_rvalid_i,
      support_if.data_req_had_integrity,
      !support_if.req_was_store,
      rchk_data,
      xsecure_if.core_i_m_c_obi_data_if_resp_payload.rchk,
      xsecure_if.core_alert_major_o)
  ) else `uvm_error(info_tag_glitch, "An error in the OBI data bus's response packet's checksum does not set the major alert.\n");


  ////////// INTERFACE INTEGRITY RESPONSE CHECKSUM ERRORS FOR INSTRUCTION AND DATA DO NOT SET ALERT MAJOR IF THE INTEGRITY CHECKING IS DISABLED //////////

  a_glitch_xsecure_interface_integrity_off_rchk_instr: assert property (
    p_will_checksum_error_set_major_alert(
      !xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
      xsecure_if.core_i_instr_rvalid_i,
      support_if.instr_req_had_integrity,
      REQ_WAS_READ,
      rchk_instr,
      xsecure_if.core_i_m_c_obi_data_if_resp_payload.rchk,
      !xsecure_if.core_alert_major_o)
  ) else `uvm_error(info_tag_glitch, "An error in the OBI instruction bus's response packet's checksum sets the major alert even though interface integrity checking is disabled.\n");

  a_glitch_xsecure_interface_integrity_off_rchk_data_store: assert property (
    p_will_checksum_error_set_major_alert(
      !xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
      xsecure_if.core_i_data_rvalid_i,
      support_if.data_req_had_integrity,
      support_if.req_was_store,
      rchk_data,
      xsecure_if.core_i_m_c_obi_data_if_resp_payload.rchk,
      !xsecure_if.core_alert_major_o)
  ) else `uvm_error(info_tag_glitch, "An error in the OBI data bus's response packet's checksum sets the major alert even though interface integrity checking is disabled.\n");

  a_glitch_xsecure_interface_integrity_off_rchk_data_read: assert property (
    p_will_checksum_error_set_major_alert(
      !xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
      xsecure_if.core_i_data_rvalid_i,
      support_if.data_req_had_integrity,
      !support_if.req_was_store,
      rchk_data[4],
      xsecure_if.core_i_m_c_obi_data_if_resp_payload.rchk,
      !xsecure_if.core_alert_major_o)
  ) else `uvm_error(info_tag_glitch, "An error in the OBI data bus's response packet's checksum sets the major alert even though interface integrity checking is disabled.\n");


  ////////// INTERFACE INTEGRITY DATA IS WRITTEN TO THE REGISTER FILE EVEN THOUGH THERE IS A INTEGRITY ERROR //////////

  a_glitch_xsecure_interface_integrity_update_register_parity_checksum_error: assert property (

    //Make sure we update the GPR memory
    xsecure_if.core_rf_we_wb

    //Make sure the address is not x0
    && xsecure_if.core_rf_waddr_wb != 5'b00000

    //Make sure we fetch a valid instruction form the OBI interface
    && xsecure_if.core_i_data_rvalid_i

    //Make sure there is a parity/checksum error (need glitch)
    && xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err

    |=>
    //Make sure there is a parity or checksum fault
    xsecure_if.core_register_file_wrapper_register_file_mem[$past(xsecure_if.core_rf_waddr_wb)][31:0] == $past(xsecure_if.core_rf_wdata_wb)

  ) else `uvm_error(info_tag_glitch, "There is a load/store integrity error, and the register file is not updated.\n");


  ////////// VERIFY THAT PARITY ERRORS SET INTEGRITY BIT (AND FOR INSTRUCTIONS THAT THE INTEGRITY ERROR IS SET BEFOR ENTERING THE ALIGNMENT BUFFER) //////////

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

  a_glitch_xsecure_interface_integrity_instr_error_set_if_gnt_error: assert property (
    p_check_integrity_error_bit(
      xsecure_if.core_i_instr_rvalid_i,
      support_if.gntpar_error_in_response_instr,
      xsecure_if.core_i_if_stage_i_bus_resp.integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI instruction bus's response packet, even though there was grant parity error when generating the request packet.\n");

  assign instr_rvalid_parity_error = xsecure_if.core_i_instr_rvalid_i == xsecure_if.core_i_instr_rvalidpar_i;

  a_glitch_xsecure_interface_integrity_instr_error_set_if_rvalid_error: assert property (
    p_check_integrity_error_bit(
      xsecure_if.core_i_instr_rvalid_i,
      instr_rvalid_parity_error,
      xsecure_if.core_i_if_stage_i_bus_resp.integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI instruction bus's response packet, even though there was a rvalid parity error.\n");

  a_glitch_xsecure_interface_integrity_data_error_set_if_gnt_error: assert property (
    p_check_integrity_error_bit(
      xsecure_if.core_i_data_rvalid_i,
      support_if.gntpar_error_in_response_data,
      xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI data bus's response packet, even though there was grant parity error when generating the request packet.\n");

  assign data_rvalid_parity_error = xsecure_if.core_i_data_rvalid_i == xsecure_if.core_i_data_rvalidpar_i;

  a_glitch_xsecure_interface_integrity_data_error_set_if_rvalid_error: assert property (
    p_check_integrity_error_bit(
      xsecure_if.core_i_data_rvalid_i,
      data_rvalid_parity_error,
      xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI data bus's response packet, even though there was a rvalid parity error.\n");


  ////////// VERIFY THAT CHECKSUM ERRORS SET INTEGRITY BIT BEFOR ENTERING ALIGNMENT BUFFER //////////

  property p_check_integrity_error_bit_when_checksum_error(rvalid, rchk_calculated, rchk_recived, req_had_integrity, resp_integrity_error_bit);

    //Make sure the interface integrity checking is enabled
    xsecure_if.core_xsecure_ctrl_cpuctrl_integrity

    //Make sure we receive a valid packet
    && rvalid

    //Make sure there was an error that should set the response packet's integrity error bit high
    && rchk_calculated != rchk_recived

    //Make sure the response's request had integrity
    && req_had_integrity

    |->
    //Verify that the instruction packet's integrity error bit is set
    resp_integrity_error_bit;

  endproperty


  a_glitch_xsecure_interface_integrity_instr_error_set_if_checksum_error: assert property (
    p_check_integrity_error_bit_when_checksum_error(
      xsecure_if.core_i_instr_rvalid_i,
      rchk_instr,
      xsecure_if.core_i_m_c_obi_instr_if_resp_payload.rchk,
      support_if.instr_req_had_integrity,
      xsecure_if.core_i_if_stage_i_bus_resp.integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI instruction bus's response packet, even though there was a checksum error.\n");

  a_glitch_xsecure_interface_integrity_data_error_set_if_checksum_error: assert property (
    p_check_integrity_error_bit_when_checksum_error(
      xsecure_if.core_i_data_rvalid_i,
      rchk_data,
      xsecure_if.core_i_m_c_obi_data_if_resp_payload.rchk,
      support_if.data_req_had_integrity,
      xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI data bus's response packet, even though there was a checksum error.\n");


  ////////// VERIFY THAT INTEGRITY ERROR BIT AND RCHK BITS PASSE TOGETHER WITH THE INSTRUCTION TO THE ALIGNMENT BUFFERR //////////

  property p_integrity_error_propegation(x);
  xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_wptr == x
  && xsecure_if.core_i_instr_rvalid_i
  && !xsecure_if.core_i_wb_stage_i_ctrl_fsm_i_kill_if
  && xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_n_flush_q == '0

  |=>
  xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[x].bus_resp.integrity_err == $past(xsecure_if.core_i_if_stage_i_bus_resp.integrity_err);
  endproperty

  property p_integrity_checksum_propegation(x);
  xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_wptr == x
  && xsecure_if.core_i_instr_rvalid_i
  && !xsecure_if.core_i_wb_stage_i_ctrl_fsm_i_kill_if
  && xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_n_flush_q == '0

  |=>
  xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[x].bus_resp.rchk == $past(xsecure_if.core_i_if_stage_i_bus_resp.rchk);
  endproperty

  generate for (genvar wptr_cnt = 0; wptr_cnt < 3; wptr_cnt++) begin
    a_glitch_xsecure_integrity_interface_integrity_error_passes_with_instruction_to_alignment_buffer: assert property(
      p_integrity_error_propegation(wptr_cnt)
    ) else `uvm_error(info_tag, $sformatf("The alignmentbuffer entry the wptr points to (entry nr. %0d) does not contain the instruction's integirty bit.\n", wptr_cnt));

    a_glitch_xsecure_integrity_interface_rchk_bits_passes_with_instruction_to_alignment_buffer: assert property(
      p_integrity_checksum_propegation(wptr_cnt)
    ) else `uvm_error(info_tag, $sformatf("The alignmentbuffer entry the wptr points to (entry nr. %0d) does not contain the instruction's integirty bit.\n", wptr_cnt));
  end endgenerate

  ////////// INTERFACE INTEGRITY INSTRUCTION SHOULD HAVE AN ASSOCIATED INTEGRITY ERROR IF ANY OF ITS RELATED INSTRUCTION FETCHES INDICATE AN INTEGRITY ERROR //////////

  //Aligned or compressed instructions:

  property p_feature_inheritance_aligned_or_compressed(integrity_enabled_or_dontcare, is_compressed_aligned, rptr, is_alignment_buffer_instruction_valid, is_alignment_buffer_instruction_2_valid_or_dontcare, integrity_or_dontcare, inherit_signal_source);

    //Make sure the integrity configuration is enabled when setting integirty_err bit based on the checksum result
    //Or dont care if it is set or not when setting integrity_err bit based on only parity errors
    integrity_enabled_or_dontcare

    //Make sure it is not a dummy instruction
    && !xsecure_if.core_i_if_stage_i_dummy_insert

    //Make sure there is an instruction that will be executed in the pipeline
    && xsecure_if.core_if_stage_if_valid_o
    && xsecure_if.core_if_stage_id_ready_i

    //Check is the instruction is compressed or aligned, or not
    && is_compressed_aligned

    //Make sure the read pointer points so position rptr in the alignmentbuffer
    && xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_rptr == rptr

    //Check if there is a valid instruction in the alignmentbuffer,
    //if not use the OBI instruction input
    && is_alignment_buffer_instruction_valid

    //This signal only relevant for the unalignment instruction, and acts as a dontcare for the compressed and aligned instructions
    //Purpose: checke if more instructions in the alignmentbuffer is valid,
    //if not use the OBI instruction input
    && is_alignment_buffer_instruction_2_valid_or_dontcare

    //Make sure the integrity is set when setting integirty_err bit based on the checksum result
    //Or dont care if it is set or not when setting integrity_err bit based on only parity errors
    && integrity_or_dontcare

    |=>
    //Verify that integrity_err bit propegates to the instruction sendt into the pipeline
    xsecure_if.core_if_id_pipe_instr.bus_resp.integrity_err == $past(inherit_signal_source);

  endproperty

  assign compressed_aligned = (!xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_instr_addr_o[1]
  || (xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_instr_addr_o[1] && xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_unaligned_is_compressed));


  generate for (genvar i = 0; i < 3; i++) begin
    assign rchk_instr_alinmentbuffer[i] = f_rchk(
      xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[i].bus_resp.err,
      EXOKAY_TIE_OFF_VALUE,
      xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[i].bus_resp.rdata);
  end endgenerate


  generate for (genvar rptr = 0; rptr < 3; rptr++) begin

    //Instruction generated from one compressed instruction or aligned instruction fetch:

    //Parity error:

    a_glitch_xsecure_integrity_aligned_instruction_parity_err_inheritance_alignmentbuffer: assert property (
      p_feature_inheritance_aligned_or_compressed(
        1,
        compressed_aligned,
        rptr,
        xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_valid_q[rptr],
        1,
        1,
        xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr].bus_resp.integrity_err)
    ) else `uvm_error(info_tag, "Generated instruction does not inherit parity error bit from aligned instruction in the alignment buffer.\n");

    a_glitch_xsecure_integrity_aligned_instruction_parity_err_inheritance_obi_input: assert property (
        p_feature_inheritance_aligned_or_compressed(
          1,
          compressed_aligned,
          rptr,
          !xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_valid_q[rptr],
          1,
          1,
          xsecure_if.core_i_if_stage_i_bus_resp.integrity_err)
      ) else `uvm_error(info_tag, "Generated instruction does not inherit parity error bit from aligned OBI input instruction.\n");


    //Integrity error (parity/rchk):

    assign integrity_err_parity_rchk_alignmentbuffer = (xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr].bus_resp.integrity_err
    || (rchk_instr_alinmentbuffer[rptr] != xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr].bus_resp.rchk));

    a_glitch_xsecure_integrity_aligned_instruction_parity_rchk_err_inheritance_alignmentbuffer: assert property (
      p_feature_inheritance_aligned_or_compressed(
        xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
        compressed_aligned,
        rptr,
        xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_valid_q[rptr],
        1,
        xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr].bus_resp.integrity,
        integrity_err_parity_rchk_alignmentbuffer)
    ) else `uvm_error(info_tag, "Generated instruction does not inherit parity or rchk error from aligned instruction in the alignment buffer (integrity is on).\n");


    assign integrity_err_parity_rchk_obi_input = (xsecure_if.core_i_if_stage_i_bus_resp.integrity_err
    || (rchk_instr != xsecure_if.core_i_if_stage_i_bus_resp.rchk));

    a_glitch_xsecure_integrity_aligned_instruction_parity_rchk_err_inheritance_obi_input: assert property (
      p_feature_inheritance_aligned_or_compressed(
        xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
        compressed_aligned,
        rptr,
        !xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_valid_q[rptr],
        1,
        xsecure_if.core_i_if_stage_i_bus_resp.integrity,
        integrity_err_parity_rchk_obi_input)
    ) else `uvm_error(info_tag, "Generated instruction does not inherit parity or rchk error from aligned OBI input instruction (integrity is on).\n");



    if (rptr == 2) begin
      assign rptr2 = 0;
    end else begin
      assign rptr2 = rptr +1;
    end

    //Instruction generated from two unaligned instruction fetches:
    //Parity error:

    assign unaligned_integrity_error_parity_alignmentbuffer = xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr].bus_resp.integrity_err
    || xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr2].bus_resp.integrity_err;

    a_glitch_xsecure_integrity_unaligned_instruction_parity_err_inheritance_alignmentbuffer: assert property (
      p_feature_inheritance_aligned_or_compressed(
        1,
        !compressed_aligned,
        rptr,
        xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_valid_q[rptr],
        xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_valid_q[rptr2],
        1,
        unaligned_integrity_error_parity_alignmentbuffer)

    ) else `uvm_error(info_tag, "Generated instruction does not inherit integrity error bit from unaligned instructions in the alignment buffer.\n");

    assign unaligned_integrity_error_parity_alignmentbuffer_obi_input = xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr].bus_resp.integrity_err
    || xsecure_if.core_i_if_stage_i_bus_resp.integrity_err;

    a_glitch_xsecure_integrity_unaligned_instruction_parity_err_inheritance_alignmentbuffer_obi_input: assert property (
      p_feature_inheritance_aligned_or_compressed(
        1,
        !compressed_aligned,
        rptr,
        xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_valid_q[rptr],
        !xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_valid_q[rptr2],
        1,
        unaligned_integrity_error_parity_alignmentbuffer_obi_input)

    ) else `uvm_error(info_tag, "Generated instruction does not inherit integrity error bit from unaligned instructions in the alignment buffer.\n");


    //Integrity error (parity/rchk):


    assign unaligned_integrity_error_parity_rchk_alignmentbuffer = (xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr].bus_resp.integrity_err
    || xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr2].bus_resp.integrity_err
    || (rchk_instr_alinmentbuffer[rptr] != xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr].bus_resp.rchk)
    || (rchk_instr_alinmentbuffer[rptr2] != xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr2].bus_resp.rchk));

    a_glitch_xsecure_integrity_unaligned_instruction_parity_rchk_err_inheritance_alignmentbuffer: assert property (
      p_feature_inheritance_aligned_or_compressed(
        xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
        !compressed_aligned,
        rptr,
        xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_valid_q[rptr],
        xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_valid_q[rptr2],
        xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr].bus_resp.integrity && xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr2].bus_resp.integrity,
        unaligned_integrity_error_parity_rchk_alignmentbuffer)

    ) else `uvm_error(info_tag, "Generated instruction does not inherit integrity error bit from unaligned instructions in the alignment buffer.\n");


    assign unaligned_integrity_error_parity_rchk_alignmentbuffer_obi_input = (xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr].bus_resp.integrity_err
    || xsecure_if.core_i_if_stage_i_bus_resp.integrity_err
    || (rchk_instr_alinmentbuffer[rptr] != xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr].bus_resp.rchk)
    || (rchk_instr != xsecure_if.core_i_if_stage_i_bus_resp.rchk));

    a_glitch_xsecure_integrity_unaligned_instruction_parity_rchk_err_inheritance_alignmentbuffer_obi_input: assert property (
      p_feature_inheritance_aligned_or_compressed(
        xsecure_if.core_xsecure_ctrl_cpuctrl_integrity,
        !compressed_aligned,
        rptr,
        xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_valid_q[rptr],
        !xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_valid_q[rptr2],
        xsecure_if.core_i_if_stage_i_prefetch_unit_i_alignment_buffer_i_resp_q[rptr].bus_resp.integrity && xsecure_if.core_i_if_stage_i_bus_resp.integrity,
        unaligned_integrity_error_parity_rchk_alignmentbuffer_obi_input)

    ) else `uvm_error(info_tag, "Generated instruction does not inherit integrity error bit from unaligned instructions in the alignment buffer and OBI input.\n");


  end endgenerate


  ////////// INTERFACE INTEGRITY DATA ERROR RESULTS IN A NMI ERROR WITH EXCEPTION CODE 1026 OR 1027 //////////

  a_glitch_xsecure_interface_integrity_data_error_gives_instruction_error_helper_assertion: assert property (

    //Make sure we receive a valid instruction packet on the OBI instruction bus
    xsecure_if.core_i_data_rvalid_i

    //Make sure the data has an integrity error
    && xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err

    |=>
    //Verify that is set the NMI pending signal
    $rose(xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip)

    //Or that NMI is already pending due to a previous bus fault
    || $past(xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip)

  ) else `uvm_error(info_tag_glitch, "An associated parity/checksum error does not set the pending NMI signal.\n");


  a_glitch_xsecure_interface_integrity_data_error_gives_instruction_error: assert property (

    //Make sure we receive a valid instruction packet on the OBI instruction bus
    xsecure_if.core_i_data_rvalid_i

    //Make sure the data has an integrity error
    && xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err

    //Verify that is set the NMI pending signal
    ##1 $rose(xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip)

    |=>
    //Verify that mcause exception code is updated to 1026 (Load parity/checksum fault (imprecise)) or 1027 (Store parity/checksum fault (imprecise)) when the NMI is taken
    xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip[*0:$]
    ##1 !xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip && (xsecure_if.core_i_cs_registers_i_mcause_q.exception_code == 1026 || xsecure_if.core_i_cs_registers_i_mcause_q.exception_code == 1027)

  ) else `uvm_error(info_tag_glitch, "The NMI caused by an associated parity/checksum error does not have exception code 1027 or 1026.\n");


  ////////// THE SECURITY ALERT MAJOR IS SET WHENEVER THERE IS A NMI INTEGRITY FAULT //////////

  a_glitch_xsecure_security_alert_major_load_store_parity_checksum_fault_NMI_helper_assertion: assert property (

    //Receive valid data from the data bus
    xsecure_if.core_i_data_rvalid_i

    //Make sure the data has an integrity error
    && xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err

    |=>
    //Verify that is set the NMI pending signal
    $rose(xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip)

    //Or that NMI is already pending due to a previous bus fault
    || $past(xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip)

  ) else `uvm_error(info_tag_glitch, "A load/store parity/checksum fault does not set the pending NMI signal.\n");


  a_glitch_xsecure_security_alert_major_load_store_parity_checksum_fault_NMI: assert property (

    //Receive valid data from the data bus
    xsecure_if.core_i_data_rvalid_i

    //Make sure the data has an integrity error
    && xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err

    //Make sure the NMI pending signal will be set, and was not already set
    ##1 $rose(xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip)

    |=>
    //Verify that major alert is set when the NMI is taken
    xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip[*0:$]
    ##1 !xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip && xsecure_if.core_alert_major_o

  ) else `uvm_error(info_tag_glitch, "A load/store parity/checksum fault does not set the major alert when the integrity fault NMI is handeld.\n");


  //coverage with a load instructions
  c_glitch_xsecure_security_alert_major_parity_checksum_fault_NMI_load_instruction: cover property (

    //Receive valid data from the data bus
    xsecure_if.core_i_data_rvalid_i

    //Make sure the data has an integrity error
    && xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err

    //Make sure the NMI pending signal will be set, and was not already set
    ##1 $rose(xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip)

    //Make sure there is a load instruction
    && xsecure_if.rvfi_opcode == OPCODE_LOAD

  );

  //coverage with a store instructions
  c_glitch_xsecure_security_alert_major_parity_checksum_fault_NMI_store_instruction: cover property (

    //Receive valid data from the data bus
    xsecure_if.core_i_data_rvalid_i

    //Make sure the data has an integrity error
    && xsecure_if.core_i_load_store_unit_i_bus_resp.integrity_err

    //Make sure the NMI pending signal will be set, and was not already set
    ##1 $rose(xsecure_if.core_i_cs_registers_i_dcsr_rdata.nmip)

    //Make sure there is a store instruction
    && xsecure_if.rvfi_opcode == OPCODE_STORE

  );

  endmodule : uvmt_cv32e40s_xsecure_interface_integrity_assert