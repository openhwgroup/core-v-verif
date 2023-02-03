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


module uvmt_cv32e40s_xsecure_bus_protocol_hardening_assert
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

  //Sticky bit that indicates if the major alert has been set.
  logic core_i_alert_i_itf_prot_err_i_sticky;

  //Sticky bit that indicates if major alert has been set due to a protocol error.
  always @(posedge clk_i) begin
    if(!rst_ni) begin
      core_i_alert_i_itf_prot_err_i_sticky = 0;
    end else if (xsecure_if.core_i_alert_i_itf_prot_err_i) begin
      core_i_alert_i_itf_prot_err_i_sticky = xsecure_if.core_i_alert_i_itf_prot_err_i;
    end
  end


  ////////// BUS PROTOCOL HARDENING BEHAVIOUR WHEN THERE ARE NO GLITCHES //////////

  property p_resp_after_addr_no_glitch(obi_rvalid, v_addr_ph_cnt);

    //Make sure there is a response phase transfer
    obi_rvalid

    |->
    //Check that the response phase transfer is indeed a response to an address transfer (in other words, that there at least exists one active address transfer)
    v_addr_ph_cnt > 0;

  endproperty;

  a_xsecure_bus_hardening_resp_after_addr_no_glitch_data: assert property (
    p_resp_after_addr_no_glitch(
      xsecure_if.core_i_data_rvalid_i,
      support_if.data_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "There is a response before a request in the OBI data bus handshake.\n");

  a_xsecure_bus_hardening_resp_after_addr_no_glitch_instr: assert property (
    p_resp_after_addr_no_glitch(
      xsecure_if.core_i_instr_rvalid_i,
      support_if.instr_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "There is a response before a request in the OBI instruction bus handshake.\n");

  a_xsecure_bus_hardening_resp_after_addr_no_glitch_abiim: assert property (
    p_resp_after_addr_no_glitch(
      xsecure_if.core_i_if_stage_i_prefetch_resp_valid,
      support_if.abiim_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "There is a response before a request in the handshake between alignmentbuffer (ab) and instructoin (i) interface (i) mpu (m).\n");

  a_xsecure_bus_hardening_resp_after_addr_no_glitch_lml: assert property (
    p_resp_after_addr_no_glitch(
      xsecure_if.core_i_load_store_unit_i_resp_valid,
      support_if.lml_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "There is a response before a request in the handshake between LSU (l) MPU (m) and LSU (l).\n");

  a_xsecure_bus_hardening_resp_after_addr_no_glitch_lrfodi: assert property (
    p_resp_after_addr_no_glitch(
      xsecure_if.core_i_load_store_unit_i_bus_resp_valid,
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

    //Make sure major alert has not been set due to protpcol error
    !core_i_alert_i_itf_prot_err_i_sticky

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

  a_glitch_xsecure_bus_hardening_resp_after_addr_glitch_data: assert property (
    p_resp_after_addr_glitch(
      xsecure_if.core_i_m_c_obi_data_if_s_rvalid_rvalid,
      support_if.data_bus_resp_ph_cont,
      support_if.data_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag_glitch, "A response before a request in the OBI data bus handshake does not set the major alert.\n");

  a_glitch_xsecure_bus_hardening_resp_after_addr_glitch_instr: assert property (
    p_resp_after_addr_glitch(
      xsecure_if.core_i_m_c_obi_instr_if_s_rvalid_rvalid,
      support_if.instr_bus_resp_ph_cont,
      support_if.instr_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag_glitch, "A response before a request in the OBI instruction bus handshake does not set the major alert.\n");

  a_glitch_xsecure_bus_hardening_resp_after_addr_glitch_abiim: assert property (
    p_resp_after_addr_glitch(
      xsecure_if.core_i_if_stage_i_prefetch_resp_valid,
      support_if.abiim_bus_resp_ph_cont,
      support_if.abiim_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag_glitch, "A response before a request in the handshake between alignmentbuffer (ab) and instructoin (i) interface (i) mpu (m) does not set the major alert.\n");

  a_glitch_xsecure_bus_hardening_resp_after_addr_glitch_lml: assert property (
    p_resp_after_addr_glitch(
      xsecure_if.core_i_load_store_unit_i_resp_valid,
      support_if.lml_bus_resp_ph_cont,
      support_if.lml_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag_glitch, "A response before a request in the handshake between LSU (l) MPU (m) and LSU (l) does not set the major alert.\n");

  a_glitch_xsecure_bus_hardening_resp_after_addr_glitch_lrfodi: assert property (
    p_resp_after_addr_glitch(
      xsecure_if.core_i_load_store_unit_i_bus_resp_valid,
      support_if.lrfodi_bus_resp_ph_cont,
      support_if.lrfodi_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag_glitch, "A response before a request in the handshake between LSU (l) respons (r) filter (f) and the OBI (o) data (d) interface (i) does not set the major alert.\n");



  ////////// BUS PROTOCOL HARDENING BEHAVIOUR COUNTER UNDERFLOW SET THE MAJOR ALERT //////////

  a_glitch_xsecure_bus_hardening_counter_overflow_set_major_alert: assert property (

    //Make sure the counter is in a position where it can underflow
    (xsecure_if.core_i_load_store_unit_i_response_filter_i_core_cnt_q == 0)

    //Make sure the counter underflows
    ##1 xsecure_if.core_i_load_store_unit_i_response_filter_i_core_cnt_q != 0
    && xsecure_if.core_i_load_store_unit_i_response_filter_i_core_cnt_q != 1

    |->
    //Verify that alert major is set
    xsecure_if.core_alert_major_o
  ) else `uvm_error(info_tag_glitch, "The counter underflows but does not set the major alert.\n");


  endmodule : uvmt_cv32e40s_xsecure_bus_protocol_hardening_assert