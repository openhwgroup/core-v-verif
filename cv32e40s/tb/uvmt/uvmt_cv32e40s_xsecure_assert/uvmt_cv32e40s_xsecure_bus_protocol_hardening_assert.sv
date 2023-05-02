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


module uvmt_cv32e40s_xsecure_bus_protocol_hardening_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
    //Interfaces:
    uvmt_cv32e40s_support_logic_module_o_if_t.slave_mp support_if,

    //Signals:
    input rst_ni,
    input clk_i,

    //Alerts:
    input logic alert_major,
    input logic bus_protocol_hardening_glitch,

    //OBI:
    input logic obi_data_rvalid,
    input logic obi_instr_rvalid,

    //Resp valids:
    input logic instr_if_mpu_resp,
    input logic lsu_mpu_resp,

    //Counters:
    input logic [1:0] lsu_rf_core_side_cnt,
    input logic [1:0] lsu_rf_bus_side_cnt

  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) || !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";
  string info_tag_glitch = "CV32E40S_XSECURE_ASSERT_COVERPOINTS (GLITCH BEHAVIOR)";


  logic bus_protocol_hardening_glitch_sticky;

  always @(posedge clk_i) begin
    if(!rst_ni) begin
      bus_protocol_hardening_glitch_sticky = 0;
    end else if (bus_protocol_hardening_glitch) begin
      bus_protocol_hardening_glitch_sticky = bus_protocol_hardening_glitch;
    end
  end


  //Verify that there are only response packets when there are outstanding requests in the following OBI protocols

  property p_resp(obi_rvalid, v_addr_ph_cnt);

    obi_rvalid
    |->
    v_addr_ph_cnt > 0;

  endproperty;


  a_xsecure_bus_hardening_no_outstanding_obi_instr_trans: assert property (
    p_resp(
      obi_instr_rvalid,
      support_if.instr_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "There is a response before a request in the OBI instruction bus handshake.\n");

  a_xsecure_bus_hardening_no_outstanding_obi_data_trans: assert property (
    p_resp(
      obi_data_rvalid,
      support_if.data_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag, "There is a response before a request in the OBI data bus handshake.\n");

  a_xsecure_bus_hardening_alignment_buff_receive_instr_if_mpu_resp: assert property (
    p_resp(
      instr_if_mpu_resp,
      support_if.alignment_buff_addr_ph_cnt)
  ) else `uvm_error(info_tag, "The alignment buffer does not have outstanding requests but receives a response from the instruction interface MPU.\n");

  a_xsecure_bus_hardening_lsu_receive_lsu_mpu_resp: assert property (
    p_resp(
      lsu_mpu_resp,
      support_if.lsu_addr_ph_cnt)
  ) else `uvm_error(info_tag, "The load-store unit does not have outstanding requests but receives a response from the load-store unit MPU.\n");


  //Verify that the core side and bus side transaction counters in the load store units response filter dont underflow

  property p_counter(cnt);

    cnt == 0
    |=>
    cnt == 0 || cnt == 1;

  endproperty


  a_xsecure_bus_hardening_core_side_cnt: assert property (
    p_counter(
      lsu_rf_core_side_cnt
    )
  ) else `uvm_error(info_tag, "The core side memory transaction counter in the load-store unit response filter underflows.\n");

  a_xsecure_bus_hardening_bus_side_cnt: assert property (
    p_counter(
      lsu_rf_bus_side_cnt
    )
  ) else `uvm_error(info_tag, "The bus side memory transaction counter in the load-store unit response filter underflows.\n");


  //Verify that major alert is set when there is a response packet even though there are no outstanding requests, in the following OBI protocols

  property p_resp_no_outstanding_req(obi_rvalid, resp_ph_cont, v_addr_ph_cnt);

    //If there has already been a bus protpcol fault the there will be an underflow error and the system acts strangely
    !bus_protocol_hardening_glitch_sticky
    && obi_rvalid
    && !resp_ph_cont
    && v_addr_ph_cnt == 0
    |=>
    alert_major;
  endproperty;

  a_glitch_xsecure_bus_hardening_no_outstanding_obi_instr_trans: assert property (
    p_resp_no_outstanding_req(
      obi_instr_rvalid,
      support_if.instr_bus_resp_ph_cont,
      support_if.instr_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag_glitch, "A response before a request in the OBI instruction bus handshake, but the alert major is not set.\n");

  a_glitch_xsecure_bus_hardening_no_outstanding_obi_data_trans: assert property (
    p_resp_no_outstanding_req(
      obi_data_rvalid,
      support_if.data_bus_resp_ph_cont,
      support_if.data_bus_v_addr_ph_cnt)
  ) else `uvm_error(info_tag_glitch, "A response before a request in the OBI data bus handshake, but the alert major is not set.\n");

  a_glitch_xsecure_bus_hardening_alignment_buff_receive_instr_if_mpu_resp: assert property (
    p_resp_no_outstanding_req(
      instr_if_mpu_resp,
      support_if.alignment_buff_resp_ph_cont,
      support_if.alignment_buff_addr_ph_cnt)
  ) else `uvm_error(info_tag_glitch, "The alignment buffer does not have outstanding requests but receives a response from the instruction interface MPU, but the alert major is not set.\n");

  a_glitch_xsecure_bus_hardening_lsu_receive_lsu_mpu_resp: assert property (
    p_resp_no_outstanding_req(
      lsu_mpu_resp,
      support_if.lsu_resp_ph_cont,
      support_if.lsu_addr_ph_cnt)
  ) else `uvm_error(info_tag_glitch, "The load-store unit does not have outstanding requests but receives a response from the load-store unit MPU, but the alert major is not set.\n");


  //Verify that the core side and bus side transaction counters in the load store units response filter dont underflow

  property p_counter_underflows(cnt);

    cnt == 0
    ##1 cnt != 0
    && cnt != 1
    |->
    alert_major;

  endproperty

  a_glitch_xsecure_bus_hardening_core_side_cnt_underflows: assert property (
    p_counter_underflows(
      lsu_rf_core_side_cnt
    )
  ) else `uvm_error(info_tag_glitch, "The core side memory transaction counter in the load-store unit response filter underflows, but the major alert is not set.\n");

  a_glitch_xsecure_bus_hardening_bus_side_cnt_underflows: assert property (
    p_counter_underflows(
      lsu_rf_bus_side_cnt
    )
  ) else `uvm_error(info_tag_glitch, "The bus side memory transaction counter in the load-store unit response filter underflows, but the major alert is not set.\n");


  endmodule : uvmt_cv32e40s_xsecure_bus_protocol_hardening_assert
