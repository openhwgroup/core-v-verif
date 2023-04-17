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


module uvmt_cv32e40s_xsecure_hardened_csrs_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (

    input rst_ni,
    input clk_i,

    //Alert:
    input logic alert_major,

    //CSRs:
    input logic [31:0] mstateen0,
    input [$bits(privlvl_t)-1:0] priv_lvl,
    input jvt_t jvt,
    input mstatus_t mstatus,
    input cpuctrl_t cpuctrl,
    input dcsr_t dcsr,
    input logic [31:0] mepc,
    input logic [31:0] mscratch,

    //Shadows:
    input logic [31:0] mstateen0_shadow,
    input logic [$bits(privlvl_t)-1:0] priv_lvl_shadow,
    input logic [$bits(jvt_t)-1:0] jvt_shadow,
    input logic [$bits(mstatus_t)-1:0] mstatus_shadow,
    input logic [$bits(cpuctrl_t)-1:0] cpuctrl_shadow,
    input logic [$bits(dcsr_t)-1:0] dcsr_shadow,
    input logic [31:0] mepc_shadow,
    input logic [31:0] mscratch_shadow

  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) || !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";
  string info_tag_glitch = "CV32E40S_XSECURE_ASSERT_COVERPOINTS (GLITCH BEHAVIOR)";


  //Verify that the following CSRs have bit-wise complemented shadows

  property p_hardened_csr(csr, shadow);
    csr == ~shadow;
  endproperty


  //MSTATEEN0
  a_xsecure_hardened_csr_mstateen0: assert property (
    p_hardened_csr(
      mstateen0,
      mstateen0_shadow)
  ) else `uvm_error(info_tag, "The CSR MSTATEEN0 is not shadowed.\n");

  //PRIVILEGE LEVEL
  a_xsecure_hardened_csr_privlvl: assert property (
    p_hardened_csr(
      priv_lvl,
      priv_lvl_shadow)
  ) else `uvm_error(info_tag, "The priviliged level is not shadowed.\n");

  //JVT
  a_xsecure_hardened_csr_jvt: assert property (
    p_hardened_csr(
      jvt,
      jvt_shadow)
  ) else `uvm_error(info_tag, "The CSR JVT is not shadowed.\n");

  //MSTATUS
  a_xsecure_hardened_csr_mstatus: assert property (
    p_hardened_csr(
      mstatus,
      mstatus_shadow)
  ) else `uvm_error(info_tag, "The CSR MSTATUS is not shadowed.\n");

  //CPUCTRL
  a_xsecure_hardened_csr_cpuctrl: assert property (
    p_hardened_csr(
      cpuctrl,
      cpuctrl_shadow)
  ) else `uvm_error(info_tag, "The CSR CPUCTRL is not shadowed.\n");

  //DCSR
  a_xsecure_hardened_csr_dcsr: assert property (
    p_hardened_csr(
      dcsr,
      dcsr_shadow)
  ) else `uvm_error(info_tag, "The CSR DCSR is not shadowed.\n");

  //MEPC
  a_xsecure_hardened_csr_mepc: assert property (
    p_hardened_csr(
      mepc,
      mepc_shadow)
  ) else `uvm_error(info_tag, "The CSR MEPC is not shadowed.\n");

  //MSCRATCH (which includes MSCRATCHCSW and MSCRATCHCSWL)
  a_xsecure_hardened_csr_mscratch: assert property (
    p_hardened_csr(
      mscratch,
      mscratch_shadow)
  ) else `uvm_error(info_tag, "The CSR MSCRATCH is not shadowed.\n");



  //Verify that mismatch between the following CSRs and their shadows set alert major

  property p_hardened_csr_mismatch_sets_major_alert(csr, shadow);

    shadow != ~csr
    |=>
    alert_major;
  endproperty


  //MSTATEEN0
  a_glitch_xsecure_hardened_csr_mismatch_mstateen0: assert property (
    p_hardened_csr_mismatch_sets_major_alert(
      mstateen0,
      mstateen0_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MSTATEEN0 and its shadow does not set the major alert.\n");

  //PRIVILEGE LEVEL
  a_glitch_xsecure_hardened_csr_mismatch_privlvl: assert property (
    p_hardened_csr_mismatch_sets_major_alert(
      priv_lvl,
      priv_lvl_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the priviliged level and its shadow does not set the major alert.\n");

  //JVT
  a_glitch_xsecure_hardened_csr_mismatch_jvt: assert property (
    p_hardened_csr_mismatch_sets_major_alert(
      jvt,
      jvt_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR JVT and its shadow does not set the major alert.\n");

  //MSTATUS
  a_glitch_xsecure_hardened_csr_mismatch_mstatus: assert property (
    p_hardened_csr_mismatch_sets_major_alert(
      mstatus,
      mstatus_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MSTATUS and its shadow does not set the major alert.\n");

  //CPUCTRL
  a_glitch_xsecure_hardened_csr_mismatch_cpuctrl: assert property (
    p_hardened_csr_mismatch_sets_major_alert(
      cpuctrl,
      cpuctrl_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR CPUCTRL and its shadow does not set the major alert.\n");

  //DCSR
  a_glitch_xsecure_hardened_csr_mismatch_dcsr: assert property (
    p_hardened_csr_mismatch_sets_major_alert(
      dcsr,
      dcsr_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR DCSR and its shadow does not set the major alert.\n");

  //MEPC
  a_glitch_xsecure_hardened_csr_mismatch_mepc: assert property (
    p_hardened_csr_mismatch_sets_major_alert(
      mepc,
      mepc_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MEPC and its shadow does not set the major alert.\n");

  //MSCRATCH
  a_glitch_xsecure_hardened_csr_mismatch_mscratch: assert property (
    p_hardened_csr_mismatch_sets_major_alert(
      mscratch,
      mscratch_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MSCRATCH and its shadow does not set the major alert.\n");


  endmodule : uvmt_cv32e40s_xsecure_hardened_csrs_assert

