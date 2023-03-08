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


module uvmt_cv32e40s_xsecure_hardened_csrs_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1,
    parameter int       PMP_ADDR_WIDTH = 32,
    parameter int       PMP_NUM_REGIONS = 2
  )
  (

    input rst_ni,
    input clk_i,

    //Alert:
    input logic alert_major,

    //PMP:
    `ifdef PMP_ENABLE_2
      //CSRs:
      input mseccfg_t pmp_mseccfg,
      input pmpncfg_t pmpncfg[PMP_MAX_REGIONS],
      input logic [PMP_ADDR_WIDTH-1:0] pmp_addr[PMP_MAX_REGIONS],

      //Shadows:
      input logic [$bits(mseccfg_t)-1:0] pmp_mseccfg_shadow,
      input logic [$bits(pmpncfg_t)-1:0] pmpncfg_shadow[PMP_MAX_REGIONS],
      input logic [PMP_ADDR_WIDTH-1:0] pmp_addr_shadow[PMP_MAX_REGIONS],
    `endif

    //CLIC or Basic mode
    `ifdef CLIC_EN
      input mtvt_t mtvt,
      input mintstatus_t mintstatus,
      input logic [31:0] mintthresh,

      input logic [$bits(mtvt_t)-1:0] mtvt_shadow,
      input logic [$bits(mintstatus_t)-1:0] mintstatus_shadow,
      input logic [31:0] mintthresh_shadow,

    `elsif CLIC_DIS
      input logic [31:0] mie,
      input logic [31:0] mie_shadow,
    `endif

    input mtvec_t mtvec,
    input logic [31:0] mstateen0,
    input [$bits(privlvl_t)-1:0] priv_lvl,
    input jvt_t jvt,
    input mstatus_t mstatus,
    input cpuctrl_t cpuctrl,
    input dcsr_t dcsr,
    input logic [31:0] mepc,
    input logic [31:0] mscratch,

    input logic [$bits(mtvec_t)-1:0] mtvec_shadow,
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
  default disable iff (!(rst_ni) | !(SECURE));
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


  `ifdef PMP_ENABLE_2

    //MSECCFG
    a_xsecure_hardened_csr_mseccfg: assert property (
      p_hardened_csr(
        pmp_mseccfg,
        pmp_mseccfg_shadow)
    ) else `uvm_error(info_tag, "The CSR MSECCFG is not shadowed.\n");

    generate
      for (genvar n = 0; n < PMP_NUM_REGIONS; n++) begin

        //PMPNCFG
        a_xsecure_hardened_csr_pmpncfg: assert property (
          p_hardened_csr(
            pmpncfg[n],
            pmpncfg_shadow[n])
        ) else `uvm_error(info_tag, $sformatf("The CSR PMP%0dCFG is not shadowed.\n", n));

        //PMPADDR
        a_xsecure_hardened_csr_pmpaddr: assert property (
          p_hardened_csr(
            pmp_addr[n],
            pmp_addr_shadow[n])
        ) else `uvm_error(info_tag, $sformatf("The CSR PMPADDR[%0d] is not shadowed.\n", n));

      end
    endgenerate
  `endif


  `ifdef CLIC_EN

    //MTVT
    a_xsecure_hardened_csr_mtvt: assert property (
      p_hardened_csr(
        mtvt,
        mtvt_shadow)
    ) else `uvm_error(info_tag, "The CSR MTVT is not shadowed.\n");

    //MTVEC
    a_xsecure_hardened_csr_mtvec: assert property (
      p_hardened_csr(
        mtvec,
        mtvec_shadow)
    ) else `uvm_error(info_tag, "The CSR MTVEC is not shadowed.\n");

    //MINTSTATUS
    a_xsecure_hardened_csr_mintstatus: assert property (
      p_hardened_csr(
        mintstatus,
        mintstatus_shadow)
    ) else `uvm_error(info_tag, "The CSR MINTSTATUS is not shadowed.\n");

    //MINTTHRESH
    a_xsecure_hardened_csr_mintthresh: assert property (
      p_hardened_csr(
        mintthresh,
        mintthresh_shadow)
    ) else `uvm_error(info_tag, "The CSR MINTTHRESH is not shadowed.\n");

  `elsif CLIC_DIS

    //MTVEC
    a_xsecure_hardened_csr_mtvec: assert property (
      p_hardened_csr(
        mtvec,
        mtvec_shadow)
    ) else `uvm_error(info_tag, "The CSR MTVEC is not shadowed.\n");

    //MIE
    a_xsecure_hardened_csr_mie: assert property (
      p_hardened_csr(
        mie,
        mie_shadow)
    ) else `uvm_error(info_tag, "The CSR MIE is not shadowed.\n");

  `endif


  //Verify that mismatch between the following CSRs and their shadows

  property p_hardened_csr_mismatch_sets_major_aler(csr, shadow);

    shadow != ~csr
    |=>
    alert_major;

  endproperty

  //MSTATEEN0
  a_glitch_xsecure_hardened_csr_mismatch_mstateen0: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      mstateen0,
      mstateen0_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MSTATEEN0 and its shadow does not set the major alert.\n");

  //PRIVILEGE LEVEL
  a_glitch_xsecure_hardened_csr_mismatch_privlvl: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      priv_lvl,
      priv_lvl_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the priviliged level and its shadow does not set the major alert.\n");

  //JVT
  a_glitch_xsecure_hardened_csr_mismatch_jvt: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      jvt,
      jvt_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR JVT and its shadow does not set the major alert.\n");

  //MSTATUS
  a_glitch_xsecure_hardened_csr_mismatch_mstatus: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      mstatus,
      mstatus_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MSTATUS and its shadow does not set the major alert.\n");

  //CPUCTRL
  a_glitch_xsecure_hardened_csr_mismatch_cpuctrl: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      cpuctrl,
      cpuctrl_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR CPUCTRL and its shadow does not set the major alert.\n");

  //DCSR
  a_glitch_xsecure_hardened_csr_mismatch_dcsr: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      dcsr,
      dcsr_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR DCSR and its shadow does not set the major alert.\n");

  //MEPC
  a_glitch_xsecure_hardened_csr_mismatch_mepc: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      mepc,
      mepc_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MEPC and its shadow does not set the major alert.\n");

  //MSCRATCH
  a_glitch_xsecure_hardened_csr_mismatch_mscratch: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      mscratch,
      mscratch_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MSCRATCH and its shadow does not set the major alert.\n");


  `ifdef PMP_ENABLE_2

    //MSECCFG
    a_glitch_xsecure_hardened_csr_mismatch_mseccfg: assert property (
      p_hardened_csr_mismatch_sets_major_aler(
        pmp_mseccfg,
        pmp_mseccfg_shadow)
    ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MSECCFG and its shadow does not set the major alert.\n");

    generate
      for (genvar n = 0; n < PMP_NUM_REGIONS; n++) begin

        //PMPNCFG
        a_glitch_xsecure_hardened_csr_mismatch_pmpncfg: assert property (
          p_hardened_csr_mismatch_sets_major_aler(
            pmpncfg[n],
            pmpncfg_shadow[n])
        ) else `uvm_error(info_tag_glitch, $sformatf("A mismatch between the CSR PMP%0dCFG and its shadow does not set the major alert.\n", n));

        //PMPADDR
        a_glitch_xsecure_hardened_csr_mismatch_pmpaddr: assert property (
          p_hardened_csr_mismatch_sets_major_aler(
            pmp_addr[n],
            pmp_addr_shadow[n])
        ) else `uvm_error(info_tag_glitch, $sformatf("A mismatch between the CSR PMPADDR[%0d] and its shadow does not set the major alert.\n", n));

      end
    endgenerate

  `endif

  `ifdef CLIC_EN

    //MTVT
    a_glitch_xsecure_hardened_csr_mismatch_mtvt: assert property (
      p_hardened_csr_mismatch_sets_major_aler(
        mtvt,
        mtvt_shadow)
    ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MTVT and its shadow does not set the major alert.\n");

    //MTVEC
    a_glitch_xsecure_hardened_csr_mismatch_mtvec: assert property (
      p_hardened_csr_mismatch_sets_major_aler(
        mtvec,
        mtvec_shadow)
    ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MTVEC and its shadow does not set the major alert.\n");

    //MINTSTATUS
    a_glitch_xsecure_hardened_csr_mismatch_mintstatus: assert property (
      p_hardened_csr_mismatch_sets_major_aler(
        mintstatus,
        mintstatus_shadow)
    ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MINTSTATUS and its shadow does not set the major alert.\n");

    //MINTTHRESH
    a_glitch_xsecure_hardened_csr_mismatch_mintthresh: assert property (
      p_hardened_csr_mismatch_sets_major_aler(
        mintthresh,
        mintthresh_shadow)
    ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MINTTHRESH and its shadow does not set the major alert.\n");

  `elsif CLIC_DIS

    //MTVEC
    a_glitch_xsecure_hardened_csr_mismatch_mtvec: assert property (
      p_hardened_csr_mismatch_sets_major_aler(
        mtvec,
        mtvec_shadow)
    ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MTVEC and its shadow does not set the major alert.\n");

    //MIE
    a_glitch_xsecure_hardened_csr_mismatch_mie: assert property (
      p_hardened_csr_mismatch_sets_major_aler(
        mie,
        mie_shadow)
    ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MIE and its shadow does not set the major alert.\n");

  `endif


  endmodule : uvmt_cv32e40s_xsecure_hardened_csrs_assert