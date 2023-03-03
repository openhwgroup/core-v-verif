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
    parameter logic     CLIC = 0,
    parameter int       PMP_NUM_REGIONS = 2
  )
  (
   uvmt_cv32e40s_xsecure_if xsecure_if,
   input rst_ni,
   input clk_i
  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) | !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";
  string info_tag_glitch = "CV32E40S_XSECURE_ASSERT_COVERPOINTS (GLITCH BEHAVIOR)";


  ////////// CSRS ARE SHADOWED //////////

  //The following assertions make sure the CSRs are shadowed at all times.
  //The shadow registers are the complements of the CSRs

  property p_hardened_csr(csr, shadow);
    //Make sure the CSR is shadowed at all times, and that the shadow is equal to the complement of the CSR
    csr == ~shadow;
  endproperty

  //MSTATEEN0
  a_xsecure_hardened_csr_mstateen0: assert property (
    p_hardened_csr(
      xsecure_if.core_i_cs_registers_i_mstateen0_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mstateen0_csr_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag, "The CSR MSTATEEN0 is not shadowed.\n");

  //PRIVILEGE LEVEL
  a_xsecure_hardened_csr_privlvl: assert property (
    p_hardened_csr(
      xsecure_if.core_i_cs_registers_i_priv_lvl_csr_i_rdata_q,
      xsecure_if.core_cs_registers_priv_lvl_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag, "The priviliged level is not shadowed.\n");

  //JVT
  a_xsecure_hardened_csr_jvt: assert property (
    p_hardened_csr(
      xsecure_if.core_i_cs_registers_i_jvt_csr_i_rdata_q,
      xsecure_if.core_cs_registers_jvt_csr_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag, "The CSR JVT is not shadowed.\n");

  //MSTATUS
  a_xsecure_hardened_csr_mstatus: assert property (
    p_hardened_csr(
      xsecure_if.core_i_cs_registers_i_mstatus_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mstatus_csr_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag, "The CSR MSTATUS is not shadowed.\n");

  //CPUCTRL
  a_xsecure_hardened_csr_cpuctrl: assert property (
    p_hardened_csr(
      xsecure_if.core_i_cs_registers_i_cpuctrl_csr_i_rdata_q,
      xsecure_if.core_cs_registers_xsecure_cpuctrl_csr_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag, "The CSR CPUCTRL is not shadowed.\n");

  //DCSR
  a_xsecure_hardened_csr_dcsr: assert property (
    p_hardened_csr(
      xsecure_if.core_i_cs_registers_i_dcsr_csr_i_rdata_q,
      xsecure_if.core_i_cs_registers_i_gen_debug_csr_dcsr_csr_i_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag, "The CSR DCSR is not shadowed.\n");

  //MEPC
  a_xsecure_hardened_csr_mepc: assert property (
    p_hardened_csr(
      xsecure_if.core_i_cs_registers_i_mepc_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mepc_csr_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag, "The CSR MEPC is not shadowed.\n");

  //MSCRATCH (Therby also MSCRATCHCSW and MSCRATCHCSWL)
  a_xsecure_hardened_csr_mscratch: assert property (
    p_hardened_csr(
      xsecure_if.core_i_cs_registers_i_mscratch_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mscratch_csr_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag, "The CSR MSCRATCH is not shadowed.\n");

  generate
    if(PMP_NUM_REGIONS > 0) begin

      //MSECCFG
      a_xsecure_hardened_csr_mseccfg: assert property (
        p_hardened_csr(
          xsecure_if.core_i_cs_registers_i_pmp_mseccfg_q,
          xsecure_if.uvmt_cv32e40s_tb_pmp_mseccfg_q_shadow_q)
      ) else `uvm_error(info_tag, "The CSR MSECCFG is not shadowed.\n");

    end
  endgenerate

  generate
    for (genvar n = 0; n < PMP_NUM_REGIONS; n++) begin

      //PMPNCFG
      a_xsecure_hardened_csr_pmpncfg: assert property (
        p_hardened_csr(
          xsecure_if.core_i_cs_registers_i_pmpncfg_q[n],
          xsecure_if.uvmt_cv32e40s_tb_pmpncfg_q_shadow_q[n])
      ) else `uvm_error(info_tag, $sformatf("The CSR PMP%0dCFG is not shadowed.\n", n));

      //PMPADDR
      a_xsecure_hardened_csr_pmpaddr: assert property (
        p_hardened_csr(
          xsecure_if.core_i_cs_registers_i_pmp_addr_q[n],
          xsecure_if.uvmt_cv32e40s_tb_pmp_addr_q_shadow_q[n])
      ) else `uvm_error(info_tag, $sformatf("The CSR PMPADDR[%0d] is not shadowed.\n", n));

    end
  endgenerate

  generate
    if(CLIC) begin

      //MTVT
      a_xsecure_hardened_csr_mtvt: assert property (
        p_hardened_csr(
          xsecure_if.core_i_cs_registers_i_mtvt_q,
          xsecure_if.uvmt_cv32e40s_tb_mtvt_q_shadow_q)
      ) else `uvm_error(info_tag, "The CSR MTVT is not shadowed.\n");

      //MTVEC
      a_xsecure_hardened_csr_mtvec: assert property (
        p_hardened_csr(
          xsecure_if.core_i_cs_registers_i_mtvec_q,
          xsecure_if.uvmt_cv32e40s_tb_mtvec_q_shadow_q)
      ) else `uvm_error(info_tag, "The CSR MTVEC is not shadowed.\n");

      //MINTSTATUS
      a_xsecure_hardened_csr_mintstatus: assert property (
        p_hardened_csr(
          xsecure_if.core_i_cs_registers_i_mintstatus_q,
          xsecure_if.uvmt_cv32e40s_tb_mintstatus_q_shadow_q)
      ) else `uvm_error(info_tag, "The CSR MINTSTATUS is not shadowed.\n");

      //MINTTHRESH
      a_xsecure_hardened_csr_mintthresh: assert property (
        p_hardened_csr(
          xsecure_if.core_i_cs_registers_i_mintthresh_q,
          xsecure_if.uvmt_cv32e40s_tb_mintthresh_q_shadow_q)
      ) else `uvm_error(info_tag, "The CSR MINTTHRESH is not shadowed.\n");

    end else begin

      //MTVEC
      a_xsecure_hardened_csr_mtvec: assert property (
        p_hardened_csr(
          xsecure_if.core_i_cs_registers_i_mtvec_q,
          xsecure_if.uvmt_cv32e40s_tb_mtvec_q_shadow_q)
      ) else `uvm_error(info_tag, "The CSR MTVEC is not shadowed.\n");

      //MIE
      a_xsecure_hardened_csr_mie: assert property (
        p_hardened_csr(
          xsecure_if.core_i_cs_registers_i_mie_q,
          xsecure_if.uvmt_cv32e40s_tb_mie_q_hardened_shadow_q)
      ) else `uvm_error(info_tag, "The CSR MIE is not shadowed.\n");

    end
  endgenerate


  ////////// SET THE MAJOR ALERT IF A CSR IS NOT SHADOWED //////////

  //The following assertions check if mismatches between the CSRs and their corresponding shadow registers result in the major alert being set

  property p_hardened_csr_mismatch_sets_major_aler(csr, shadow);

    //Make sure the shadow is not the complement of the CSR
    shadow != ~csr

    |=>
    //Verify that the major alert is set
    xsecure_if.core_alert_major_o;
  endproperty

  //MSTATEEN0
  a_glitch_xsecure_hardened_csr_mismatch_mstateen0: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      xsecure_if.core_i_cs_registers_i_mstateen0_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mstateen0_csr_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MSTATEEN0 and its shadow does not set the major alert.\n");

  //PRIVILEGE LEVEL
  a_glitch_xsecure_hardened_csr_mismatch_privlvl: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      xsecure_if.core_i_cs_registers_i_priv_lvl_csr_i_rdata_q,
      xsecure_if.core_cs_registers_priv_lvl_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the priviliged level and its shadow does not set the major alert.\n");

  //JVT
  a_glitch_xsecure_hardened_csr_mismatch_jvt: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      xsecure_if.core_i_cs_registers_i_jvt_csr_i_rdata_q,
      xsecure_if.core_cs_registers_jvt_csr_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR JVT and its shadow does not set the major alert.\n");

  //MSTATUS
  a_glitch_xsecure_hardened_csr_mismatch_mstatus: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      xsecure_if.core_i_cs_registers_i_mstatus_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mstatus_csr_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MSTATUS and its shadow does not set the major alert.\n");

  //CPUCTRL
  a_glitch_xsecure_hardened_csr_mismatch_cpuctrl: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      xsecure_if.core_i_cs_registers_i_cpuctrl_csr_i_rdata_q,
      xsecure_if.core_cs_registers_xsecure_cpuctrl_csr_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR CPUCTRL and its shadow does not set the major alert.\n");

  //DCSR
  a_glitch_xsecure_hardened_csr_mismatch_dcsr: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      xsecure_if.core_i_cs_registers_i_dcsr_csr_i_rdata_q,
      xsecure_if.core_i_cs_registers_i_gen_debug_csr_dcsr_csr_i_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR DCSR and its shadow does not set the major alert.\n");

  //MEPC
  a_glitch_xsecure_hardened_csr_mismatch_mepc: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      xsecure_if.core_i_cs_registers_i_mepc_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mepc_csr_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MEPC and its shadow does not set the major alert.\n");

  //MSCRATCH
  a_glitch_xsecure_hardened_csr_mismatch_mscratch: assert property (
    p_hardened_csr_mismatch_sets_major_aler(
      xsecure_if.core_i_cs_registers_i_mscratch_csr_i_rdata_q,
      xsecure_if.core_cs_registers_mscratch_csr_gen_hardened_shadow_q)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MSCRATCH and its shadow does not set the major alert.\n");



  generate
    if(PMP_NUM_REGIONS > 0) begin

      //MSECCFG
      a_glitch_xsecure_hardened_csr_mismatch_mseccfg: assert property (
        p_hardened_csr_mismatch_sets_major_aler(
          xsecure_if.core_i_cs_registers_i_pmp_mseccfg_q,
          xsecure_if.uvmt_cv32e40s_tb_pmp_mseccfg_q_shadow_q)
      ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MSECCFG and its shadow does not set the major alert.\n");

    end
  endgenerate

  generate
    for (genvar n = 0; n < PMP_NUM_REGIONS; n++) begin

      //PMPNCFG
      a_glitch_xsecure_hardened_csr_mismatch_pmpncfg: assert property (
        p_hardened_csr_mismatch_sets_major_aler(
          xsecure_if.core_i_cs_registers_i_pmpncfg_q[n],
          xsecure_if.uvmt_cv32e40s_tb_pmpncfg_q_shadow_q[n])
      ) else `uvm_error(info_tag_glitch, $sformatf("A mismatch between the CSR PMP%0dCFG and its shadow does not set the major alert.\n", n));

      //PMPADDR
      a_glitch_xsecure_hardened_csr_mismatch_pmpaddr: assert property (
        p_hardened_csr_mismatch_sets_major_aler(
          xsecure_if.core_i_cs_registers_i_pmp_addr_q[n],
          xsecure_if.uvmt_cv32e40s_tb_pmp_addr_q_shadow_q[n])
      ) else `uvm_error(info_tag_glitch, $sformatf("A mismatch between the CSR PMPADDR[%0d] and its shadow does not set the major alert.\n", n));

    end
  endgenerate

  generate
    if(CLIC) begin

      //MTVT
      a_glitch_xsecure_hardened_csr_mismatch_mtvt: assert property (
        p_hardened_csr_mismatch_sets_major_aler(
          xsecure_if.core_i_cs_registers_i_mtvt_q,
          xsecure_if.uvmt_cv32e40s_tb_mtvt_q_shadow_q)
      ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MTVT and its shadow does not set the major alert.\n");

      //MTVEC
      a_glitch_xsecure_hardened_csr_mismatch_mtvec: assert property (
        p_hardened_csr_mismatch_sets_major_aler(
          xsecure_if.core_i_cs_registers_i_mtvec_q,
          xsecure_if.uvmt_cv32e40s_tb_mtvec_q_shadow_q)
      ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MTVEC and its shadow does not set the major alert.\n");

      //MINTSTATUS
      a_glitch_xsecure_hardened_csr_mismatch_mintstatus: assert property (
        p_hardened_csr_mismatch_sets_major_aler(
          xsecure_if.core_i_cs_registers_i_mintstatus_q,
          xsecure_if.uvmt_cv32e40s_tb_mintstatus_q_shadow_q)
      ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MINTSTATUS and its shadow does not set the major alert.\n");

      //MINTTHRESH
      a_glitch_xsecure_hardened_csr_mismatch_mintthresh: assert property (
        p_hardened_csr_mismatch_sets_major_aler(
          xsecure_if.core_i_cs_registers_i_mintthresh_q,
          xsecure_if.uvmt_cv32e40s_tb_mintthresh_q_shadow_q)
      ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MINTTHRESH and its shadow does not set the major alert.\n");

    end else begin

      //MTVEC
      a_glitch_xsecure_hardened_csr_mismatch_mtvec: assert property (
        p_hardened_csr_mismatch_sets_major_aler(
          xsecure_if.core_i_cs_registers_i_mtvec_q,
          xsecure_if.uvmt_cv32e40s_tb_mtvec_q_shadow_q)
      ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MTVEC and its shadow does not set the major alert.\n");

      //MIE
      a_glitch_xsecure_hardened_csr_mismatch_mie: assert property (
        p_hardened_csr_mismatch_sets_major_aler(
          xsecure_if.core_i_cs_registers_i_mie_q,
          xsecure_if.uvmt_cv32e40s_tb_mie_q_hardened_shadow_q)
      ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MIE and its shadow does not set the major alert.\n");

    end
  endgenerate


  endmodule : uvmt_cv32e40s_xsecure_hardened_csrs_assert