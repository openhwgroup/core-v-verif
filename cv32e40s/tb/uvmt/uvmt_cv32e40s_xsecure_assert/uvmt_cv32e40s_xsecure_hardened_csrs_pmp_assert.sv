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


module uvmt_cv32e40s_xsecure_hardened_csrs_pmp_assert
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

    //CSRs:
    input mseccfg_t pmp_mseccfg,
    input pmpncfg_t pmpncfg[PMP_NUM_REGIONS],
    input logic [PMP_ADDR_WIDTH-1:0] pmp_addr[PMP_NUM_REGIONS],

    //Shadows:
    input logic [$bits(mseccfg_t)-1:0] pmp_mseccfg_shadow,
    input logic [$bits(pmpncfg_t)-1:0] pmpncfg_shadow[PMP_NUM_REGIONS],
    input logic [PMP_ADDR_WIDTH-1:0] pmp_addr_shadow[PMP_NUM_REGIONS]

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


  //Verify that mismatch between the following CSRs and their shadows set alert major

  property p_hardened_csr_mismatch_sets_major_alert(csr, shadow);

    shadow != ~csr
    |=>
    alert_major;

  endproperty


  //MSECCFG
  a_glitch_xsecure_hardened_csr_mismatch_mseccfg: assert property (
    p_hardened_csr_mismatch_sets_major_alert(
    pmp_mseccfg,
    pmp_mseccfg_shadow)
  ) else `uvm_error(info_tag_glitch, "A mismatch between the CSR MSECCFG and its shadow does not set the major alert.\n");

  generate
    for (genvar n = 0; n < PMP_NUM_REGIONS; n++) begin

    //PMPNCFG
    a_glitch_xsecure_hardened_csr_mismatch_pmpncfg: assert property (
      p_hardened_csr_mismatch_sets_major_alert(
      pmpncfg[n],
      pmpncfg_shadow[n])
    ) else `uvm_error(info_tag_glitch, $sformatf("A mismatch between the CSR PMP%0dCFG and its shadow does not set the major alert.\n", n));

    //PMPADDR
    a_glitch_xsecure_hardened_csr_mismatch_pmpaddr: assert property (
      p_hardened_csr_mismatch_sets_major_alert(
      pmp_addr[n],
      pmp_addr_shadow[n])
    ) else `uvm_error(info_tag_glitch, $sformatf("A mismatch between the CSR PMPADDR[%0d] and its shadow does not set the major alert.\n", n));

    end
  endgenerate


  endmodule : uvmt_cv32e40s_xsecure_hardened_csrs_pmp_assert

