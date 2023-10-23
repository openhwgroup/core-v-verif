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


module uvmt_cv32e40s_xsecure_register_file_ecc_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;

  #(
    parameter int       SECURE   = 1
  )
  (
    uvma_rvfi_instr_if_t rvfi_if,
    input rst_ni,
    input clk_i,

    //alerts:
    input logic alert_major,

    //Register file memory:
    input logic [REGFILE_WORD_WIDTH-1:0] gpr_mem [CORE_PARAM_REGFILE_NUM_WORDS],

    //Soruce registers:
    input logic [4:0] rs1,
    input logic [4:0] rs2,

    //Writing of GPRs:
    input logic gpr_we,
    input logic [4:0] gpr_waddr,
    input logic [31:0] gpr_wdata

  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) || !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";
  string info_tag_glitch = "CV32E40S_XSECURE_ASSERT_COVERPOINTS (GLITCH BEHAVIOR)";

  localparam REG_SIZE = 32;
  localparam ECC_SIZE = 6;
  localparam ZERO = '0;
  localparam REG_DEFAULT = '0;
  localparam ECC_DEFAULT = 6'h2A;

  ////////// GENERAL PURPOSE REGISTERS ARE ZERO WHEN EXITING RESET //////////

  //Verify that the general purpose registers are zero when exiting reset, and that their ECC values are corresponding to value zero (6'h2A)

  property p_gpr_ecc_reset(integer gpr_addr);

    $rose(rst_ni)
    |->
    gpr_mem[gpr_addr][(REG_SIZE-1) -:REG_SIZE] == REG_DEFAULT
    && gpr_mem[gpr_addr][(ECC_SIZE+REG_SIZE-1) -:ECC_SIZE] == ECC_DEFAULT;

  endproperty


  //Check the default value of the instructions' register sources by using RVFI
  property p_gpr_reset_rvfi(rs_addr, gpr_addr);

    $rose(rst_ni) ##0 rvfi_if.rvfi_valid[->1]
    ##0 rs_addr == gpr_addr

    |->
    rvfi_if.rvfi_rs1_rdata == REG_DEFAULT;
  endproperty


  generate for (genvar gpr_addr = 0; gpr_addr < 32; gpr_addr++) begin : gen_gpr_reset_value

    a_xsecure_rf_ecc_gpr_reset_value: assert property (
      p_gpr_ecc_reset(
        gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("GPR %0d is not set to 0 when exiting reset stage, or the syndrome is not set to 0x2A.\n", gpr_addr));

    a_xsecure_rf_ecc_gpr_reset_value_rvfi_rs1: assert property (
      p_gpr_reset_rvfi(
        rvfi_if.rvfi_rs1_addr,
        gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("GPR %0d is not set to 0 when exiting reset stage (as RS1 is not 0).\n", gpr_addr));

    a_xsecure_rf_ecc_gpr_reset_value_rvfi_rs2: assert property (
      p_gpr_reset_rvfi(
        rvfi_if.rvfi_rs2_addr,
        gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("GPR %0d is not set to 0 when exiting reset stage (as RS2 is not 0).\n", gpr_addr));

  end endgenerate //gen_gpr_reset_value


  //Verify that the GPRs and their ECC values have not all bits set to 0s or all bits set to 1s in the same clock cycle

  generate for (genvar gpr_addr = 1; gpr_addr < 32; gpr_addr++) begin : gen_gpr_not_1s_or_0s

    a_xsecure_rf_ecc_gpr_not_all_0s_or_1s: assert property (
      gpr_mem[gpr_addr] != '0
      && gpr_mem[gpr_addr] != '1
    ) else `uvm_error(info_tag, $sformatf("The value of GPR %0d is all %0s.\n", gpr_addr, gpr_mem[gpr_addr][0]));

  end endgenerate //gen_gpr_not_1s_or_0s


  //Verify that we set major alert if the the register sources' values and corresponding ECC score have all bits set to 0s or 1s

  generate for (genvar gpr_addr = 1; gpr_addr < 32; gpr_addr++) begin : gen_gpr_1s_or_0s

    a_glitch_xsecure_rf_gpr_not_all_0s_or_1s: assert property (
      (rs1 == gpr_addr
      || rs2 == gpr_addr)

      && (gpr_mem[gpr_addr] == '0
      || gpr_mem[gpr_addr] == '1)

      |=>
      alert_major

    ) else `uvm_error(info_tag_glitch, $sformatf("The value of GPR %0d is all %0s, and major alert is not set.\n", gpr_addr, gpr_mem[gpr_addr][0]));

  end endgenerate //gen_gpr_1s_or_0s




  //Verify that decoding missmatch of 1 og 2 bits sets major alert

  /****************************************
  Support logic:
  The support logic creates a local memory that shadowes the GPR
  In the local memory, we insert data in the same manner as for the GPRs.
  We detect bit flip in the GPRs by comparing them with the local memory
  ****************************************/

  logic [31:0][31:0] gpr_mem_shadow;

  always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
      gpr_mem_shadow = '0;
    end else if (gpr_we && gpr_waddr != ZERO) begin
      gpr_mem_shadow[gpr_waddr] = gpr_wdata;
    end
  end

  //Verify that support logic work as expected:

  a_xsecure_rf_ecc_reset_gpr_mem_shadow: assert property (
    ##0
    $rose(rst_ni)
    |->
    gpr_mem_shadow == '0

  ) else `uvm_error(info_tag, "The local support memory is not set to 0s when exiting reset.\n");


  a_xsecure_rf_ecc_update_gpr_mem_shadow: assert property (

    gpr_we
    && gpr_waddr != ZERO
    |=>
    gpr_mem_shadow[$past(gpr_waddr)] == $past(gpr_wdata)

  ) else `uvm_error(info_tag, "The support logic does not update the local memory in the same manner as the GPRs.\n");


  //Verify requirements:

  property p_rs_bit_fault(rs_addr, gpr_addr);

    rs_addr == gpr_addr
    && ($countbits(gpr_mem[gpr_addr][(REG_SIZE-1) -:REG_SIZE] ^ gpr_mem_shadow[gpr_addr], '1) inside {1,2})
    |=>
    alert_major;

  endproperty


  generate for (genvar gpr_addr = 1; gpr_addr < 32; gpr_addr++) begin : gen_gpr_bit_faults

    a_glitch_xsecure_rf_ecc_rs1_bit_fault: assert property (
      p_rs_bit_fault(
        rs1,
        gpr_addr)
    ) else `uvm_error(info_tag_glitch, $sformatf("1 or 2 bit errors when reading RS1 (address %0d) do not set the alert major.\n", gpr_addr));

    a_glitch_xsecure_rf_ecc_rs2_bit_fault: assert property (
      p_rs_bit_fault(
        rs2,
        gpr_addr)
    ) else `uvm_error(info_tag_glitch, $sformatf("1 or 2 bit errors when reading RS2 (address %0d) do not set the alert major.\n", gpr_addr));

  end endgenerate //gen_gpr_bit_faults

  endmodule : uvmt_cv32e40s_xsecure_register_file_ecc_assert
