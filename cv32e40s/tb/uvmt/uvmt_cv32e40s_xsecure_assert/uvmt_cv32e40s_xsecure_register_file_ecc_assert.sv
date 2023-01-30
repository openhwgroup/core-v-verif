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


module uvmt_cv32e40s_xsecure_register_file_ecc_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
   uvmt_cv32e40s_xsecure_if xsecure_if,
   uvma_rvfi_instr_if rvfi_if,
   input rst_ni,
   input clk_i
  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) | !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";
  string info_tag_glitch = "CV32E40S_XSECURE_ASSERT_COVERPOINTS (GLITCH BEHAVIOR)";


  ////////// GENERAL PURPOSE REGISTERS ARE ZERO WHEN EXITING RESET //////////

  //Check that the GPR is reset to 0 when exiting the reset stage:
  property p_xsecure_gpr_reset(integer register_addr);
    //Make sure we are going out of reset
    $rose(rst_ni)

    //Make sure the general purpose register of address <register_addr> is reset to zero
    |->
    xsecure_if.core_register_file_wrapper_register_file_mem[register_addr][31:0] == 32'h0000_0000

    //Make sure the ECC score of the general purpose register of address "register_addr" is the ECC encoding of the value zero
    && xsecure_if.core_register_file_wrapper_register_file_mem[register_addr][37:32] == 6'h2a;

  endproperty


  //Use RVFI to check that RS1 has a value of 0 when exiting the reset stage:
  property p_xsecure_gpr_reset_rvfi_rs1(integer gpr_addr);

    //Make sure we check out the first instruction after the reset stage
    $rose(rst_ni) ##0 rvfi_if.rvfi_valid[->1]

    //Make sure the instruction reads the RS1 value
    ##0 rvfi_if.rvfi_rs1_addr == gpr_addr

    |->
    //Make sure the RS1 value is 0
    rvfi_if.rvfi_rs1_rdata == 32'h0000_0000;

  endproperty


  //Use RVFI to check that RS2 has a value of 0 when exiting the reset stage:
  property p_xsecure_gpr_reset_rvfi_rs2(integer gpr_addr);

    //Make sure we check out the first instruction after the reset stage
    $rose(rst_ni) ##0 rvfi_if.rvfi_valid[->1]

    //Make sure the instruction reads the RS1 value
    ##0 rvfi_if.rvfi_rs2_addr == gpr_addr

    |->
    //Make sure the RS2 value is 0
    rvfi_if.rvfi_rs2_rdata == 32'h0000_0000;

  endproperty


  //Make reset assertions for each GPR:
  generate for (genvar gpr_addr = 0; gpr_addr < 32; gpr_addr++) begin

    a_xsecure_register_file_ecc_gpr_reset_value: assert property (
      p_xsecure_gpr_reset(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("GPR %0d is not set to 0 when exiting reset stage, or the syndrome is not 0x2a.\n", gpr_addr));

    a_xsecure_register_file_ecc_gpr_reset_value_rvfi_rs1: assert property (
      p_xsecure_gpr_reset_rvfi_rs1(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("GPR %0d is not set to 0 when exiting reset stage (as RS1 is not 0).\n", gpr_addr));

    a_xsecure_register_file_ecc_gpr_reset_value_rvfi_rs2: assert property (
      p_xsecure_gpr_reset_rvfi_rs2(gpr_addr)
    ) else `uvm_error(info_tag, $sformatf("GPR %0d is not set to 0 when exiting reset stage (as RS2 is not 0).\n", gpr_addr));

  end endgenerate


  ////////// GENERAL PURPOSE REGISTERS AND ECC ATTACHMENTS ARE NEVER ALL ZEROS OR ONES //////////

  property p_gpr_x_syndrom_not_x(gpr_addr, x);
    xsecure_if.core_register_file_wrapper_register_file_mem[gpr_addr][31:0] == {32{x}}
    |->
    xsecure_if.core_register_file_wrapper_register_file_mem[gpr_addr][37:32] != {6{x}};
  endproperty

  property p_syndrom_x_gpr_not_x(gpr_addr, x);
    xsecure_if.core_register_file_wrapper_register_file_mem[gpr_addr][37:32] == {6{x}}
    |->
    xsecure_if.core_register_file_wrapper_register_file_mem[gpr_addr][31:0] != {32{x}};
  endproperty


  //Make assertions for each GPR:
  generate for (genvar gpr_addr = 1; gpr_addr < 32; gpr_addr++) begin

    a_xsecure_register_file_ecc_gprecc_never_all_zeros_part_1: assert property (
      p_gpr_x_syndrom_not_x(
        gpr_addr,
        1'b0)
    ) else `uvm_error(info_tag, $sformatf("The value of GPR %0d \"equals\" its syndrome, and is all 0s.\n", gpr_addr));

    a_xsecure_register_file_ecc_gprecc_never_all_zeros_part_2: assert property (
      p_syndrom_x_gpr_not_x(
        gpr_addr,
        1'b0)
    ) else `uvm_error(info_tag, $sformatf("The value of GPR %0d \"equals\" its syndrome, and is all 0s.\n", gpr_addr));

    a_xsecure_register_file_ecc_gprecc_never_all_ones_part_1: assert property (
      p_gpr_x_syndrom_not_x(
        gpr_addr,
        1'b1)
    ) else `uvm_error(info_tag, $sformatf("The value of GPR %0d \"equals\" its syndrome, and is all 1s.\n", gpr_addr));

    a_xsecure_register_file_ecc_gprecc_never_all_ones_part_2: assert property (
      p_syndrom_x_gpr_not_x(
        gpr_addr,
        1'b1)
    ) else `uvm_error(info_tag, $sformatf("The value of GPR %0d \"equals\" its syndrome, and is all 1s.\n", gpr_addr));

  end endgenerate


  ////////// IF GENERAL PURPOSE REGISTERS AND ECC ATTACHMENTS ARE ALL ZEROS OR ONES MAJOR ALERT MUST BE SET ////////// //TODO: fix

  property p_gpr_and_syndrom_x_set_major_alert(gpr_addr, x);
    //Make sure we are in a state where we read the gpr word
    (xsecure_if.if_id_pipe_rs1 == gpr_addr
    || xsecure_if.if_id_pipe_rs2 == gpr_addr)

    //Make sure the bits in the register word and the syndrom are all x.
    && xsecure_if.core_register_file_wrapper_register_file_mem[gpr_addr][37:0] == {32{x}}

    |=>
    //Verify that the alert major is set
    xsecure_if.core_alert_major_o;
  endproperty

  //Make assertions for each GPR:
  generate for (genvar gpr_addr = 1; gpr_addr < 32; gpr_addr++) begin

    a_glitch_xsecure_register_file_ecc_gpr_and_syndrome_all_zeros_set_major_alert: assert property (
      p_gpr_and_syndrom_x_set_major_alert(
        gpr_addr,
        1'b0)
    ) else `uvm_error(info_tag, $sformatf("The value of GPR %0d \"equals\" its syndrome, and is all 0s, but the alert major is not set.\n", gpr_addr));

    a_glitch_xsecure_register_file_ecc_gpr_and_syndrome_all_ones_set_major_alert: assert property (
      p_gpr_and_syndrom_x_set_major_alert(
        gpr_addr,
        1'b1)
    ) else `uvm_error(info_tag, $sformatf("The value of GPR %0d \"equals\" its syndrome, and is all 1s, but the alert major is not set.\n", gpr_addr));

  end endgenerate


  ////////// ECC DECODING MISMATCH ON EVERY READ SETS MAJOR ALERT //////////

  /****************************************
  Support logic:
  The support logic creates a local memory that shadowes the GPR
  In the local memory, we insert data in the same manner as for the GPRs.
  We detect bit flip in the GPRs by comparing them with the local memory
  ****************************************/

  //Local memory for the support logic
  logic [31:0][31:0] gpr_shadow = '0;

  //Make sure the local memory is updated whenever the GPR memory is updated
  always @(posedge clk_i) begin
    if(!rst_ni) begin
      gpr_shadow = '0;
    end else if (xsecure_if.core_rf_we_wb && xsecure_if.core_rf_waddr_wb != 5'b00000) begin
      gpr_shadow[xsecure_if.core_rf_waddr_wb] = xsecure_if.core_rf_wdata_wb;
    end
  end


  //Make sure the support logic works as expected when updating the memory
  a_xsecure_register_file_ecc_no_supression_by_comparing_ecc_scores_support_logic: assert property (

    //Make sure we update the GPR memory
    xsecure_if.core_rf_we_wb

    //Make sure the address is not x0
    && xsecure_if.core_rf_waddr_wb != 5'b00000

    |=>
    //Make sure the local memory is updated in the same manner as the gpr memory
    gpr_shadow[$past(xsecure_if.core_rf_waddr_wb)] == $past(xsecure_if.core_rf_wdata_wb)

  ) else `uvm_error(info_tag, "The support logic does not update the local memory in the same manner as the GPRs.\n");


  //Make sure the support logic works as expected when exiting reset mode
  a_xsecure_register_file_ecc_no_supression_by_comparing_ecc_scores_support_logic_start_at_zero: assert property (

    //Exit reset mode
    $rose(rst_ni)

    //Check that the local memory is set to 0s
    |->
    gpr_shadow == '0

  ) else `uvm_error(info_tag, "The local support memory is not set to 0s when exiting reset.\n");


  property p_xsecure_register_file_ecc_no_supression_reading_rs1(rs1_addr);

    //Specify the RS1 address
    xsecure_if.if_id_pipe_rs1 == rs1_addr

    //Make sure the GPR memory and the local memory differ in one or two bits
    && ($countbits(xsecure_if.core_register_file_wrapper_register_file_mem[rs1_addr][31:0] ^ gpr_shadow[rs1_addr], '1) inside {1,2})

    |=>
    //Make sure the alert major is set
    xsecure_if.core_alert_major_o;
  endproperty

  property p_xsecure_register_file_ecc_no_supression_reading_rs2(rs2_addr);

    //Specify the RS2 address
    xsecure_if.if_id_pipe_rs2 == rs2_addr

    //Make sure the GPR memory and the local memory differ in one or two bits
    && ($countbits(xsecure_if.core_register_file_wrapper_register_file_mem[rs2_addr][31:0] ^ gpr_shadow[rs2_addr], '1) inside {1,2})

    |=>
    //Make sure the alert major is set
    xsecure_if.core_alert_major_o;
  endproperty

  generate for (genvar gpr_addr = 1; gpr_addr < 32; gpr_addr++) begin

    a_glitch_xsecure_register_file_ecc_no_supression_reading_rs1: assert property (
      p_xsecure_register_file_ecc_no_supression_reading_rs1(
        gpr_addr)
    ) else `uvm_error(info_tag_glitch, $sformatf("1 or 2 bit errors when reading RS1 (address %0d) do not set the alert major.\n", gpr_addr));

    a_glitch_xsecure_register_file_ecc_no_supression_reading_rs2: assert property (
      p_xsecure_register_file_ecc_no_supression_reading_rs2(
        gpr_addr)
    ) else `uvm_error(info_tag_glitch, $sformatf("1 or 2 bit errors when reading RS2 (address %0d) do not set the alert major.\n", gpr_addr));

  end endgenerate


  endmodule : uvmt_cv32e40s_xsecure_register_file_ecc_assert