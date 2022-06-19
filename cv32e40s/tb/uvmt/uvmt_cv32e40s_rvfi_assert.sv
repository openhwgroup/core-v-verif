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


module uvmt_cv32e40s_rvfi_assert
  import cv32e40s_pkg::*;
  import uvm_pkg::*;
(
  input  clk_i,
  input  rst_ni,

  input         rvfi_valid,
  input [ 4:0]  rvfi_rs1_addr,
  input [ 4:0]  rvfi_rs2_addr,
  input [31:0]  rvfi_rs1_rdata,
  input [31:0]  rvfi_rs2_rdata
);

  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;
  string info_tag = "CV32E40S_RVFI_ASSERT";


  // rs1/rs2 Reset Values

  property p_rs_resetvalue (addr, rdata);
    $past(rst_ni == 0)  ##0
    (rvfi_valid [->1])  ##0
    addr
    |->
    (rdata == 0);  // TODO:ropeders use "RF_REG_RV"
  endproperty : p_rs_resetvalue

  a_rs1_resetvalue: assert property (
    p_rs_resetvalue(rvfi_rs1_addr, rvfi_rs1_rdata)
  ) else `uvm_error(info_tag, "TODO");

  a_rs2_resetvalue: assert property (
    p_rs_resetvalue(rvfi_rs2_addr, rvfi_rs2_rdata)
  ) else `uvm_error(info_tag, "TODO");

endmodule : uvmt_cv32e40s_rvfi_assert
