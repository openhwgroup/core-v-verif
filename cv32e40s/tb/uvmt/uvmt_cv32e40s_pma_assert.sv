// Copyright 2023 Silicon Labs, Inc.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0.
//
// You may obtain a copy of the License at
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.


`default_nettype none


module  uvmt_cv32e40s_pma_assert
  import uvm_pkg::*;
(
  input wire  clk,
  input wire  rst_n,

  input wire  pma_err,
  input wire  bus_trans_valid_o
);


  default clocking @(posedge clk); endclocking
  default disable iff !rst_n;

  string info_tag = "CV32E40S_PMA_ASSERT";


  // PMA-restricted regions deassert OBI req  (vplan:InstructionFetches:2)

  a_TODO: assert property (
    pma_err
    |->
    !bus_trans_valid_o
    //TODO:WARNING:silabs-robin Have not checked that "!trans -> !obi"
  ) else `uvm_error(info_tag, "TODO");


endmodule : uvmt_cv32e40s_pma_assert


`default_nettype wire
