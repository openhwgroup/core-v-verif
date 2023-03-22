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


// Description:
//   Coverage definitions for RVFI; mainly the support logic.
//
// Rationale:
//   The RVFI support logic has many useful functions.
//   They should be coverable in both formal and sim.
//   They should be inspected in formal to see that they work as intended.


`default_nettype none


module  uvmt_cv32e40s_rvfi_cov (
  input wire  clk_i,
  input wire  rst_ni,

  uvma_rvfi_instr_if  rvfi_if
);


  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;


  // Cover mem access split in two OBI transactions

  cov_split_data: cover property (
    rvfi_if.is_split_datatrans()  &&
    !rvfi_if.rvfi_trap
  );


endmodule : uvmt_cv32e40s_rvfi_cov


`default_nettype wire
