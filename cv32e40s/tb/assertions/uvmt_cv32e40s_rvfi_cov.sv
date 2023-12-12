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


module  uvmt_cv32e40s_rvfi_cov
  import cv32e40s_pkg::*;
(
  input wire  clk_i,
  input wire  rst_ni,

  uvma_rvfi_instr_if_t  rvfi_if
);


  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;


  // Aliases

  let  mem_rmask = rvfi_if.rvfi_mem_rmask;
  let  mem_wmask = rvfi_if.rvfi_mem_wmask;


  // Mem access split in two OBI transactions

  cov_split_data: cover property (
    rvfi_if.is_split_datatrans_intended  &&
    !rvfi_if.rvfi_trap
  );


  // Pushpop instrs

  cov_pushpop: cover property (
    rvfi_if.is_pushpop  &&
    !rvfi_if.rvfi_trap  &&
    ((mem_rmask | mem_wmask) > 'h FF)
  );


  // Table Jump

  cov_tablejump_notrap: cover property (
    rvfi_if.is_tablejump_raw  &&
    !rvfi_if.rvfi_trap
  );

  cov_tablejump_exception: cover property (
    rvfi_if.is_tablejump_raw  &&
    rvfi_if.rvfi_trap.exception
  );


endmodule : uvmt_cv32e40s_rvfi_cov


`default_nettype wire
