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
//   NB! Assumes are dangerous.
//   Here is a collection of some assumes needed to have the environment usable.


`default_nettype none


module  uvmt_cv32e40s_assumes (
  input wire  clk_i,
  input wire  rst_ni,

  uvma_obi_memory_if  obi,
  uvma_rvfi_instr_if  rvfi,
  uvmt_cv32e40s_support_logic_for_assert_coverage_modules_if.slave_mp  sup
);


  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;


  // OBI doesn't stall forever

  asu_eventually_rvalid: assume property (
    (sup.instr_bus_v_addr_ph_cnt > 0)
    |->
    s_eventually  obi.rvalid
  );

  asu_eventually_gnt: assume property (
    obi.req
    |->
    s_eventually  obi.gnt
  );


endmodule : uvmt_cv32e40s_assumes


`default_nettype wire
