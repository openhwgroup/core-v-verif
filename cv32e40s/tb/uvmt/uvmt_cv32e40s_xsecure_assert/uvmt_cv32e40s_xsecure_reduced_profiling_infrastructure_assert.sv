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


module uvmt_cv32e40s_xsecure_reduced_profiling_infrastructure_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
  )
  (
    input rst_ni,
    input clk_i,

    //CSRs:
    input logic [31:0][31:0] mhpmevent,
    input logic [31:0][63:0] mhpmcounter,
    input logic [31:0] mcountinhibit

  );

  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) || !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";

  localparam ZERO = 0;


  //Verify that the following bits in these CSRs are hardwired to 0:
  //- mphmevent: 3 to 31
  //- mcountinhibit: 1 and 3 to 31

  //And that the following CSRs are tied to 0:
  //- mphmcounter3,
  //- mphmcounter4,
  //...
  //- mphmcounter31,
  //- mhpmcounterh3,
  //- mhpmcounterh4,
  //...
  //- mhpmcounterh31


  a_xsecure_reduced_profiling_mhpmevent: assert property (

    mhpmevent[31:3] == ZERO

  ) else `uvm_error(info_tag, "The MHPMEVENT registers 31 to 3 are not hardwired to zero.\n");


  a_xsecure_reduced_profiling_mhpmcounter: assert property (

    //Note that the mhpmcounter signal contain both the mhpmcounter and mhpmcounterh bits
    mhpmcounter[31:3] == ZERO

  ) else `uvm_error(info_tag, "The MHPMCOUNTER and MHPMCOUNTERH registers 31 to 3 are not hardwired to zero.\n");


  a_xsecure_reduced_profiling_mcountinhibit: assert property (

    mcountinhibit[1] == ZERO
    && mcountinhibit[31:3] == ZERO

  ) else `uvm_error(info_tag, "The MHPMCOUNTINHIBIT registers 1, and 3 to 31 are not hardwired to zero.\n");


  endmodule : uvmt_cv32e40s_xsecure_reduced_profiling_infrastructure_assert

