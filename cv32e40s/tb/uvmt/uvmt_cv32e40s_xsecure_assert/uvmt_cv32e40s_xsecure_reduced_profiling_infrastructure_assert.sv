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


module uvmt_cv32e40s_xsecure_reduced_profiling_infrastructure_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  #(
    parameter int       SECURE   = 1
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


  a_xsecure_reduction_of_profiling_infrastructure_mhpmevent_31_to_3_are_zero: assert property (

    //Make sure the MHPMEVENT 3 to 31 are hardwired to zero
    |xsecure_if.core_cs_registers_mhpmevent_rdata_31_to_3 == 1'b0

  ) else `uvm_error(info_tag, "The MHPMEVENT registers 31 to 3 are not hardwired to zero.\n");


  a_xsecure_reduction_of_profiling_infrastructure_mhpmcounter_31_to_3_are_zero: assert property (

    //Make sure the MHPMCOUNTER 3 to 31 are hardwired to zero
    //(we include MHPMCOUNTERH in the MHPMCOUNTER signal)
    |xsecure_if.core_cs_registers_mhpmcounter_rdata_31_to_3 == 1'b0

  ) else `uvm_error(info_tag, "The MHPMCOUNTER and MHPMCOUNTERH registers 31 to 3 are not hardwired to zero.\n");


  a_xsecure_reduction_of_profiling_infrastructure_mcountinhibit_31_to_3_and_1_are_zero: assert property (

    //Make sure the MCOUNTINHIBIT 1 is hardwired to zero
    xsecure_if.core_cs_registers_mcountinhibit_rdata[1] == 1'b0

    //Make sure the MCOUNTINHIBIT bit 3 to 31 are hardwired to zero
    && xsecure_if.core_cs_registers_mcountinhibit_rdata[31:3] == '0

  ) else `uvm_error(info_tag, "The MHPMCOUNTINHIBIT registers 1, and 3 to 31 are not hardwired to zero.\n");


  endmodule : uvmt_cv32e40s_xsecure_reduced_profiling_infrastructure_assert