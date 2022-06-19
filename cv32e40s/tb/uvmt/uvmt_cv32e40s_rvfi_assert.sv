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
  input clk_i,
  input rst_ni
);

  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;
  string info_tag = "CV32E40S_RVFI_ASSERT";

  a_TODO: assert property (
    0
  ) else `uvm_error(info_tag, "TODO");

endmodule : uvmt_cv32e40s_rvfi_assert
