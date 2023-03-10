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


module  uvmt_cv32e40s_pma_cov #(
  parameter int  PMA_NUM_REGIONS
)(
  input wire  clk,
  input wire  rst_n
);


  default clocking @(posedge clk); endclocking
  default disable iff !rst_n;


  covergroup cg @(posedge clk);
    option.per_instance = 1;
    option.detect_overlap = 1;

    cp_TODO: coverpoint  PMA_NUM_REGIONS {
      bins zero = {0};
      bins mid  = {[1:15]};
      bins max  = {16};
    }

  endgroup

  cg  cg_inst = new;


endmodule : uvmt_cv32e40s_pma_cov


`default_nettype wire
