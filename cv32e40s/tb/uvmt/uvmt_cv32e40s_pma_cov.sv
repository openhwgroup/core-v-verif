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


module  uvmt_cv32e40s_pma_cov
  import uvmt_cv32e40s_pkg::*;
#(
  parameter int  PMA_NUM_REGIONS,
  parameter bit  IS_INSTR_SIDE
)(
  input wire  clk,
  input wire  rst_n,

  input wire  core_trans_ready_o,
  input wire  core_trans_valid_i,
  input wire  misaligned_access_i,
  input wire  load_access,

  input wire pma_status_t  pma_status_i
);


  // Helper Logic - Match Info

  wire logic [31:0]  num_matches;
  assign  num_matches = $countones(pma_status_i.match_list);

  let  have_match = pma_status_i.have_match;
  let  match_idx  = pma_status_i.match_idx;


  // Helper Logic - MPU Activation

  wire logic  is_mpu_activated;
  assign  is_mpu_activated = (core_trans_ready_o && core_trans_valid_i);


  // Coverage Definitions

  covergroup cg @(posedge clk);
    option.per_instance = 1;
    option.detect_overlap = 1;

    // vplan:"Valid number of regions"
    cp_numregions: coverpoint  PMA_NUM_REGIONS {
      bins zero = {0}      with (PMA_NUM_REGIONS == 0);
      bins mid  = {[1:15]} with ((0 < PMA_NUM_REGIONS) && (PMA_NUM_REGIONS < 16));
      bins max  = {16}     with (PMA_NUM_REGIONS == 16);
    }

    // vplan:"Overlapping PMA Regions"
    cp_multimatch: coverpoint  num_matches  iff (is_mpu_activated) {
      bins zero = {0};
      bins one  = {1}                   with (0 < PMA_NUM_REGIONS);
      bins many = {[2:PMA_NUM_REGIONS]} with (1 < PMA_NUM_REGIONS);
    }

    // vplan:TODO
    cp_matchregion: coverpoint  match_idx  iff (is_mpu_activated) {
      bins           regions[] = {[0:PMA_NUM_REGIONS-1]}  iff (have_match == 1);
      wildcard bins  nomatch   = {'X}                     iff (have_match == 0);
    }

    // vplan:TODO
    cp_aligned: coverpoint  misaligned_access_i  iff (is_mpu_activated) {
      bins          misaligned = {1} with (!IS_INSTR_SIDE);
      illegal_bins  illegal    = {1} with ( IS_INSTR_SIDE);
      bins          aligned    = {0};
    }

    // vplan:TODO
    cp_loadstoreexec: coverpoint  load_access  iff (is_mpu_activated) {
      bins           load  = {1}  with (!IS_INSTR_SIDE);
      bins           store = {0}  with (!IS_INSTR_SIDE);
      wildcard bins  exec  = {'X} with ( IS_INSTR_SIDE);
    }

    // vplan:TODO
    cp_main:        coverpoint  pma_status_i.main         iff (is_mpu_activated);
    cp_bufferable:  coverpoint  pma_status_i.bufferable   iff (is_mpu_activated) {
      bins          bufferable    = {1} with (!IS_INSTR_SIDE);
      illegal_bins  illegal       = {1} with ( IS_INSTR_SIDE);
      bins          nonbufferable = {0};
    }
    cp_cacheable:   coverpoint  pma_status_i.cacheable    iff (is_mpu_activated);
    cp_integrity:   coverpoint  pma_status_i.integrity    iff (is_mpu_activated);
    cp_override_dm: coverpoint  pma_status_i.override_dm  iff (is_mpu_activated);
  endgroup

  cg  cg_inst = new;


endmodule : uvmt_cv32e40s_pma_cov


`default_nettype wire
