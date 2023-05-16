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


module  uvmt_cv32e40s_pma_model
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
#(
  parameter logic [31:0]  DM_REGION_START,
  parameter logic [31:0]  DM_REGION_END,
  parameter bit           IS_INSTR_SIDE,
  parameter int           PMA_NUM_REGIONS,
  parameter pma_cfg_t     PMA_CFG [PMA_NUM_REGIONS-1:0]
)(
  input wire  clk,
  input wire  rst_n,

  input wire         core_trans_pushpop_i,
  input wire         dbg,
  input wire         load_access,
  input wire         misaligned_access_i,
  input wire [31:0]  addr_i,
  input wire jvt_t   jvt_q,

  output wire pma_status_t  pma_status_o
);


  localparam int  MAX_REGIONS = 16;

  localparam pma_cfg_t  CFG_DEFAULT = '{
    default : '0,
    main    : (PMA_NUM_REGIONS == 0)
  };

  localparam pma_cfg_t  CFG_DEBUG = '{
    default : '0,
    main    : 1'b 1
  };

  var logic [PMA_MAX_REGIONS-1:0]  match_list;
  function automatic logic  is_match_on(int i);
    logic [33:0]  low  = {PMA_CFG[i].word_addr_low,  2'b 00};
    logic [33:0]  high = {PMA_CFG[i].word_addr_high, 2'b 00};
    return ((low <= addr_i) && (addr_i < high));
  endfunction
  for (genvar i = 0; i < MAX_REGIONS; i++) begin: gen_match_list
    always_comb  match_list[i] = (i < PMA_NUM_REGIONS) && is_match_on(i);
  end

  var pma_cfg_t    cfg_matched;
  var logic        have_match;
  var logic[31:0]  match_idx;
  always_comb  begin
    have_match   = '0;
    cfg_matched  = 'X;
    match_idx    = 'X;
    for (int i = 0; i < PMA_NUM_REGIONS; i++) begin
      if (pma_status_o.match_list[i]) begin
        have_match   = 1;
        cfg_matched  = PMA_CFG[i];
        match_idx    = i;
        break;
      end
    end
  end


  wire logic  accesses_dmregion;
  assign  accesses_dmregion =
    ((DM_REGION_START <= addr_i) && (addr_i <= DM_REGION_END));

  wire logic  override_dm;
  assign  override_dm = dbg && accesses_dmregion;

  var pma_cfg_t  cfg_effective;
  always_comb  begin
    cfg_effective =
      override_dm
        ? CFG_DEBUG
        : (have_match ? cfg_matched : CFG_DEFAULT);

    cfg_effective.bufferable =
      cfg_effective.bufferable && !IS_INSTR_SIDE && !load_access;
  end

  wire logic  allow_instr;
  assign  allow_instr = cfg_effective.main;

  wire logic  allow_data;
  assign  allow_data =
    cfg_effective.main  ||
    (!misaligned_access_i && !core_trans_pushpop_i);

  wire logic  accesses_jvt;
  assign  accesses_jvt =
    (jvt_q <= addr_i)  &&
    (addr_i <= (jvt_q + (4 * 8'b 1111_1111)));

  assign  pma_status_o.allow =
    override_dm  ||
    (IS_INSTR_SIDE ? allow_instr : allow_data);
  assign  pma_status_o.main              = cfg_effective.main;
  assign  pma_status_o.bufferable        = cfg_effective.bufferable;
  assign  pma_status_o.cacheable         = cfg_effective.cacheable;
  assign  pma_status_o.integrity         = cfg_effective.integrity;
  assign  pma_status_o.override_dm       = override_dm;
  assign  pma_status_o.accesses_dmregion = accesses_dmregion;
  assign  pma_status_o.accesses_jvt      = accesses_jvt;
  assign  pma_status_o.match_list        = match_list;
  assign  pma_status_o.have_match        = have_match;
  assign  pma_status_o.match_idx         = match_idx;


endmodule : uvmt_cv32e40s_pma_model


`default_nettype wire
