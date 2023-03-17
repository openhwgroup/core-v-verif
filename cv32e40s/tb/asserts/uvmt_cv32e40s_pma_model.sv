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
  import uvmt_cv32e40s_pkg::*;
#(
  parameter type          CORE_REQ_TYPE,
  parameter logic [31:0]  DM_REGION_START,
  parameter logic [31:0]  DM_REGION_END,
  parameter bit           IS_INSTR_SIDE,
  parameter int           PMA_NUM_REGIONS,
  parameter pma_cfg_t     PMA_CFG [PMA_NUM_REGIONS-1:0]
)(
  input wire  clk,
  input wire  rst_n,

  input CORE_REQ_TYPE  core_trans_i,
  input wire [31:0]    addr_i,
  input wire           misaligned_access_i,
  input wire           core_trans_pushpop_i,
  input wire           load_access,

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

  wire logic [MAX_REGIONS-1:0]  matching_states;
  function automatic logic  is_match_on(int i);
    logic [33:0]  low  = {PMA_CFG[i].word_addr_low,  2'b 00};
    logic [33:0]  high = {PMA_CFG[i].word_addr_high, 2'b 00};
    return ((low <= addr_i) && (addr_i < high));
  endfunction
  for (genvar i = 0; i < MAX_REGIONS; i++) begin: gen_matching_states
    assign  matching_states[i] = (i < PMA_NUM_REGIONS) && is_match_on(i);
  end

  var logic      have_region_match;
  var pma_cfg_t  matched_region;
  var int        matched_index;
  always_comb  begin
    have_region_match = '0;
    matched_region    = 'X;
    matched_index     = 'X;
    for (int i = 0; i < PMA_NUM_REGIONS; i++) begin
      if (matching_states[i]) begin
        have_region_match = 1;
        matched_region    = PMA_CFG[i];
        matched_index     = i;
        break;
      end
    end
  end

  wire logic  override_dm;
  assign  override_dm =
    core_trans_i.dbg  &&
    ((DM_REGION_START <= addr_i) && (addr_i <= DM_REGION_END));

  var pma_cfg_t  cfg_effective;
  always_comb  begin
    cfg_effective =
      override_dm
        ? CFG_DEBUG
        : (have_region_match ? matched_region : CFG_DEFAULT);

    cfg_effective.bufferable =
      cfg_effective.bufferable && !IS_INSTR_SIDE && !load_access;
  end

  wire logic  allow_instr;
  assign  allow_instr = cfg_effective.main;

  wire logic  allow_data;
  assign  allow_data =
    cfg_effective.main  ||
    (!misaligned_access_i && !core_trans_pushpop_i);

  assign  pma_status_o.allow =
    override_dm  ||
    (IS_INSTR_SIDE ? allow_instr : allow_data);
  assign  pma_status_o.bufferable = cfg_effective.bufferable;
  assign  pma_status_o.cacheable  = cfg_effective.cacheable;
  assign  pma_status_o.integrity  = cfg_effective.integrity;


endmodule : uvmt_cv32e40s_pma_model


`default_nettype wire
