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


class  uvme_cv32e40s_vp_obi_err_await_goahead_seq_c
  extends  uvma_obi_memory_vp_base_seq_c #(
    .AUSER_WIDTH (ENV_PARAM_DATA_AUSER_WIDTH),
    .WUSER_WIDTH (ENV_PARAM_DATA_WUSER_WIDTH),
    .RUSER_WIDTH (ENV_PARAM_DATA_RUSER_WIDTH),
    .ADDR_WIDTH  (ENV_PARAM_DATA_ADDR_WIDTH),
    .DATA_WIDTH  (ENV_PARAM_DATA_DATA_WIDTH),
    .ID_WIDTH    (ENV_PARAM_DATA_ID_WIDTH),
    .ACHK_WIDTH  (ENV_PARAM_DATA_ACHK_WIDTH),
    .RCHK_WIDTH  (ENV_PARAM_DATA_RCHK_WIDTH)
  );

  `uvm_object_utils( uvme_cv32e40s_vp_obi_err_await_goahead_seq_c )

  uvma_obi_memory_cfg_c  obi_memory_cfg_instr;
  uvma_obi_memory_cfg_c  obi_memory_cfg_data;


  function new(string name="uvme_cv32e40s_vp_obi_err_await_goahead_seq_c");
    super.new(name);
  endfunction


  function int unsigned get_num_words();
    return 1;
  endfunction


  virtual task vp_body(uvma_obi_memory_mon_trn_c  mon_trn);
    uvma_obi_memory_slv_seq_item_c  slv_rsp;

    obi_memory_cfg_instr.random_err_await_goahead = 0;
    obi_memory_cfg_data.random_err_await_goahead  = 0;

    `uvm_create(slv_rsp)
    `uvm_send(slv_rsp)
  endtask


endclass
