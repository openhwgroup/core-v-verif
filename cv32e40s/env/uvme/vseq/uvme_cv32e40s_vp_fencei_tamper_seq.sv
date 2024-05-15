// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.


`ifndef __UVME_CV32E40S_VP_FENCEI_TAMPER_SEQ_SV__
`define __UVME_CV32E40S_VP_FENCEI_TAMPER_SEQ_SV__

//import rvviApiPkg::*; //TODO: conditionally include this?

class uvme_cv32e40s_vp_fencei_tamper_seq_c#(
   parameter AUSER_WIDTH = `UVMA_OBI_MEMORY_AUSER_DEFAULT_WIDTH, ///< Width of the auser signal. RI5CY, Ibex, CV32E40* do not have the auser signal.
   parameter WUSER_WIDTH = `UVMA_OBI_MEMORY_WUSER_DEFAULT_WIDTH, ///< Width of the wuser signal. RI5CY, Ibex, CV32E40* do not have the wuser signal.
   parameter RUSER_WIDTH = `UVMA_OBI_MEMORY_RUSER_DEFAULT_WIDTH, ///< Width of the ruser signal. RI5CY, Ibex, CV32E40* do not have the ruser signal.
   parameter ADDR_WIDTH  = `UVMA_OBI_MEMORY_ADDR_DEFAULT_WIDTH , ///< Width of the addr signal.
   parameter DATA_WIDTH  = `UVMA_OBI_MEMORY_DATA_DEFAULT_WIDTH , ///< Width of the rdata and wdata signals. be width is DATA_WIDTH / 8. Valid DATA_WIDTH settings are 32 and 64.
   parameter ID_WIDTH    = `UVMA_OBI_MEMORY_ID_DEFAULT_WIDTH   , ///< Width of the aid and rid signals.
   parameter ACHK_WIDTH  = `UVMA_OBI_MEMORY_ACHK_DEFAULT_WIDTH , ///< Width of the achk signal.
   parameter RCHK_WIDTH  = `UVMA_OBI_MEMORY_RCHK_DEFAULT_WIDTH   ///< Width of the rchk signal.
) extends uvma_obi_memory_vp_base_seq_c#(
   .AUSER_WIDTH(AUSER_WIDTH),
   .WUSER_WIDTH(WUSER_WIDTH),
   .RUSER_WIDTH(RUSER_WIDTH),
   .ADDR_WIDTH(ADDR_WIDTH),
   .DATA_WIDTH(DATA_WIDTH),
   .ID_WIDTH(ID_WIDTH),
   .ACHK_WIDTH(ACHK_WIDTH),
   .RCHK_WIDTH(RCHK_WIDTH)
);

  uvme_cv32e40s_cntxt_c  cv32e40s_cntxt;

  bit        enabled = 0;
  bit [31:0] addr;
  bit [31:0] data;

  `uvm_object_utils(uvme_cv32e40s_vp_fencei_tamper_seq_c#(
    .AUSER_WIDTH(AUSER_WIDTH),
    .WUSER_WIDTH(WUSER_WIDTH),
    .RUSER_WIDTH(RUSER_WIDTH),
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .ID_WIDTH(ID_WIDTH),
    .ACHK_WIDTH(ACHK_WIDTH),
    .RCHK_WIDTH(RCHK_WIDTH)
  ))

  extern function new(string name="uvme_cv32e40s_vp_fencei_tamper_seq_c");
  extern virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);
  extern virtual function int unsigned get_num_words();
  extern virtual task body();
  extern function void write_rtl_mem();
  extern function void write_iss_mem();

endclass : uvme_cv32e40s_vp_fencei_tamper_seq_c


function uvme_cv32e40s_vp_fencei_tamper_seq_c::new(string name="uvme_cv32e40s_vp_fencei_tamper_seq_c");

  super.new(name);

endfunction : new


task uvme_cv32e40s_vp_fencei_tamper_seq_c::vp_body(uvma_obi_memory_mon_trn_c mon_trn);

  uvma_obi_memory_slv_seq_item_c  slv_rsp;

  `uvm_create(slv_rsp)
  slv_rsp.orig_trn = mon_trn;
  slv_rsp.err = 1'b0;

  if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
    case (get_vp_index(mon_trn))
      0: enabled = | mon_trn.data;
      1: addr = mon_trn.data;
      2: data = mon_trn.data;
    endcase
  end

  add_r_fields(mon_trn, slv_rsp);
  slv_rsp.set_sequencer(p_sequencer);
  `uvm_send(slv_rsp)

endtask : vp_body


function int unsigned uvme_cv32e40s_vp_fencei_tamper_seq_c::get_num_words();

   return 3;

endfunction : get_num_words


task uvme_cv32e40s_vp_fencei_tamper_seq_c::body();

  if (cv32e40s_cntxt == null) begin
    `uvm_fatal("E40SVPSTATUS", "Must initialize cv32e40s_cntxt in virtual peripheral");
  end
  if (cv32e40s_cntxt.fencei_cntxt == null) begin
    `uvm_fatal("E40SVPSTATUS", "Must initialize fencei_cntxt in virtual peripheral");
  end
  if (cv32e40s_cntxt.fencei_cntxt.fencei_vif == null) begin
    `uvm_fatal("E40SVPSTATUS", "Must initialize fencei_vif in virtual peripheral");
  end

  fork
    while (1) begin
      @(posedge cv32e40s_cntxt.fencei_cntxt.fencei_vif.flush_req);
      if (enabled) begin
        write_rtl_mem();
        write_iss_mem();
      end
    end
  join_none

  super.body();

endtask : body


function void uvme_cv32e40s_vp_fencei_tamper_seq_c::write_rtl_mem();

  cntxt.mem.write((addr + 0), data[ 7: 0]);
  cntxt.mem.write((addr + 1), data[15: 8]);
  cntxt.mem.write((addr + 2), data[23:16]);
  cntxt.mem.write((addr + 3), data[31:24]);

endfunction : write_rtl_mem

function void uvme_cv32e40s_vp_fencei_tamper_seq_c::write_iss_mem();

  if ($test$plusargs("USE_ISS")) begin
    //rvviRefMemoryWrite(0, addr, data, 4); // TODO: conditionally include this
  end

endfunction : write_iss_mem


`endif // __UVME_OBI_MEMORY_VP_FENCEI_TAMPER_SEQ_SV__
