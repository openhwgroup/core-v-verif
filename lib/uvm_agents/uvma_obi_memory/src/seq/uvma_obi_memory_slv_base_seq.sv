//
// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
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
//


`ifndef __UVMA_OBI_MEMORY_SLV_BASE_SEQ_SV__
`define __UVMA_OBI_MEMORY_SLV_BASE_SEQ_SV__


/**
 * TODO Describe uvma_obi_memory_slv_base_seq_c
 */
class uvma_obi_memory_slv_base_seq_c#(
   parameter AUSER_WIDTH = `UVMA_OBI_MEMORY_AUSER_DEFAULT_WIDTH, ///< Width of the auser signal. RI5CY, Ibex, CV32E40* do not have the auser signal.
   parameter WUSER_WIDTH = `UVMA_OBI_MEMORY_WUSER_DEFAULT_WIDTH, ///< Width of the wuser signal. RI5CY, Ibex, CV32E40* do not have the wuser signal.
   parameter RUSER_WIDTH = `UVMA_OBI_MEMORY_RUSER_DEFAULT_WIDTH, ///< Width of the ruser signal. RI5CY, Ibex, CV32E40* do not have the ruser signal.
   parameter ADDR_WIDTH  = `UVMA_OBI_MEMORY_ADDR_DEFAULT_WIDTH , ///< Width of the addr signal.
   parameter DATA_WIDTH  = `UVMA_OBI_MEMORY_DATA_DEFAULT_WIDTH , ///< Width of the rdata and wdata signals. be width is DATA_WIDTH / 8. Valid DATA_WIDTH settings are 32 and 64.
   parameter ID_WIDTH    = `UVMA_OBI_MEMORY_ID_DEFAULT_WIDTH   , ///< Width of the aid and rid signals.
   parameter ACHK_WIDTH  = `UVMA_OBI_MEMORY_ACHK_DEFAULT_WIDTH , ///< Width of the achk signal.
   parameter RCHK_WIDTH  = `UVMA_OBI_MEMORY_RCHK_DEFAULT_WIDTH   ///< Width of the rchk signal.
) extends uvma_obi_memory_base_seq_c#(
   .AUSER_WIDTH(AUSER_WIDTH),
   .WUSER_WIDTH(WUSER_WIDTH),
   .RUSER_WIDTH(RUSER_WIDTH),
   .ADDR_WIDTH(ADDR_WIDTH),
   .DATA_WIDTH(DATA_WIDTH),
   .ID_WIDTH(ID_WIDTH),
   .ACHK_WIDTH(ACHK_WIDTH),
   .RCHK_WIDTH(RCHK_WIDTH)
);

   // Fields


   `uvm_object_param_utils_begin(uvma_obi_memory_slv_base_seq_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   ))

   `uvm_object_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_slv_base_seq");

   /**
    * TODO Describe uvma_obi_memory_slv_base_seq_c::body()
    */
   extern task body();

   /**
    * TODO Describe uvma_obi_memory_slv_base_seq_c::do_response()
    */
   extern virtual task do_response(ref uvma_obi_memory_mon_trn_c mon_req);

   /**
    * Convenience function to encapsulate the add_* reponse functions to generate all non-data response fields
    */
   extern virtual function void add_r_fields(uvma_obi_memory_mon_trn_c mon_req, uvma_obi_memory_slv_seq_item_c slv_rsp);

   /**
    * Standard method to add a random ralid latency
    */
   extern virtual function void add_latencies(uvma_obi_memory_slv_seq_item_c slv_rsp);

   /**
    * Standard method to add a random error response as based on cfg knobs
    */
   extern virtual function void add_err(uvma_obi_memory_slv_seq_item_c slv_rsp);

   /**
    * Standard method to add a random exclusive okay response as based on cfg knobs
    */
   extern virtual function void add_exokay(uvma_obi_memory_mon_trn_c mon_req, uvma_obi_memory_slv_seq_item_c slv_rsp);

   /**
    * Standard method to add a random or custom ruser, default implementation writes 0
    */
   extern virtual function void add_rchk(uvma_obi_memory_slv_seq_item_c slv_rsp);

   /**
    * Standard method to add a random or custom rchk, default implementation writes 0
    */
   extern virtual function void add_ruser(uvma_obi_memory_slv_seq_item_c slv_rsp);

endclass : uvma_obi_memory_slv_base_seq_c


function uvma_obi_memory_slv_base_seq_c::new(string name="uvma_obi_memory_slv_base_seq");

   super.new(name);

endfunction : new


task uvma_obi_memory_slv_base_seq_c::body();

   uvma_obi_memory_mon_trn_c  mon_trn;

   forever begin
      // Wait for the monitor to send us the mstr's "req" with an access request
      p_sequencer.mon_trn_fifo.get(mon_trn);
      `uvm_info("OBI_MEMORY_SLV_SEQ", $sformatf("Got mon_trn:\n%s", mon_trn.sprint()), UVM_HIGH)
      do_response(mon_trn);
   end

endtask : body


task uvma_obi_memory_slv_base_seq_c::do_response(ref uvma_obi_memory_mon_trn_c mon_req);

   `uvm_fatal("OBI_MEMORY_SLV_SEQ", "Call to pure virtual task")

endtask : do_response


function void uvma_obi_memory_slv_base_seq_c::add_latencies(uvma_obi_memory_slv_seq_item_c slv_rsp);

   slv_rsp.rvalid_latency = cfg.calc_random_rvalid_latency();

endfunction : add_latencies


function void uvma_obi_memory_slv_base_seq_c::add_r_fields(uvma_obi_memory_mon_trn_c mon_req, uvma_obi_memory_slv_seq_item_c slv_rsp);

   // This is just a convenience function
   // Take care to leave rchk last as it will likely incorporate a checksum of all other response fields

   slv_rsp.rid = mon_req.aid;
   add_latencies(slv_rsp);
   if (cfg.version >= UVMA_OBI_MEMORY_VERSION_1P2) begin
      add_err(slv_rsp);
      add_exokay(mon_req, slv_rsp);
      add_ruser(slv_rsp);
      add_rchk(slv_rsp);
   end

endfunction : add_r_fields


function void uvma_obi_memory_slv_base_seq_c::add_err(uvma_obi_memory_slv_seq_item_c slv_rsp);

   slv_rsp.err = cfg.calc_random_err(slv_rsp.orig_trn.address);

endfunction : add_err


function void uvma_obi_memory_slv_base_seq_c::add_exokay(uvma_obi_memory_mon_trn_c mon_req, uvma_obi_memory_slv_seq_item_c slv_rsp);

   if (mon_req.atop[5] != 1'b1 || !(mon_req.atop[4:0] inside {5'h2, 5'h3})) begin
      slv_rsp.exokay = 0;
   end else begin
      slv_rsp.exokay = cfg.calc_random_exokay(slv_rsp.orig_trn.address, (mon_req.atop == 6'h23));
   end

   if (slv_rsp.exokay && mon_req.atop == 6'h22) begin //LR.W
      cfg.set_reservation(slv_rsp.orig_trn.address);
   end

   if (mon_req.atop == 6'h23) begin //SC.W
      cfg.invalidate_reservation();
   end

endfunction : add_exokay


function void uvma_obi_memory_slv_base_seq_c::add_ruser(uvma_obi_memory_slv_seq_item_c slv_rsp);

   slv_rsp.ruser = '0;

endfunction : add_ruser


function void uvma_obi_memory_slv_base_seq_c::add_rchk(uvma_obi_memory_slv_seq_item_c slv_rsp);

   if(cfg.chk_scheme == UVMA_OBI_MEMORY_CHK_TIED) begin
      slv_rsp.rchk = '0;
   end
   // Checksum scheme for CV32E40S. If other schemes are required, they need to be added here,
   // in addition to adding the option to enable them
   else if(cfg.chk_scheme == UVMA_OBI_MEMORY_CHK_CV32E40S) begin
      slv_rsp.rchk[0]    = ^slv_rsp.rdata[7:0];
      slv_rsp.rchk[1]    = ^slv_rsp.rdata[15:8];
      slv_rsp.rchk[2]    = ^slv_rsp.rdata[23:16];
      slv_rsp.rchk[3]    = ^slv_rsp.rdata[31:24];
      slv_rsp.rchk[4]    = ^{slv_rsp.err, 1'b0}; // exokay signal is an optional signal that is only included for CPUs supporting the Atomic (A) extension.
   end

endfunction : add_rchk


`endif // __UVMA_OBI_MEMORY_SLV_BASE_SEQ_SV__
