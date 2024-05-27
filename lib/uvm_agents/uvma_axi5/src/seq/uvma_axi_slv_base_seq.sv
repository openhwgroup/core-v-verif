// Copyright 2023 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVMA_AXI_SLV_BASE_SEQ_SV__
`define __UVMA_AXI_SLV_BASE_SEQ_SV__


/**
 * TODO Describe uvma_axi_slv_base_seq_c
 */
class uvma_axi_slv_base_seq_c extends uvma_axi_base_seq_c;

   uvma_axi_synchronizer_c  synchronizer;


   `uvm_object_utils_begin(uvma_axi_slv_base_seq_c)
   `uvm_object_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_axi_slv_base_seq");

   /**
    * Assigns synchronizer handles from p_sequencer.
    */
   extern virtual task pre_body();

   /**
    * TODO Describe uvma_axi_slv_base_seq_c::body()
    */
   extern task body();

   /**
    * TODO Describe uvma_axi_slv_base_seq_c::do_response()
    */
   extern virtual task do_response(ref uvma_axi_base_seq_item_c mon_req);

   /**
    * Convenience function to encapsulate the axi request in the synchronizer
    */
   extern virtual function void trs_registration(ref uvma_axi_base_seq_item_c mon_req);

endclass : uvma_axi_slv_base_seq_c


function uvma_axi_slv_base_seq_c::new(string name="uvma_axi_slv_base_seq");

   super.new(name);

endfunction : new

task uvma_axi_slv_base_seq_c::pre_body();

   synchronizer   = p_sequencer.synchronizer;

endtask : pre_body

task uvma_axi_slv_base_seq_c::body();

   uvma_axi_base_seq_item_c   mon_trn;
   mon_trn = uvma_axi_base_seq_item_c::type_id::create("mon_trn");

   forever begin
      // Wait for the monitor to send us the mstr's "req" with an access request
      p_sequencer.mon2seq_export.get(mon_trn);
      do_response(mon_trn);
   end

endtask : body

task uvma_axi_slv_base_seq_c::do_response(ref uvma_axi_base_seq_item_c mon_req);

   `uvm_fatal("AXI_SLV_SEQ", "Call to pure virtual task")

endtask : do_response

function void uvma_axi_slv_base_seq_c::trs_registration(ref uvma_axi_base_seq_item_c mon_req);

   if((mon_req.aw_valid && mon_req.aw_ready) || (mon_req.w_valid && mon_req.w_ready)) begin
      synchronizer.add_w_trs(mon_req);
   end

   if(mon_req.ar_valid && mon_req.ar_ready) begin
      synchronizer.add_r_trs(mon_req);
   end

endfunction : trs_registration

`endif // __UVMA_AXI_SLV_BASE_SEQ_SV__
