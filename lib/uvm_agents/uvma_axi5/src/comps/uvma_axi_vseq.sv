// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVMA_AXI_VSEQ_SV__
`define __UVMA_AXI_VSEQ_SV__

/**
 * Object starting AXI sequences in the appropriate sequencer.
 */
class uvma_axi_vseq_c extends uvm_sequence;

   // Objects handles
   uvma_axi_cfg_c    cfg;
   uvma_axi_cntxt_c  cntxt;

   `uvm_object_utils(uvma_axi_vseq_c)
   `uvm_declare_p_sequencer(uvma_axi_vsqr_c)


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_axi_vseq");

   /**
    * Retrieve cfg and cntxt handles from p_sequencer.
    */
   extern virtual task pre_start();
   
   /**
    * Start sequences
    */
   extern virtual task body();

endclass : uvma_axi_vseq_c


function uvma_axi_vseq_c::new(string name="uvma_axi_vseq");

   super.new(name);

endfunction : new


task uvma_axi_vseq_c::pre_start();

   cfg   = p_sequencer.cfg  ;
   cntxt = p_sequencer.cntxt;

endtask : pre_start

task uvma_axi_vseq_c::body();

   uvma_axi_fw_preload_seq_c   axi_preload_seq;
   axi_preload_seq = uvma_axi_fw_preload_seq_c::type_id::create("axi_preload_seq");
   //Start preload sequence to instantiate the memory class
   axi_preload_seq.start(p_sequencer);
   fork
      begin
         if(cfg.is_active == UVM_ACTIVE) begin

            uvma_axi_slv_seq_c  axi_seq;
            axi_seq = uvma_axi_slv_seq_c::type_id::create("axi_seq");
            void'(axi_seq.randomize());
            //Start axi_seq to generate response to be be driven by driver
            axi_seq.start(p_sequencer);

         end
      end
   join_none

endtask : body

`endif // __uvma_axi_vseq_SV__
