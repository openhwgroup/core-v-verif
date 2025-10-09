// Copyright 2023 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVMA_AXI_BASE_SEQ_SV__
`define __UVMA_AXI_BASE_SEQ_SV__


/**
 * Abstract object from which all other AXI agent
 * sequences must extend. Subclasses must be run on AXI
 * sequencer (uvma_axi_vsqr_c) instance.
 */
class uvma_axi_base_seq_c extends uvm_sequence#(uvma_axi_transaction_c);

   // Agent handles
   uvma_axi_cfg_c    cfg;
   uvma_axi_cntxt_c  cntxt;

   `uvm_object_utils(uvma_axi_base_seq_c)
   `uvm_declare_p_sequencer(uvma_axi_vsqr_c)


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_axi_base_seq");

   /**
    * Assigns cfg and cntxt handles from p_sequencer.
    */
   extern virtual task pre_start();
 //  extern virtual task pre_body();

endclass : uvma_axi_base_seq_c

function uvma_axi_base_seq_c::new(string name="uvma_axi_base_seq");

   super.new(name);

endfunction : new


task uvma_axi_base_seq_c::pre_start();

   if(p_sequencer == null) begin
         `uvm_fatal("SQR", "SQR handle is null")     
   end

   cfg   = p_sequencer.cfg;
   cntxt = p_sequencer.cntxt;

endtask : pre_start

`endif // __UVMA_AXI_BASE_SEQ_SV__
