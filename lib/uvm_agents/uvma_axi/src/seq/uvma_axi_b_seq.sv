// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi


//=============================================================================
// Description: Sequence for agent axi_b
//=============================================================================

`ifndef UVMA_AXI_B_SEQ_SV
`define UVMA_AXI_B_SEQ_SV

class uvma_axi_b_seq_c extends uvm_sequence #(uvma_axi_b_item_c);

   `uvm_object_utils(uvma_axi_b_seq_c)
   `uvm_declare_p_sequencer(uvma_axi_b_sqr_c)

   uvma_axi_b_item_c  resp_item;

   extern function new(string name = "");
   extern task body();

endclass : uvma_axi_b_seq_c

function uvma_axi_b_seq_c::new(string name = "");
   super.new(name);
endfunction : new

task uvma_axi_b_seq_c::body();
   forever begin
      `uvm_info(get_type_name(), "Default sequence starting", UVM_HIGH)
      resp_item = uvma_axi_b_item_c::type_id::create("resp_item");
      p_sequencer.b_resp_fifo.get(resp_item);
      start_item(resp_item);
      `uvm_info(get_type_name(), "resp item", UVM_HIGH)
      finish_item(resp_item);
   end
   `uvm_info(get_type_name(), "Default sequence completed", UVM_HIGH)
endtask : body

`endif
