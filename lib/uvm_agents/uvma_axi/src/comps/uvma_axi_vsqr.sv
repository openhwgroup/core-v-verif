// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group

/**** AXI4 slave sequencer  ****/

`ifndef __UVMA_AXI_VSQR_SV__
`define __UVMA_AXI_VSQR_SV__

class uvma_axi_vsqr_c extends uvm_sequencer#(uvma_axi_base_seq_item_c);

   `uvm_component_utils(uvma_axi_vsqr_c)

   uvma_axi_cfg_c    cfg;
   uvma_axi_cntxt_c  cntxt;

   //Handles to sequencer FIFOS
   uvm_tlm_analysis_fifo#(uvma_axi_base_seq_item_c,10)    mon2seq_fifo;

   //Handles to sequencer port connected to the FIFOS
   uvm_get_port#(uvma_axi_base_seq_item_c)                mon2seq_export;

   function new(string name = "uvma_axi_sqr_c", uvm_component parent = null);

      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("CFG", "Configuration handle is null")
      end
      
      void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("CNTXT", "Context handle is null")
      end
      this.mon2seq_export      = new("mon2seq_export", this);
      this.mon2seq_fifo        = new("mon2seq_fifo", this);

   endfunction

   function void connect_phase(uvm_phase phase);

      super.connect_phase(phase);
      // Connect get ports to FIFO get peek_export ports

      this.mon2seq_export.connect(mon2seq_fifo.get_peek_export);

   endfunction

endclass

`endif
