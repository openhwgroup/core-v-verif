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
   uvm_tlm_analysis_fifo#(uvma_axi_aw_item_c,2)    aw_req_fifo;
   uvm_tlm_analysis_fifo#(uvma_axi_aw_item_c,2)    aw_drv_req_fifo;
   uvm_tlm_analysis_fifo#(uvma_axi_w_item_c,1)     w_req_fifo;
   uvm_tlm_analysis_fifo#(uvma_axi_w_item_c,1)     w_drv_req_fifo;
   uvm_tlm_analysis_fifo#(uvma_axi_ar_item_c,1)    ar_req_fifo;
   uvm_tlm_analysis_fifo#(uvma_axi_ar_item_c,1)    ar_drv_req_fifo;
   uvm_tlm_analysis_fifo#(uvma_axi_r_item_c,1)     r_resp_fifo;
   uvm_tlm_analysis_fifo#(uvma_axi_b_item_c,1)     b_drv_resp_fifo;

   //Handles to sequencer port connected to the FIFOS
   uvm_get_port#(uvma_axi_aw_item_c)               aw_req_export;
   uvm_get_port#(uvma_axi_aw_item_c)               aw_drv_req_export;
   uvm_get_port#(uvma_axi_w_item_c)                w_req_export;
   uvm_get_port#(uvma_axi_w_item_c)                w_drv_req_export;
   uvm_get_port#(uvma_axi_ar_item_c)               ar_req_export;
   uvm_get_port#(uvma_axi_ar_item_c)               ar_drv_req_export;
   uvm_get_port#(uvma_axi_r_item_c)                r_resp_export;
   uvm_get_port#(uvma_axi_b_item_c)                b_drv_resp_export;

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
      this.ar_req_export      = new("ar_req_export", this);
      this.ar_req_fifo        = new("ar_req_fifo", this);
      this.ar_drv_req_fifo    = new("ar_drv_req_fifo", this);
      this.ar_drv_req_export  = new("ar_drv_req_export", this);

      this.aw_req_export      = new("aw_req_export", this);
      this.aw_drv_req_export  = new("aw_drv_req_export", this);
      this.aw_req_fifo        = new("aw_req_fifo", this);
      this.aw_drv_req_fifo    = new("aw_drv_req_fifo", this);

      this.w_req_export       = new("w_req_export", this);
      this.w_req_fifo         = new("w_req_fifo", this);
      this.w_drv_req_fifo     = new("w_drv_req_fifo", this);
      this.w_drv_req_export   = new("w_drv_req_export", this);

      this.b_drv_resp_export  = new("b_drv_resp_export", this);
      this.b_drv_resp_fifo    = new("b_drv_resp_fifo", this);

      this.r_resp_export      = new("r_resp_export", this);
      this.r_resp_fifo        = new("r_resp_fifo", this);

   endfunction

   function void connect_phase(uvm_phase phase);

      super.connect_phase(phase);

      // Connect get ports to FIFO get peek_export ports

      this.aw_req_export.connect(aw_req_fifo.get_peek_export);

      this.aw_drv_req_export.connect(aw_drv_req_fifo.get_peek_export);

      this.w_req_export.connect(w_req_fifo.get_peek_export);

      this.w_drv_req_export.connect(w_drv_req_fifo.get_peek_export);

      this.ar_req_export.connect(ar_req_fifo.get_peek_export);

      this.ar_drv_req_export.connect(ar_drv_req_fifo.get_peek_export);

      this.r_resp_export.connect(r_resp_fifo.get_peek_export);

      this.b_drv_resp_export.connect(b_drv_resp_fifo.get_peek_export);

   endfunction

endclass

`endif
