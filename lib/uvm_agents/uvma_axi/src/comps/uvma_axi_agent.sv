// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group

/**** AXI4 (top) agent ****/

`ifndef __UVMA_AXI_AGENT_SV__
`define __UVMA_AXI_AGENT_SV__

class uvma_axi_agent_c extends uvm_agent;

   `uvm_component_utils(uvma_axi_agent_c)

   uvma_axi_mon_c             monitor;
   uvma_axi_drv_c             driver;
   uvma_axi_vsqr_c            vsequencer;


   uvma_axi_seq_item_logger_c seq_item_logger;

   uvma_axi_cfg_c      cfg;
   uvma_axi_cntxt_c    cntxt;

   function new(string name = "uvma_axi_agent_c", uvm_component parent = null);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);

      super.build_phase(phase);
      get_and_set_cfg  ();
      get_and_set_cntxt();
      retrieve_vif     ();
      create_components();

   endfunction : build_phase

   function void get_and_set_cntxt();

      void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_info("CNTXT", "Context handle is null; creating", UVM_DEBUG)
         cntxt = uvma_axi_cntxt_c::type_id::create("cntxt");
      end
      uvm_config_db#(uvma_axi_cntxt_c)::set(this, "*", "cntxt", cntxt);

   endfunction : get_and_set_cntxt

   function void get_and_set_cfg();

      void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("CFG", "Configuration handle is null")
      end
      else begin
         `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
         uvm_config_db#(uvma_axi_cfg_c)::set(this, "*", "cfg", cfg);
      end

   endfunction : get_and_set_cfg

   function void retrieve_vif();

      if (!uvm_config_db#(virtual uvma_axi_intf)::get(this, "", "axi_vif", cntxt.axi_vi)) begin
         `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", $typename(cntxt.axi_vi)))
      end
      else begin
         `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", $typename(cntxt.axi_vi)), UVM_DEBUG)
      end

   endfunction : retrieve_vif

   function void create_components();

      this.monitor = uvma_axi_mon_c :: type_id :: create("monitor", this);
      this.seq_item_logger = uvma_axi_seq_item_logger_c::type_id::create("seq_item_logger", this);
      if( cfg.is_active == UVM_ACTIVE) begin
         this.vsequencer = uvma_axi_vsqr_c::type_id::create("vsequencer", this);
         this.driver  = uvma_axi_drv_c  :: type_id :: create("driver",  this);
      end

   endfunction : create_components

   function void connect_phase(uvm_phase phase);

      super.connect_phase(phase);

      if( cfg.is_active == UVM_ACTIVE) begin

         //Establishing connections between driver and sequencer

         this.driver.seq_item_port.connect(vsequencer.seq_item_export);

         //Establishing connections between monitor ports and sequencer FIFOS

         this.monitor.uvma_mon_port.connect(vsequencer.mon2seq_fifo.analysis_export);

      end else begin
         `uvm_info(get_type_name(), $sformatf("PASSIVE MODE"), UVM_LOW)
      end
      if (cfg.trn_log_enabled) begin

         //Establishing connections between monitor ports and logger

         this.monitor.mon2log_port.connect(seq_item_logger.analysis_export);

         `uvm_info(get_type_name(), $sformatf("Transaction Loger enable"), UVM_LOW)

      end

   endfunction



endclass : uvma_axi_agent_c

`endif //__UVMA_AXI_AGENT_SV__
