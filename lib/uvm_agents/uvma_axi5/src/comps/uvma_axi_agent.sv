// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group

/**
 * Top-level component that encapsulates, builds and connects all others component.
 * Capable of driving/monitoring AXI interface.
 */
`ifndef __UVMA_AXI_AGENT_SV__
`define __UVMA_AXI_AGENT_SV__

class uvma_axi_agent_c extends uvm_agent;

   `uvm_component_utils(uvma_axi_agent_c)

   uvma_axi_mon_c             monitor;
   uvma_axi_drv_c             driver;
   uvma_axi_vsqr_c            vsequencer;
   uvma_axi_seq_item_logger_c seq_item_logger;
   uvma_axi_covg_c            axi_covg;

   // Objects handles
   uvma_axi_cfg_c      cfg;
   uvma_axi_cntxt_c    cntxt;

   /**
   * Default constructor.
   */
   function new(string name = "uvma_axi_agent_c", uvm_component parent = null);
      super.new(name, parent);
   endfunction

   /**
    * 1. Ensures cfg & cntxt handles are not null
    * 2. retrieve vif
    * 3. Builds all components
    */
   function void build_phase(uvm_phase phase);

      super.build_phase(phase);
      get_and_set_cfg  ();
      get_and_set_cntxt();
      retrieve_vif     ();
      create_components();

   endfunction : build_phase

   /**
    * Uses uvm_config_db to retrieve cntxt and hand out to sub-components.
    */
   function void get_and_set_cntxt();

      void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_info("CNTXT", "Context handle is null; creating", UVM_DEBUG)
         cntxt = uvma_axi_cntxt_c::type_id::create("cntxt");
         cntxt.mem.mem_default = MEM_DEFAULT_RANDOM;
      end
      uvm_config_db#(uvma_axi_cntxt_c)::set(this, "*", "cntxt", cntxt);

   endfunction : get_and_set_cntxt

   /**
    * Uses uvm_config_db to retrieve cfg and hand out to sub-components.
    */
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

   /**
    * Uses uvm_config_db to retrieve the Virtual Interface (vif) associated with this agent.
    */
   function void retrieve_vif();

      if(cfg.is_slave) begin
        if (!uvm_config_db#(virtual uvma_axi_intf)::get(this, "", "axi_vif", cntxt.axi_vi)) begin
           `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", $typename(cntxt.axi_vi)))
        end
        else begin
           `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", $typename(cntxt.axi_vi)), UVM_DEBUG)
        end
      end

      if(!cfg.is_slave) begin
        if (!uvm_config_db#(virtual uvma_axi_mst_intf)::get(this, "", "axi_mst_vif", cntxt.axi_mst_vi)) begin
           `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", $typename(cntxt.axi_vi)))
        end
        else begin
           `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", $typename(cntxt.axi_vi)), UVM_DEBUG)
        end
      end
   endfunction : retrieve_vif

   /**
    * Creates sub-components.
    */
   function void create_components();

      this.monitor = uvma_axi_mon_c :: type_id :: create("monitor", this);
      this.seq_item_logger = uvma_axi_seq_item_logger_c::type_id::create("seq_item_logger", this);
      if( cfg.is_active == UVM_ACTIVE) begin
         this.vsequencer = uvma_axi_vsqr_c::type_id::create("vsequencer", this);
         this.driver  = uvma_axi_drv_c  :: type_id :: create("driver",  this);
      end

      if(cfg.cov_model_enabled) begin
         this.axi_covg = uvma_axi_covg_c::type_id::create("axi_covg", this);
      end

   endfunction : create_components

   /**
    * 1. Links agent's analysis ports to sub-components'
    * 2. Connects coverage models and loggers
    */
   function void connect_phase(uvm_phase phase);

      super.connect_phase(phase);

      if( cfg.is_active == UVM_ACTIVE) begin

         //Establishing connections between driver and sequencer
         this.driver.seq_item_port.connect(vsequencer.seq_item_export);
         this.driver.rsp_port.connect(vsequencer.rsp_export);


         //Establishing connections between monitor ports and sequencer
         this.monitor.m_uvma_axi_read_req_packets_collected.connect(vsequencer.ar_mon2seq_export);
         this.monitor.m_uvma_axi_write_add_req_packets_collected.connect(vsequencer.aw_mon2seq_export);
         this.monitor.m_uvma_axi_write_data_req_packets_collected.connect(vsequencer.w_mon2seq_export);
         this.monitor.m_uvma_axi_req_packets_collected.connect(vsequencer.mon2seq_export);
         this.vsequencer.set_agent_config(cfg);
         `uvm_info(get_type_name(), $sformatf("ACTIVE MODE"), UVM_LOW)

      end else begin
         `uvm_info(get_type_name(), $sformatf("PASSIVE MODE"), UVM_LOW)
      end
      if (cfg.trn_log_enabled) begin

         //Establishing connections between synchronizer ports and logger
         this.monitor.m_uvma_axi_read_req_packets_collected.connect(seq_item_logger.analysis_export);
         this.monitor.m_uvma_axi_write_req_packets_collected.connect(seq_item_logger.analysis_export);
         this.monitor.m_uvma_axi_read_rsp_packets_collected.connect(seq_item_logger.analysis_export);
         this.monitor.m_uvma_axi_write_rsp_packets_collected.connect(seq_item_logger.analysis_export);

         `uvm_info(get_type_name(), $sformatf("Transaction Loger enable"), UVM_LOW)

      end

      if(cfg.cov_model_enabled) begin
         monitor.m_uvma_axi_write_rsp_packets_collected.connect(axi_covg.uvma_axi_cov_b_resp_fifo.analysis_export);
         monitor.m_uvma_axi_read_rsp_packets_collected .connect(axi_covg.uvma_axi_cov_r_resp_fifo.analysis_export);
         monitor.m_uvma_axi_read_req_packets_collected .connect(axi_covg.uvma_axi_cov_ar_req_fifo.analysis_export);
         monitor.m_uvma_axi_write_req_packets_collected.connect(axi_covg.uvma_axi_cov_aw_req_fifo.analysis_export);
      end

   endfunction

endclass : uvma_axi_agent_c

`endif //__UVMA_AXI_AGENT_SV__
