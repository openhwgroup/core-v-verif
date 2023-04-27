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


`ifndef __UVMA_OBI_MEMORY_AGENT_SV__
`define __UVMA_OBI_MEMORY_AGENT_SV__


/**
 * Top-level component that encapsulates, builds and connects all others.
 * Capable of driving/monitoring Open Bus Interface interface.
 */
class uvma_obi_memory_agent_c#(
   parameter AUSER_WIDTH = `UVMA_OBI_MEMORY_AUSER_DEFAULT_WIDTH, ///< Width of the auser signal. RI5CY, Ibex, CV32E40* do not have the auser signal.
   parameter WUSER_WIDTH = `UVMA_OBI_MEMORY_WUSER_DEFAULT_WIDTH, ///< Width of the wuser signal. RI5CY, Ibex, CV32E40* do not have the wuser signal.
   parameter RUSER_WIDTH = `UVMA_OBI_MEMORY_RUSER_DEFAULT_WIDTH, ///< Width of the ruser signal. RI5CY, Ibex, CV32E40* do not have the ruser signal.
   parameter ADDR_WIDTH  = `UVMA_OBI_MEMORY_ADDR_DEFAULT_WIDTH , ///< Width of the addr signal.
   parameter DATA_WIDTH  = `UVMA_OBI_MEMORY_DATA_DEFAULT_WIDTH , ///< Width of the rdata and wdata signals. be width is DATA_WIDTH / 8. Valid DATA_WIDTH settings are 32 and 64.
   parameter ID_WIDTH    = `UVMA_OBI_MEMORY_ID_DEFAULT_WIDTH   , ///< Width of the aid and rid signals.
   parameter ACHK_WIDTH  = `UVMA_OBI_MEMORY_ACHK_DEFAULT_WIDTH , ///< Width of the achk signal.
   parameter RCHK_WIDTH  = `UVMA_OBI_MEMORY_RCHK_DEFAULT_WIDTH   ///< Width of the rchk signal.
) extends uvm_agent;

   // Objects
   uvma_obi_memory_cfg_c    cfg;
   uvma_obi_memory_cntxt_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   ) cntxt;

   // Components
   uvma_obi_memory_drv_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   ) driver;

   uvma_obi_memory_mon_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   ) monitor;

   uvma_obi_memory_sqr_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   ) sequencer;

   uvma_obi_memory_cov_model_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   ) cov_model;

   uvma_obi_memory_seq_item_logger_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   ) seq_item_logger;

   uvma_obi_memory_mon_trn_logger_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   ) mon_trn_logger;

   // TLM
   uvm_analysis_port#(uvma_obi_memory_mstr_seq_item_c)  drv_mstr_ap;
   uvm_analysis_port#(uvma_obi_memory_slv_seq_item_c )  drv_slv_ap ;
   uvm_analysis_port#(uvma_obi_memory_mon_trn_c      )  mon_ap     ;


   `uvm_component_utils_begin(uvma_obi_memory_agent_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   ))
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_agent", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null
    * 2. Builds all components
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * 1. Links agent's analysis ports to sub-components'
    * 2. Connects coverage models and loggers
    */
   extern virtual function void connect_phase(uvm_phase phase);

   /**
    * Uses uvm_config_db to retrieve cfg and hand out to sub-components.
    */
   extern function void get_and_set_cfg();

   /**
    * Uses uvm_config_db to retrieve cntxt and hand out to sub-components.
    */
   extern function void get_and_set_cntxt();

   /**
    * Uses uvm_config_db to retrieve the Virtual Interface (vif) associated with this
    * agent.
    */
   extern function void retrieve_vif();

   /**
    * Creates sub-components.
    */
   extern function void create_components();

   /**
    * Connects sequencer and driver's TLM port(s).
    */
   extern function void connect_sequencer_and_driver();

   /**
    * Connects monitor and driver's TLM port(s).
    */
   extern function void connect_rsp_path();

   /**
    * Connects agent's TLM ports to driver's and monitor's.
    */
   extern function void connect_analysis_ports();

   /**
    * Connects coverage model to monitor and driver's analysis ports.
    */
   extern function void connect_cov_model();

   /**
    * Connects transaction loggers to monitor and driver's analysis ports.
    */
   extern function void connect_trn_loggers();

endclass : uvma_obi_memory_agent_c


function uvma_obi_memory_agent_c::new(string name="uvma_obi_memory_agent", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_obi_memory_agent_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   get_and_set_cfg  ();
   get_and_set_cntxt();
   retrieve_vif     ();
   create_components();

endfunction : build_phase


function void uvma_obi_memory_agent_c::connect_phase(uvm_phase phase);

   super.connect_phase(phase);

   connect_analysis_ports      ();
   connect_sequencer_and_driver();
   connect_rsp_path            ();

   if (cfg.cov_model_enabled) begin
      connect_cov_model();
   end
   if (cfg.trn_log_enabled) begin
      connect_trn_loggers();
   end

endfunction: connect_phase


function void uvma_obi_memory_agent_c::get_and_set_cfg();

   void'(uvm_config_db#(uvma_obi_memory_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   else begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
      uvm_config_db#(uvma_obi_memory_cfg_c)::set(this, "*", "cfg", cfg);
   end

endfunction : get_and_set_cfg


function void uvma_obi_memory_agent_c::get_and_set_cntxt();

   void'(uvm_config_db#(uvma_obi_memory_cntxt_c#(
        .AUSER_WIDTH(AUSER_WIDTH),
        .WUSER_WIDTH(WUSER_WIDTH),
        .RUSER_WIDTH(RUSER_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .ACHK_WIDTH(ACHK_WIDTH),
        .RCHK_WIDTH(RCHK_WIDTH)
   ))::get(this, "", "cntxt", cntxt));

   if (cntxt == null) begin
      `uvm_info("CNTXT", "Context handle is null; creating.", UVM_DEBUG)
      cntxt = uvma_obi_memory_cntxt_c#(
        .AUSER_WIDTH(AUSER_WIDTH),
        .WUSER_WIDTH(WUSER_WIDTH),
        .RUSER_WIDTH(RUSER_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .ACHK_WIDTH(ACHK_WIDTH),
        .RCHK_WIDTH(RCHK_WIDTH)
      )::type_id::create("cntxt");
   end
   uvm_config_db#(uvma_obi_memory_cntxt_c#(
        .AUSER_WIDTH(AUSER_WIDTH),
        .WUSER_WIDTH(WUSER_WIDTH),
        .RUSER_WIDTH(RUSER_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .ACHK_WIDTH(ACHK_WIDTH),
        .RCHK_WIDTH(RCHK_WIDTH)
   ))::set(this, "*", "cntxt", cntxt);

endfunction : get_and_set_cntxt


function void uvma_obi_memory_agent_c::retrieve_vif();
   if (!uvm_config_db#(virtual uvma_obi_memory_if_t#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH))
   )::get(this, "", "vif", cntxt.vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", $typename(cntxt.vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", $typename(cntxt.vif)), UVM_DEBUG)
   end

endfunction : retrieve_vif


function void uvma_obi_memory_agent_c::create_components();

   monitor         = uvma_obi_memory_mon_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   )::type_id::create("monitor"        , this);
   cov_model       = uvma_obi_memory_cov_model_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   )::type_id::create("cov_model"      , this);
   mon_trn_logger  = uvma_obi_memory_mon_trn_logger_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   )::type_id::create("mon_trn_logger" , this);
   seq_item_logger = uvma_obi_memory_seq_item_logger_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   )::type_id::create("seq_item_logger", this);

   if (cfg.is_active) begin
      sequencer = uvma_obi_memory_sqr_c#(
        .AUSER_WIDTH(AUSER_WIDTH),
        .WUSER_WIDTH(WUSER_WIDTH),
        .RUSER_WIDTH(RUSER_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .ACHK_WIDTH(ACHK_WIDTH),
        .RCHK_WIDTH(RCHK_WIDTH)
      )::type_id::create("sequencer", this);
      driver    = uvma_obi_memory_drv_c#(
        .AUSER_WIDTH(AUSER_WIDTH),
        .WUSER_WIDTH(WUSER_WIDTH),
        .RUSER_WIDTH(RUSER_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .ACHK_WIDTH(ACHK_WIDTH),
        .RCHK_WIDTH(RCHK_WIDTH)
      )::type_id::create("driver"   , this);
   end

endfunction : create_components


function void uvma_obi_memory_agent_c::connect_analysis_ports();

   if (cfg.is_active) begin
      drv_mstr_ap = driver .mstr_ap;
      drv_slv_ap  = driver .slv_ap ;
   end
   mon_ap = monitor.ap;

endfunction : connect_analysis_ports


function void uvma_obi_memory_agent_c::connect_sequencer_and_driver();

   if (cfg.is_active) begin
      sequencer.set_arbitration(cfg.sqr_arb_mode);
      driver.seq_item_port.connect(sequencer.seq_item_export);
   end

endfunction : connect_sequencer_and_driver


function void uvma_obi_memory_agent_c::connect_rsp_path();

   if (cfg.is_active) begin
      // FIXME:This conenction is a memory leak (driver never drains FIFO)
      //monitor.ap          .connect(driver   .mon_trn_fifo.analysis_export);
      monitor.sequencer_ap.connect(sequencer.mon_trn_fifo.analysis_export);
   end

endfunction : connect_rsp_path


function void uvma_obi_memory_agent_c::connect_cov_model();

   if (cfg.is_active) begin
      drv_mstr_ap.connect(cov_model.mstr_seq_item_fifo.analysis_export);
      drv_slv_ap .connect(cov_model.slv_seq_item_fifo .analysis_export);
   end
   mon_ap.connect(cov_model.mon_trn_fifo.analysis_export);

endfunction : connect_cov_model


function void uvma_obi_memory_agent_c::connect_trn_loggers();

   //if (cfg.is_active) begin
   //   drv_mstr_ap.connect(seq_item_logger.analysis_export);
   //   drv_slv_ap .connect(seq_item_logger.analysis_export);
   //end
   mon_ap.connect(mon_trn_logger.analysis_export);

endfunction : connect_trn_loggers


`endif // __UVMA_OBI_MEMORY_AGENT_SV__
