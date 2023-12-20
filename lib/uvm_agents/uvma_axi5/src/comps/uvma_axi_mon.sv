// Copyright 2023 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Omar HOUTI (omar.houti@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group
// Co-Author: Alae Eddine EZ ZEJJARI


`ifndef __UVMA_AXI_MON_SV__
`define __UVMA_AXI_MON_SV__

/**
 * Component sampling transactions from a Open Bus Interface virtual interface
 * (uvma_obi_if).
 */
class uvma_axi_mon_c extends uvm_monitor;

   `uvm_component_utils(uvma_axi_mon_c)

   // Objects
   uvma_axi_cfg_c                                cfg;
   uvma_axi_cntxt_c                              cntxt;

   // TLM
   uvm_analysis_port #(uvma_axi_base_seq_item_c)       uvma_mon_port;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.passive                 passive_mp;

   int aw_status = -1;
   int w_status = -1;
   int ar_status = -1;

   /**
    * Default constructor.
    */
   function new(string name = "uvma_axi_mon_c", uvm_component parent);
      super.new(name, parent);

      this.uvma_mon_port     = new("uvma_mon_port", this);

   endfunction

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   function void build_phase(uvm_phase phase);

      super.build_phase(phase);

      void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("build_phase", "monitor cntxt class failed")
      end

      passive_mp = cntxt.axi_vi.passive;

      void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("CFG", "Configuration handle is null")
      end

   endfunction

   /**
    * TODO Describe uvma_axi_mon_c::run_phase()
    */
   task run_phase(uvm_phase phase);
      super.run_phase(phase);

      fork
         observe_reset();
         begin
            forever begin
               case (cntxt.reset_state)
                  UVMA_AXI_RESET_STATE_PRE_RESET : mon_pre_reset ();
                  UVMA_AXI_RESET_STATE_IN_RESET  : mon_in_reset  ();
                  UVMA_AXI_RESET_STATE_POST_RESET: mon_post_reset();
               endcase
            end
         end
      join_none

   endtask: run_phase

   /**
    * Monitors passive_mp for asynchronous reset and updates the context's reset state.
    */
   task observe_reset();

      forever begin

         wait (cntxt.axi_vi.rst_n === 0);
         cntxt.reset_state = UVMA_AXI_RESET_STATE_IN_RESET;
         `uvm_info(get_type_name(), $sformatf("RESET_STATE_IN_RESET"), UVM_LOW)
         wait (cntxt.axi_vi.rst_n === 1);
         @(passive_mp.psv_axi_cb);
         cntxt.reset_state = UVMA_AXI_RESET_STATE_POST_RESET;
         `uvm_info(get_type_name(), $sformatf("RESET_STATE_POST_RESET"), UVM_LOW)
      end

   endtask : observe_reset

   /**
    * TODO Describe uvma_axi_mon_c::mon_pre_reset()
    */
   task mon_pre_reset();
      @(passive_mp.psv_axi_cb);
   endtask : mon_pre_reset

   /**
    * TODO Describe uvma_axi_mon_c::mon_in_reset()
    */
   task mon_in_reset();
      @(passive_mp.psv_axi_cb);
   endtask : mon_in_reset

   /**
    * TODO Describe uvma_axi_mon_c::mon_post_reset()
    */
   task mon_post_reset();

      uvma_axi_base_seq_item_c                       item;

      item        = uvma_axi_base_seq_item_c::type_id::create("item", this);

      if(passive_mp.psv_axi_cb.aw_valid) begin
         `uvm_info(get_type_name(), $sformatf("write address, collect AW signals and send item"), UVM_HIGH)
         item.aw_id    = passive_mp.psv_axi_cb.aw_id;
         item.aw_addr  = passive_mp.psv_axi_cb.aw_addr;
         item.aw_len   = passive_mp.psv_axi_cb.aw_len;
         item.aw_size  = passive_mp.psv_axi_cb.aw_size;
         item.aw_burst = passive_mp.psv_axi_cb.aw_burst;
         item.aw_valid = passive_mp.psv_axi_cb.aw_valid;
         item.aw_ready = passive_mp.psv_axi_cb.aw_ready;
         item.aw_cache = passive_mp.psv_axi_cb.aw_cache;
         item.aw_user  = passive_mp.psv_axi_cb.aw_user;
         item.aw_lock  = passive_mp.psv_axi_cb.aw_lock;
         item.aw_prot  = passive_mp.psv_axi_cb.aw_prot;
         item.aw_qos   = passive_mp.psv_axi_cb.aw_qos;
         item.aw_region= passive_mp.psv_axi_cb.aw_region;
         item.aw_atop  = passive_mp.psv_axi_cb.aw_atop;
         aw_status++;
         if(item.aw_ready) begin
            `uvm_info(get_type_name(), $sformatf("write address, collect AW signals and send item"), UVM_HIGH)
            item.aw_latency = aw_status;
            item.aw_start_time = $time;
            aw_status = -1;
         end
      end else begin
         item.aw_id    = 0;
         item.aw_addr  = 0;
         item.aw_len   = 0;
         item.aw_size  = 0;
         item.aw_burst = 0;
         item.aw_valid = 0;
         item.aw_ready = 0;
         item.aw_cache = 0;
         item.aw_user  = 0;
         item.aw_lock  = 0;
         item.aw_prot  = 0;
         item.aw_qos   = 0;
         item.aw_region= 0;
         item.aw_atop  = 0;
         item.aw_latency = -1;
      end

      if(passive_mp.psv_axi_cb.w_valid) begin
         item.w_strb  = passive_mp.psv_axi_cb.w_strb;
         item.w_data  = passive_mp.psv_axi_cb.w_data;
         item.w_last  = passive_mp.psv_axi_cb.w_last;
         item.w_user  = passive_mp.psv_axi_cb.w_user;
         item.w_valid = passive_mp.psv_axi_cb.w_valid;
         item.w_ready = passive_mp.psv_axi_cb.w_ready;
         w_status++;
         if(item.w_ready) begin
            item.w_latency = w_status;
            item.w_start_time = $time;
            w_status = -1;
         end
      end else begin
         item.w_strb  = 0;
         item.w_data  = 0;
         item.w_last  = 0;
         item.w_user  = 0;
         item.w_valid = 0;
         item.w_ready = 0;
         item.w_latency = -1;
      end

      item.b_ready = passive_mp.psv_axi_cb.b_ready;

      if(this.passive_mp.psv_axi_cb.ar_valid) begin
         item.ar_id    = passive_mp.psv_axi_cb.ar_id;
         item.ar_addr  = passive_mp.psv_axi_cb.ar_addr;
         item.ar_len   = passive_mp.psv_axi_cb.ar_len;
         item.ar_size  = passive_mp.psv_axi_cb.ar_size;
         item.ar_burst = passive_mp.psv_axi_cb.ar_burst;
         item.ar_user  = passive_mp.psv_axi_cb.ar_user;
         item.ar_valid = passive_mp.psv_axi_cb.ar_valid;
         item.ar_ready = passive_mp.psv_axi_cb.ar_ready;
         item.ar_lock  = passive_mp.psv_axi_cb.ar_lock;
         item.ar_prot  = passive_mp.psv_axi_cb.ar_prot;
         item.ar_qos   = passive_mp.psv_axi_cb.ar_qos;
         item.ar_region= passive_mp.psv_axi_cb.ar_region;
         ar_status++;
         if(item.ar_ready) begin
            item.ar_latency = ar_status;
            item.ar_start_time = $time;
            ar_status = -1;
         end
      end  else begin
         item.ar_id    = 0;
         item.ar_addr  = 0;
         item.ar_len   = 0;
         item.ar_size  = 0;
         item.ar_burst = 0;
         item.ar_user  = 0;
         item.ar_valid = 0;
         item.ar_ready = 0;
         item.ar_lock  = 0;
         item.ar_latency = -1;
      end

      item.r_ready = passive_mp.psv_axi_cb.r_ready;

      this.uvma_mon_port.write(item);

      @(passive_mp.psv_axi_cb);

   endtask: mon_post_reset

endclass : uvma_axi_mon_c

`endif
