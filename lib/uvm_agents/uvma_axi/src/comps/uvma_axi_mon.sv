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

class uvma_axi_mon_c extends uvm_monitor;

   `uvm_component_utils(uvma_axi_mon_c)

   uvma_axi_cfg_c                                cfg;
   uvma_axi_cntxt_c                              cntxt;

   //Handles to the monitor ports

   uvm_analysis_port #(uvma_axi_base_seq_item_c)       uvma_mon_port;
   uvm_analysis_port#(uvma_axi_base_seq_item_c)        mon2log_port;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.passive                 passive_mp;
   virtual uvma_axi_intf                         vif;

   function new(string name = "uvma_axi_mon_c", uvm_component parent);
      super.new(name, parent);

      this.uvma_mon_port     = new("uvma_mon_port", this);
      this.mon2log_port      = new("mon2log_port", this);

   endfunction

   function void build_phase(uvm_phase phase);

      super.build_phase(phase);

      void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("build_phase", "monitor cntxt class failed")
      end

      passive_mp = cntxt.axi_vi.passive;
      vif        = cntxt.axi_vi;

      void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("CFG", "Configuration handle is null")
      end

   endfunction

   task run_phase(uvm_phase phase);
      super.run_phase(phase);

      fork
         observe_reset();
         run_monitor();
      join_none

   endtask: run_phase

   task observe_reset();

      forever begin

         wait (cntxt.axi_vi.rst_n === 0);
         cntxt.reset_state = UVMA_AXI_RESET_STATE_IN_RESET;
         `uvm_info(get_type_name(), $sformatf("RESET_STATE_IN_RESET"), UVM_LOW)
         wait (cntxt.axi_vi.rst_n === 1);
         cntxt.reset_state = UVMA_AXI_RESET_STATE_POST_RESET;
         `uvm_info(get_type_name(), $sformatf("RESET_STATE_POST_RESET"), UVM_LOW)
      end

   endtask : observe_reset

   task run_monitor();

      uvma_axi_base_seq_item_c                 item;
      uvma_axi_base_seq_item_c                 drv_item;
      uvma_axi_base_seq_item_c                 transaction;

      forever begin

         item        = uvma_axi_base_seq_item_c::type_id::create("item", this);
         drv_item    = uvma_axi_base_seq_item_c::type_id::create("drv_item", this);
         transaction = uvma_axi_base_seq_item_c::type_id::create("transaction", this);

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

         end else begin
            if( cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET) begin
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
            end

         end
         `uvm_info(get_type_name(), $sformatf("write data, monitor DUT response and send data"), UVM_HIGH)
         item.w_strb  = passive_mp.psv_axi_cb.w_strb;
         item.w_data  = passive_mp.psv_axi_cb.w_data;
         item.w_last  = passive_mp.psv_axi_cb.w_last;
         item.w_user  = passive_mp.psv_axi_cb.w_user;
         item.w_valid = passive_mp.psv_axi_cb.w_valid;
         item.w_ready = passive_mp.psv_axi_cb.w_ready;
         if(this.passive_mp.psv_axi_cb.ar_valid) begin
           `uvm_info(get_type_name(), $sformatf("read address, collect AR signals and send item"), UVM_HIGH)
           item.ar_id    = passive_mp.psv_axi_cb.ar_id;
           item.ar_addr  = passive_mp.psv_axi_cb.ar_addr;
           item.ar_len   = passive_mp.psv_axi_cb.ar_len;
           item.ar_size  = passive_mp.psv_axi_cb.ar_size;
           item.ar_burst = passive_mp.psv_axi_cb.ar_burst;
           item.ar_user  = passive_mp.psv_axi_cb.ar_user;
           item.ar_valid = passive_mp.psv_axi_cb.ar_valid;
           item.ar_ready = passive_mp.psv_axi_cb.ar_ready;
           item.ar_lock  = passive_mp.psv_axi_cb.ar_lock;
         end  else begin
            if( cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET) begin
               item.ar_id    = 0;
               item.ar_addr  = 0;
               item.ar_len   = 0;
               item.ar_size  = 0;
               item.ar_burst = 0;
               item.ar_user  = 0;
               item.ar_valid = 0;
               item.ar_ready = 0;
               item.ar_lock  = 0;
            end
         end
         `uvm_info(get_type_name(), $sformatf("read data, collect resp signals from interface"), UVM_HIGH)
         item.r_id    = passive_mp.psv_axi_cb.r_id;
         item.r_data  = passive_mp.psv_axi_cb.r_data;
         item.r_resp  = passive_mp.psv_axi_cb.r_resp;
         item.r_last  = passive_mp.psv_axi_cb.r_last;
         item.r_user  = passive_mp.psv_axi_cb.r_user;
         item.r_valid = passive_mp.psv_axi_cb.r_valid;
         item.r_ready = passive_mp.psv_axi_cb.r_ready;
         `uvm_info(get_type_name(), $sformatf("response, collect resp signals from interface"), UVM_HIGH)

         item.b_id    = passive_mp.psv_axi_cb.b_id;
         item.b_resp  = passive_mp.psv_axi_cb.b_resp;
         item.b_user  = passive_mp.psv_axi_cb.b_user;
         item.b_valid = passive_mp.psv_axi_cb.b_valid;
         item.b_ready = passive_mp.psv_axi_cb.b_ready;
         item.monitoring_mode = passive_mode;

         repeat(9) begin
            this.uvma_mon_port.write(item);
         end
         // collect AW signals
         drv_item.aw_id    = vif.aw_id;
         drv_item.aw_addr  = vif.aw_addr;
         drv_item.aw_len   = vif.aw_len;
         drv_item.aw_size  = vif.aw_size;
         drv_item.aw_burst = vif.aw_burst;
         drv_item.aw_user  = vif.aw_user;
         drv_item.aw_valid = vif.aw_valid;
         drv_item.aw_ready = vif.aw_ready;
         drv_item.aw_lock  = vif.aw_lock;
         drv_item.aw_atop  = vif.aw_atop;
         //Collect W signals
         drv_item.w_strb   = vif.w_strb;
         drv_item.w_data   = vif.w_data;
         drv_item.w_last   = vif.w_last;
         drv_item.w_user   = vif.w_user;
         drv_item.w_valid  = vif.w_valid;
         drv_item.w_ready  = vif.w_ready;
         //Collect AR signals
         drv_item.ar_id    = vif.ar_id;
         drv_item.ar_addr  = vif.ar_addr;
         drv_item.ar_len   = vif.ar_len;
         drv_item.ar_size  = vif.ar_size;
         drv_item.ar_burst = vif.ar_burst;
         drv_item.ar_user  = vif.ar_user;
         drv_item.ar_valid = vif.ar_valid;
         drv_item.ar_ready = vif.ar_ready;
         drv_item.ar_lock  = vif.ar_lock;
         //Collect R signals
         drv_item.r_id    = vif.r_id;
         drv_item.r_data  = vif.r_data;
         drv_item.r_resp  = vif.r_resp;
         drv_item.r_last  = vif.r_last;
         drv_item.r_user  = vif.r_user;
         drv_item.r_valid = vif.r_valid;
         drv_item.r_ready = vif.r_ready;
         //Collect B signals
         drv_item.b_id    = vif.b_id;
         drv_item.b_resp  = vif.b_resp;
         drv_item.b_user  = vif.b_user;
         drv_item.b_valid = vif.b_valid;
         drv_item.b_ready = vif.b_ready;
         drv_item.monitoring_mode = native_mode;

         `uvm_info(get_type_name(), $sformatf("Monitor send aw_req to seq"), UVM_HIGH)

         repeat(9) begin
            this.uvma_mon_port.write(drv_item);
         end

         transaction.aw_id    = passive_mp.psv_axi_cb.aw_id;
         transaction.aw_addr  = passive_mp.psv_axi_cb.aw_addr;
         transaction.aw_valid = passive_mp.psv_axi_cb.aw_valid;
         transaction.aw_ready = passive_mp.psv_axi_cb.aw_ready;
         transaction.aw_lock  = passive_mp.psv_axi_cb.aw_lock;
         transaction.w_valid = passive_mp.psv_axi_cb.w_valid;
         transaction.w_ready = passive_mp.psv_axi_cb.w_ready;
         transaction.w_data  = passive_mp.psv_axi_cb.w_data;
         transaction.w_last  = passive_mp.psv_axi_cb.w_last;
         transaction.ar_id    = passive_mp.psv_axi_cb.ar_id;
         transaction.ar_addr  = passive_mp.psv_axi_cb.ar_addr;
         transaction.ar_valid = passive_mp.psv_axi_cb.ar_valid;
         transaction.ar_ready = passive_mp.psv_axi_cb.ar_ready;
         transaction.ar_lock  = passive_mp.psv_axi_cb.ar_lock;
         transaction.r_id    = passive_mp.psv_axi_cb.r_id;
         transaction.r_data  = passive_mp.psv_axi_cb.r_data;
         transaction.r_valid = passive_mp.psv_axi_cb.r_valid;
         transaction.r_ready = passive_mp.psv_axi_cb.r_ready;
         transaction.r_resp  = passive_mp.psv_axi_cb.r_resp;
         transaction.r_last  = passive_mp.psv_axi_cb.r_last;
         transaction.b_id    = passive_mp.psv_axi_cb.b_id;
         transaction.b_resp  = passive_mp.psv_axi_cb.b_resp;
         transaction.b_valid = passive_mp.psv_axi_cb.b_valid;
         transaction.b_ready = passive_mp.psv_axi_cb.b_ready;

         if( cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET) begin
            this.mon2log_port.write(transaction);
         end

         @(passive_mp.psv_axi_cb);
       end
    endtask: run_monitor


endclass : uvma_axi_mon_c

`endif
