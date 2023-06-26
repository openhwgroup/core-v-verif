// Copyright 2023 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Omar HOUTI (omar.houti@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group
// Co-Author: Alae Eddine EZ ZEJJARI

/**** AXI4 slave AW driver  ****/

`ifndef __UVMA_AXI_DRV_SV__
`define __UVMA_AXI_DRV_SV__

class uvma_axi_drv_c extends uvm_driver #(uvma_axi_base_seq_item_c);

   `uvm_component_utils(uvma_axi_drv_c)

   uvma_axi_cfg_c                      cfg;
   uvma_axi_cntxt_c                    cntxt;

   //Handle to the items to be drived
   uvma_axi_base_seq_item_c            item;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.slave        slave_mp;

   extern function new(string name = "uvma_axi_drv_c", uvm_component parent);
   extern virtual  function void build_phase(uvm_phase phase);
   extern virtual  task run_phase(uvm_phase phase);
   extern task     drv_pre_reset();
   extern task     drv_in_reset();
   extern task     drv_post_reset();
   extern task     aw_drv(uvma_axi_base_seq_item_c item);
   extern task     w_drv(uvma_axi_base_seq_item_c item);
   extern task     ar_drv(uvma_axi_base_seq_item_c item);
   extern task     r_drv(uvma_axi_base_seq_item_c item);
   extern task     b_drv(uvma_axi_base_seq_item_c item);

endclass: uvma_axi_drv_c

function uvma_axi_drv_c::new(string name = "uvma_axi_drv_c", uvm_component parent);
   super.new(name, parent);
endfunction

function void uvma_axi_drv_c::build_phase(uvm_phase phase);
   super.build_phase(phase);
   if(!uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt)) begin
      `uvm_fatal("build_phase", "driver reset cntxt class failed")
   end

   this.slave_mp = this.cntxt.axi_vi.slave;
   item  = uvma_axi_base_seq_item_c::type_id::create("item", this);

   void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

endfunction

task uvma_axi_drv_c::run_phase(uvm_phase phase);
   super.run_phase(phase);

   forever begin
      case (cntxt.reset_state)
         UVMA_AXI_RESET_STATE_PRE_RESET  : drv_pre_reset ();
         UVMA_AXI_RESET_STATE_IN_RESET   : drv_in_reset  ();
         UVMA_AXI_RESET_STATE_POST_RESET : drv_post_reset();

         default: `uvm_fatal("AXI_DRV", $sformatf("Invalid reset_state: %0d", cntxt.reset_state))
      endcase
   end
endtask: run_phase

task uvma_axi_drv_c::drv_pre_reset();

   `uvm_info(get_type_name(), $sformatf("start drv_pre_reset"), UVM_HIGH)

   this.slave_mp.slv_axi_cb.aw_ready <= 0;
   this.slave_mp.slv_axi_cb.w_ready  <= 0;
   this.slave_mp.slv_axi_cb.ar_ready <= 0;
   this.slave_mp.slv_axi_cb.r_id     <= 0;
   this.slave_mp.slv_axi_cb.r_resp   <= 0;
   this.slave_mp.slv_axi_cb.r_user   <= 0;
   this.slave_mp.slv_axi_cb.r_valid  <= 0;
   this.slave_mp.slv_axi_cb.r_user   <= 0;
   this.slave_mp.slv_axi_cb.b_id     <= 0;
   this.slave_mp.slv_axi_cb.b_resp   <= 0;
   this.slave_mp.slv_axi_cb.b_user   <= 0;
   this.slave_mp.slv_axi_cb.b_valid  <= 0;
   this.slave_mp.slv_axi_cb.b_user   <= 0;
   @(slave_mp.slv_axi_cb);

endtask: drv_pre_reset

task uvma_axi_drv_c::drv_in_reset();

   `uvm_info(get_type_name(), $sformatf("start drv_in_reset"), UVM_HIGH)

   this.slave_mp.slv_axi_cb.aw_ready <= 0;
   this.slave_mp.slv_axi_cb.w_ready  <= 0;
   this.slave_mp.slv_axi_cb.ar_ready <= 0;
   this.slave_mp.slv_axi_cb.r_id     <= 0;
   this.slave_mp.slv_axi_cb.r_resp   <= 0;
   this.slave_mp.slv_axi_cb.r_user   <= 0;
   this.slave_mp.slv_axi_cb.r_valid  <= 0;
   this.slave_mp.slv_axi_cb.r_user   <= 0;
   this.slave_mp.slv_axi_cb.b_id     <= 0;
   this.slave_mp.slv_axi_cb.b_resp   <= 0;
   this.slave_mp.slv_axi_cb.b_user   <= 0;
   this.slave_mp.slv_axi_cb.b_valid  <= 0;
   this.slave_mp.slv_axi_cb.b_user   <= 0;
   @(slave_mp.slv_axi_cb);

endtask: drv_in_reset

task uvma_axi_drv_c::drv_post_reset();

   `uvm_info(get_type_name(), $sformatf("start drv_post_reset"), UVM_HIGH)
	seq_item_port.get_next_item(item);
    `uvm_info(get_type_name(), $sformatf("start getting sequence"), UVM_HIGH)

   fork
      begin
         if(item.channel == AW_CHANNEL) begin
            aw_drv(item);
            `uvm_info(get_type_name(), $sformatf("start driving aw"), UVM_HIGH)
	     end
	  end
   join_none

   fork
      begin
         if(item.channel == W_CHANNEL) begin
            w_drv(item);
            `uvm_info(get_type_name(), $sformatf("start driving w"), UVM_HIGH)
         end
      end
   join_none

   fork
      begin
         if(item.channel == B_CHANNEL) begin
            b_drv(item);
            `uvm_info(get_type_name(), $sformatf("start driving b"), UVM_HIGH)
         end
      end
   join_none

   fork
      begin
         if(item.channel == AR_CHANNEL) begin
            ar_drv(item);
            `uvm_info(get_type_name(), $sformatf("start driving ar"), UVM_HIGH)
         end
      end
   join_none

   fork
      begin
         if(item.channel == R_CHANNEL) begin
            r_drv(item);
            `uvm_info(get_type_name(), $sformatf("start driving r"), UVM_HIGH)
         end
      end
   join_none

	seq_item_port.item_done();

endtask : drv_post_reset

task uvma_axi_drv_c::aw_drv(uvma_axi_base_seq_item_c item);

   `uvm_info(get_type_name(), $sformatf("write address driver start"), UVM_HIGH)
   this.slave_mp.slv_axi_cb.aw_ready <= 0;
   this.slave_mp.slv_axi_cb.aw_ready <= item.aw_ready;
   @(slave_mp.slv_axi_cb);

endtask

task uvma_axi_drv_c:: w_drv(uvma_axi_base_seq_item_c item);

   `uvm_info(get_type_name(), $sformatf("write w_data driver start"), UVM_HIGH)
   this.slave_mp.slv_axi_cb.w_ready <= item.w_ready;
   @(slave_mp.slv_axi_cb);

endtask

task uvma_axi_drv_c:: ar_drv(uvma_axi_base_seq_item_c item);

   this.slave_mp.slv_axi_cb.ar_ready <= 0;
   this.slave_mp.slv_axi_cb.ar_ready <= item.ar_ready;
   @(slave_mp.slv_axi_cb);
   `uvm_info(get_type_name(), $sformatf("read address, response by ar_ready"), UVM_HIGH)

endtask

task uvma_axi_drv_c:: r_drv(uvma_axi_base_seq_item_c item);

   `uvm_info(get_type_name(),$sformatf("response, send r_data to DUT"), UVM_HIGH)

   this.slave_mp.slv_axi_cb.r_id    <= this.item.r_id;
   this.slave_mp.slv_axi_cb.r_resp  <= this.item.r_resp;
   this.slave_mp.slv_axi_cb.r_user  <= this.item.r_user;
   this.slave_mp.slv_axi_cb.r_last  <= this.item.r_last;
   this.slave_mp.slv_axi_cb.r_valid <= this.item.r_valid;
   this.slave_mp.slv_axi_cb.r_data  <= this.item.r_data;
   @(slave_mp.slv_axi_cb);

endtask

task uvma_axi_drv_c:: b_drv(uvma_axi_base_seq_item_c item);

   `uvm_info(get_type_name(),$sformatf("response, send resp to DUT"), UVM_HIGH)

   this.slave_mp.slv_axi_cb.b_id    <= this.item.b_id;
   this.slave_mp.slv_axi_cb.b_resp  <= this.item.b_resp;
   this.slave_mp.slv_axi_cb.b_user  <= this.item.b_user;
   this.slave_mp.slv_axi_cb.b_user  <= this.item.b_user;
   this.slave_mp.slv_axi_cb.b_valid <= this.item.b_valid;
   @(slave_mp.slv_axi_cb);

endtask

`endif

