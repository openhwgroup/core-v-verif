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

/**
 * Component driving a AXI virtual interface (uvma_axi_intf).
 */
class uvma_axi_drv_c extends uvm_driver #(uvma_axi_slv_seq_item_c);

   `uvm_component_utils(uvma_axi_drv_c)

   // Objects
   uvma_axi_cfg_c                      cfg;
   uvma_axi_cntxt_c                    cntxt;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.slave        slave_mp;

   int aw_latency_status = 0;
   int w_latency_status = 0;
   int ar_latency_status = 0;

   /**
    * Default constructor.
    */
   extern function new(string name = "uvma_axi_drv_c", uvm_component parent);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual  function void build_phase(uvm_phase phase);

   /**
    * Oversees driving, depending on the reset state, by calling drv_<pre|in|post>_reset() tasks.
    */
   extern virtual  task run_phase(uvm_phase phase);

   /**
    * Called by run_phase() while agent is in pre-reset state.
    */
   extern task     drv_pre_reset();

   /**
    * Called by run_phase() while agent is in reset state.
    */
   extern task     drv_in_reset();

   /**
    * Called by run_phase() while agent is in post-reset state.
    */
   extern task     drv_post_reset();

   /**
    * Drives the AW channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     aw_drv(uvma_axi_slv_seq_item_c item);

   /**
    * Drives the W channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     w_drv(uvma_axi_slv_seq_item_c item);

   /**
    * Drives the B channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     ar_drv(uvma_axi_slv_seq_item_c item);

   /**
    * Drives the AR channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     r_drv(uvma_axi_slv_seq_item_c item);

   /**
    * Drives the R channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     b_drv(uvma_axi_slv_seq_item_c item);

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
   aw_latency_status = 0;
   w_latency_status  = 0;
   ar_latency_status = 0;
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
   aw_latency_status = 0;
   w_latency_status  = 0;
   ar_latency_status = 0;
   @(slave_mp.slv_axi_cb);

endtask: drv_in_reset

task uvma_axi_drv_c::drv_post_reset();

   `uvm_info(get_type_name(), $sformatf("start drv_post_reset"), UVM_HIGH)
	      seq_item_port.get_next_item(req);
    `uvm_info(get_type_name(), $sformatf("start getting sequence"), UVM_HIGH)

       fork
          begin
             if(aw_latency_status == 0) begin
                `uvm_info(get_type_name(), $sformatf("start driving aw"), UVM_HIGH)
                aw_drv(req);
             end
	      end
       join_none

       fork
          begin
             if(w_latency_status == 0) begin
                `uvm_info(get_type_name(), $sformatf("start driving w"), UVM_HIGH)
                w_drv(req);
             end
          end
       join_none

       fork
          begin
             `uvm_info(get_type_name(), $sformatf("start driving b"), UVM_HIGH)
             b_drv(req);
          end
       join_none

       fork
          begin
             if(ar_latency_status == 0) begin
                `uvm_info(get_type_name(), $sformatf("start driving ar"), UVM_HIGH)
                ar_drv(req);
             end
          end
       join_none

       fork
          begin
             `uvm_info(get_type_name(), $sformatf("start driving r"), UVM_HIGH)
             r_drv(req);
          end
       join_none

	seq_item_port.item_done();

endtask : drv_post_reset

task uvma_axi_drv_c::aw_drv(uvma_axi_slv_seq_item_c item);

   `uvm_info(get_type_name(), $sformatf("read address, response by aw_ready"), UVM_HIGH)
   aw_latency_status = 1;
   repeat (item.aw_delay) begin
      @(slave_mp.slv_axi_cb);
   end
   slave_mp.slv_axi_cb.aw_ready <= 1'b1;
   @(slave_mp.slv_axi_cb);

   slave_mp.slv_axi_cb.aw_ready <= 1'b0;
   aw_latency_status = 0;

   `uvm_info(get_type_name(), $sformatf("finish driving awready"), UVM_HIGH)

endtask

task uvma_axi_drv_c:: w_drv(uvma_axi_slv_seq_item_c item);

   `uvm_info(get_type_name(), $sformatf("write w_data driver start"), UVM_HIGH)
   w_latency_status = 1;
   repeat (item.w_delay) begin
      @(slave_mp.slv_axi_cb);
   end
   this.slave_mp.slv_axi_cb.w_ready <= 1'b1;
   @(slave_mp.slv_axi_cb);

   this.slave_mp.slv_axi_cb.w_ready <= 1'b0;
   w_latency_status = 0;

   `uvm_info(get_type_name(), $sformatf("finish driving wready"), UVM_HIGH)

endtask

task uvma_axi_drv_c:: ar_drv(uvma_axi_slv_seq_item_c item);

   `uvm_info(get_type_name(), $sformatf("read address, response by ar_ready"), UVM_HIGH)
   ar_latency_status = 1;
   repeat (item.ar_delay) begin
      @(slave_mp.slv_axi_cb);
   end
   this.slave_mp.slv_axi_cb.ar_ready <= 1'b1;
   @(slave_mp.slv_axi_cb);

   this.slave_mp.slv_axi_cb.ar_ready <= 1'b0;
   ar_latency_status = 0;

   `uvm_info(get_type_name(), $sformatf("finish driving arready"), UVM_HIGH)

endtask

task uvma_axi_drv_c:: r_drv(uvma_axi_slv_seq_item_c item);

   `uvm_info(get_type_name(),$sformatf("response, send r_data to DUT"), UVM_HIGH)

   this.slave_mp.slv_axi_cb.r_id    <= item.r_id;
   this.slave_mp.slv_axi_cb.r_resp  <= item.r_resp;
   this.slave_mp.slv_axi_cb.r_user  <= item.r_user;
   this.slave_mp.slv_axi_cb.r_last  <= item.r_last;
   this.slave_mp.slv_axi_cb.r_valid <= item.r_valid;
   this.slave_mp.slv_axi_cb.r_data  <= item.r_data;
   @(slave_mp.slv_axi_cb);

   `uvm_info(get_type_name(), $sformatf("finish driving r_item"), UVM_HIGH)

endtask

task uvma_axi_drv_c:: b_drv(uvma_axi_slv_seq_item_c item);

   `uvm_info(get_type_name(),$sformatf("response, send resp to DUT"), UVM_HIGH)

   this.slave_mp.slv_axi_cb.b_id    <= item.b_id;
   this.slave_mp.slv_axi_cb.b_resp  <= item.b_resp;
   this.slave_mp.slv_axi_cb.b_user  <= item.b_user;
   this.slave_mp.slv_axi_cb.b_user  <= item.b_user;
   this.slave_mp.slv_axi_cb.b_valid <= item.b_valid;
   @(slave_mp.slv_axi_cb);

   `uvm_info(get_type_name(), $sformatf("finish driving b_item"), UVM_HIGH)

endtask

`endif   // __UVMA_AXI_DRV_SV__

