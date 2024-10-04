// Copyright 2023 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group

/**** AXI driver  ****/

`ifndef __UVMA_AXI_DRV_SV__
`define __UVMA_AXI_DRV_SV__

/**
 * Component driving a AXI virtual interface (uvma_axi_intf).
 */
class uvma_axi_drv_c extends uvm_driver #(uvma_axi_transaction_c);

   `uvm_component_utils(uvma_axi_drv_c)

   // Objects
   uvma_axi_cfg_c                      cfg;
   uvma_axi_cntxt_c                    cntxt;

   // Handles to virtual interface modport
   virtual uvma_axi_intf.slave        slave_mp;

   event reset_asserted ;
   event reset_deasserted ;

   // Queue for storing transactions
   uvma_axi_transaction_c   ar_txn_queue[$];
   uvma_axi_transaction_c   r_txn_queue[$];
   uvma_axi_transaction_c   aw_txn_queue[$];
   uvma_axi_transaction_c   w_txn_queue[$];
   uvma_axi_transaction_c   b_txn_queue[$];

   int aw_latency_status = 0;
   int w_latency_status  = 0;
   int ar_latency_status = 0;
   int r_latency_status  = 0;
   int b_latency_status  = 0;

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
   extern virtual  task pre_reset_phase(uvm_phase phase);

   /**
    * Called by run_phase() while agent is in reset state.
    */
   extern virtual  task reset_phase(uvm_phase phase);

   /**
    * Called by run_phase() while agent is in post-reset state.
    */
   extern virtual  task post_reset_phase(uvm_phase phase);

   /**
    * Drives the AW channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     get_item();

   /**
    * Drives the AW channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     aw_drv();

   /**
    * Drives the W channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     w_drv();

   /**
    * Drives the R channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     b_drv();

   /**
    * Drives the B channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     ar_drv();

   /**
    * Drives the AR channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     r_drv();

    /**
    * Drive R channel signals
    */
   extern task drive_R_channel_signals( uvma_axi_transaction_c  r_txn = null );

   /**
    * Drives the B channel signals
    */
   extern task drive_B_channel_signals( uvma_axi_transaction_c  b_txn = null );

   /**
    * Drives the R channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task finish();

endclass: uvma_axi_drv_c


function uvma_axi_drv_c::new(string name = "uvma_axi_drv_c", uvm_component parent);
   super.new(name, parent);
endfunction


function void uvma_axi_drv_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   if(!uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt)) begin
      `uvm_fatal("build_phase", "driver reset cntxt class failed")
   end

   void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   this.slave_mp = this.cntxt.axi_vi.slave;

endfunction

// ------------------------------------------------------------------------
// Pre reset phase
// ------------------------------------------------------------------------
task uvma_axi_drv_c::pre_reset_phase(uvm_phase phase);

   `uvm_info(get_type_name(), $sformatf("start drv_pre_reset"), UVM_DEBUG)

   @(reset_asserted);
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
   r_latency_status = 0;
   b_latency_status = 0;
   `uvm_info(get_type_name(), "Pre Reset stage complete.", UVM_DEBUG)
endtask : pre_reset_phase

// ------------------------------------------------------------------------
// Reset phase
// ------------------------------------------------------------------------
task uvma_axi_drv_c::reset_phase(uvm_phase phase);
   super.reset_phase(phase);

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
   b_latency_status = 0;
   r_latency_status = 0;

   `uvm_info(get_type_name(), "Reset stage complete.", UVM_DEBUG)
endtask

// ------------------------------------------------------------------------
// Post reset phase
// ------------------------------------------------------------------------
task uvma_axi_drv_c::post_reset_phase(uvm_phase phase);
  -> reset_deasserted;
  `uvm_info(get_type_name(), "Post Reset stage complete.", UVM_DEBUG)
endtask : post_reset_phase

// -----------------------------------------------------------------------
// Run Phase
// -----------------------------------------------------------------------
task uvma_axi_drv_c::run_phase(uvm_phase phase);

   forever begin
      @(reset_deasserted);

	  fork
         get_item();
	  join_none

      if ( cfg.is_slave ) begin
         fork // Slave tasks
               ar_drv();
               r_drv();
               aw_drv();
               w_drv();
               b_drv();
         join_none
      end else begin

      end

      @(reset_asserted);
      disable fork;
   end

endtask : run_phase


task uvma_axi_drv_c::get_item();

   forever begin
      uvma_axi_transaction_c txn_queue = uvma_axi_transaction_c::type_id::create("txn_queue");
      seq_item_port.get_next_item(req);
      `uvm_info(get_type_name(), $sformatf("get item %s", req.m_txn_type), UVM_HIGH)

      $cast(txn_queue, req.clone());

      if ( cfg.is_slave ) begin
         case ( txn_queue.m_txn_type )
            UVMA_AXI_READ_REQ       : ar_txn_queue.push_back(txn_queue);
            UVMA_AXI_READ_RSP       : r_txn_queue.push_back(txn_queue);
            UVMA_AXI_WRITE_ADD_REQ  : aw_txn_queue.push_back(txn_queue);
            UVMA_AXI_WRITE_DATA_REQ : w_txn_queue.push_back(txn_queue);
            UVMA_AXI_WRITE_RSP      : b_txn_queue.push_back(txn_queue);
         endcase
      end else begin
         //TODO :
      end

      seq_item_port.item_done();
   end

endtask


task uvma_axi_drv_c:: ar_drv();

   forever begin
      `uvm_info(get_type_name(), $sformatf("read address, response by ar_ready"), UVM_HIGH)
      wait ( ar_txn_queue.size() != 0 );

      repeat (ar_txn_queue[0].ready_delay_cycle_chan_ax) begin
         @(slave_mp.slv_axi_cb);
      end

      this.slave_mp.slv_axi_cb.ar_ready <= 1'b1;
      @(slave_mp.slv_axi_cb);

      this.slave_mp.slv_axi_cb.ar_ready <= 1'b0;
      ar_txn_queue.delete(0);
      `uvm_info(get_type_name(), $sformatf("finish driving arready"), UVM_HIGH)
   end

endtask


task uvma_axi_drv_c:: r_drv();

   forever begin
      `uvm_info(get_type_name(),$sformatf("response, start driving read response"), UVM_HIGH)
      drive_R_channel_signals();
      wait ( r_txn_queue.size() != 0 );

      if(cfg.external_mem) begin
         @(slave_mp.slv_axi_cb);
      end
      repeat (r_txn_queue[0].m_delay_cycle_flits[0]) begin
         @(slave_mp.slv_axi_cb);
      end

      drive_R_channel_signals(r_txn_queue.pop_front());
      do begin
         this.slave_mp.slv_axi_cb.r_valid <= 1;
         @(slave_mp.slv_axi_cb);
      end while ( this.slave_mp.slv_axi_cb.r_ready == 0 );

      this.slave_mp.slv_axi_cb.r_valid <= 0;

      `uvm_info(get_type_name(), $sformatf("finish driving r_item"), UVM_HIGH)
   end

endtask


task uvma_axi_drv_c:: aw_drv();

   forever begin
      `uvm_info(get_type_name(), $sformatf("read address, response by aw_ready"), UVM_HIGH)
      wait ( aw_txn_queue.size() != 0 );
      repeat (aw_txn_queue[0].ready_delay_cycle_chan_ax) begin
         @(slave_mp.slv_axi_cb);
      end

      this.slave_mp.slv_axi_cb.aw_ready <= 1'b1;
      @(slave_mp.slv_axi_cb);

      this.slave_mp.slv_axi_cb.aw_ready <= 1'b0;
      aw_txn_queue.delete(0);
      `uvm_info(get_type_name(), $sformatf("finish driving awready"), UVM_HIGH)
   end

endtask


task uvma_axi_drv_c:: w_drv();

   forever begin
      `uvm_info(get_type_name(), $sformatf("read address, response by w_ready"), UVM_HIGH)
      wait ( w_txn_queue.size() != 0 );
      repeat (w_txn_queue[0].ready_delay_cycle_chan_w[0]) begin
         @(slave_mp.slv_axi_cb);
      end

      this.slave_mp.slv_axi_cb.w_ready <= 1'b1;
      @(slave_mp.slv_axi_cb);

      this.slave_mp.slv_axi_cb.w_ready <= 1'b0;
      w_txn_queue.delete(0);
      `uvm_info(get_type_name(), $sformatf("finish driving wready"), UVM_HIGH)
   end

endtask


task uvma_axi_drv_c:: b_drv();

   forever begin
      `uvm_info(get_type_name(),$sformatf("response, start driving write response"), UVM_HIGH)

      drive_B_channel_signals();
      wait ( b_txn_queue.size() != 0 );

      if(cfg.external_mem) begin
         @(slave_mp.slv_axi_cb);
      end

      repeat (b_txn_queue[0].m_delay_cycle_chan_X) begin
         @(slave_mp.slv_axi_cb);
      end
      drive_B_channel_signals(b_txn_queue.pop_front());

      do begin
         this.slave_mp.slv_axi_cb.b_valid <= 1;
         @(slave_mp.slv_axi_cb);
      end while ( slave_mp.slv_axi_cb.b_ready == 0 );

      // End of the first flit transaction
      this.slave_mp.slv_axi_cb.b_valid <= 0;

      `uvm_info(get_type_name(), $sformatf("finish driving b_item"), UVM_HIGH)
   end

endtask


task uvma_axi_drv_c::drive_R_channel_signals( uvma_axi_transaction_c  r_txn = null );

   if ( ( r_txn == null ) && ( cfg.driver_idle_value_cfg == RANDOM ) ) begin
     r_txn = new();
     r_txn.m_txn_config = cfg.txn_config;
     if (!r_txn.randomize() with 
       { m_txn_type    == UVMA_AXI_READ_RSP ;
       } )
       `uvm_error(get_type_name(),"Error randomizing the read response metadata");
   end

   if ( r_txn != null ) begin
     this.slave_mp.slv_axi_cb.r_id      <= r_txn.m_id      ;
     this.slave_mp.slv_axi_cb.r_data    <= r_txn.m_data[0] ;
     this.slave_mp.slv_axi_cb.r_resp    <= uvma_axi_sig_resp_t'(r_txn.m_resp[0]) ;
     this.slave_mp.slv_axi_cb.r_last    <= r_txn.m_last[0] ;
     this.slave_mp.slv_axi_cb.r_user    <= r_txn.m_user    ;
     this.slave_mp.slv_axi_cb.r_datachk <= r_txn.m_datachk ;
     this.slave_mp.slv_axi_cb.r_poison  <= r_txn.m_poison  ;
     this.slave_mp.slv_axi_cb.r_trace   <= r_txn.m_trace   ;
     this.slave_mp.slv_axi_cb.r_loop    <= r_txn.m_loop    ;
     this.slave_mp.slv_axi_cb.r_idunq   <= r_txn.m_idunq   ;
   end else begin
     // Payload
     this.slave_mp.slv_axi_cb.r_id      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.r_data    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.r_resp    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.r_last    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.r_user    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.r_datachk <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.r_poison  <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.r_trace   <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.r_loop    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.r_idunq   <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
   end

   // Control signal
   this.slave_mp.slv_axi_cb.r_valid <= 0 ;

endtask // drive_idle_R_channel


task uvma_axi_drv_c::drive_B_channel_signals( uvma_axi_transaction_c  b_txn = null );

   if ( ( b_txn == null ) && ( cfg.driver_idle_value_cfg == RANDOM ) ) begin
     b_txn = new();
     b_txn.m_txn_config = cfg.txn_config;
     if (!b_txn.randomize() with
       { m_txn_type    == UVMA_AXI_WRITE_RSP ;
       } )
       `uvm_error(get_type_name(),"Error randomizing the write response metadata");
   end

   if ( b_txn != null ) begin
     this.slave_mp.slv_axi_cb.b_id    <= b_txn.m_id      ;
     this.slave_mp.slv_axi_cb.b_resp  <= uvma_axi_sig_resp_t'(b_txn.m_resp[0]) ;
     this.slave_mp.slv_axi_cb.b_user  <= b_txn.m_user    ;
     this.slave_mp.slv_axi_cb.b_trace <= b_txn.m_trace   ;
     this.slave_mp.slv_axi_cb.b_loop  <= b_txn.m_loop    ;
     this.slave_mp.slv_axi_cb.b_idunq <= b_txn.m_idunq   ;
   end else begin
     // Payload
     this.slave_mp.slv_axi_cb.b_id      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.b_resp    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.b_user    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.b_trace   <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.b_loop    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
     this.slave_mp.slv_axi_cb.b_idunq   <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
   end

   // Control signal
   this.slave_mp.slv_axi_cb.b_valid <= 0 ;

endtask // drive_idle_B_channel

`endif   // __UVMA_AXI_DRV_SV__
