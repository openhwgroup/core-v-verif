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
   virtual uvma_axi_mst_intf          master_mp;

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

   // Queue for storing transactions between the request and the response:
   // the request is stored to keep its sequencer values, and extracted when
   // sending back the corresponding response
   uvma_axi_transaction_c   global_txn_queue[string][$] ;

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
    * Recieves the AW channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     aw_rcv();
   /**
    * Drives the AW channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     aw_drv();

   /**
    * Recieves the W channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     w_rcv();
   /**
    * Drives the W channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     w_drv();


   /**
    * Drives the R channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     b_drv();
   /**
    * Recieves the R channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     b_rcv();

   /**
    * Recieves the B channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     ar_rcv();
   /**
    * Drives the B channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     ar_drv();

   /**
    * Drives the AR channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     r_drv();
   /**
    * Drives the AR channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
   extern task     r_rcv();

    /**
    * Drive R channel signals
    */
   extern task drive_R_channel_signals( uvma_axi_transaction_c  r_txn = null );

   /**
    * Drives the B channel signals
    */
   extern task drive_B_channel_signals( uvma_axi_transaction_c  b_txn = null );

    /**
    * Drive AW channel signals
    */
   extern task drive_AW_channel_signals( uvma_axi_transaction_c  aw_txn = null );
    /**
    * Drive W channel signals
    */
   extern task drive_W_channel_signals( uvma_axi_transaction_c  w_txn = null );

   /**
    * Drives the   AR channel signals
    */
   extern task drive_AR_channel_signals( uvma_axi_transaction_c  ar_txn = null );

   /**
    * Drives the R channel of the AXI virtual interface's (cntxt.vif) signals using item's contents.
    */
//   extern task finish();

    // task to wait a specific number of clock cycle
    task automatic wait_n_clock_cycle( int unsigned n_clock_cycle );
      for (int i = 0 ; i < n_clock_cycle ; i++) begin
        @(posedge master_mp.clk);
      end
    endtask
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
   this.master_mp = this.cntxt.axi_mst_vi;

endfunction

// ------------------------------------------------------------------------
// Pre reset phase
// ------------------------------------------------------------------------
task uvma_axi_drv_c::pre_reset_phase(uvm_phase phase);

   `uvm_info(get_type_name(), $sformatf("start drv_pre_reset"), UVM_DEBUG)

   ->reset_asserted;
   if(cfg.is_slave) begin
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
   end
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

   if(cfg.is_slave) begin
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
   end

      // Emptying the queues
   aw_txn_queue.delete() ;
   w_txn_queue.delete()  ;
   ar_txn_queue.delete() ;
   b_txn_queue.delete()  ;
   r_txn_queue.delete()  ;

   // Driving idle bus values
   if ( !cfg.is_slave ) begin
     drive_AW_channel_signals();
     drive_W_channel_signals();
     drive_AR_channel_signals();
   end else begin
     drive_B_channel_signals();
     drive_R_channel_signals();
   end

   global_txn_queue.delete();


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
               ar_rcv();
               r_drv();
               aw_rcv();
               w_rcv();
               b_drv();
         join_none
      end else begin
         fork // Slave tasks
                aw_drv();
                w_drv();
                b_rcv();
                ar_drv();
                r_rcv();
         join_none
      end

      @(reset_asserted);
      disable fork;
   end

endtask : run_phase


task uvma_axi_drv_c::get_item();
   string ids_s;

   forever begin
      uvma_axi_transaction_c txn_queue = uvma_axi_transaction_c::type_id::create("txn_queue");
      seq_item_port.get_next_item(req);
      `uvm_info(get_type_name(), $sformatf("get item %s", req.m_txn_type), UVM_HIGH)

      $cast(txn_queue, req.clone());

      // In case of an Atomic Store, only a write response is expected. The other
      // atomic transactions expect a read response as well
      if ( ( txn_queue.m_atop[5]) && ( txn_queue.m_txn_type == UVMA_AXI_WRITE_REQ ) ) begin
        ids_s = $sformatf("UVMA_AXI_READ_REQ_%0h", req.m_id);
        global_txn_queue[ids_s].push_front(req);
      end

      ids_s = $sformatf("%0s_%0h", req.m_txn_type, req.m_id);
      // Storing the transaction in an associate array of queue to use it
      // when its time to send back the corresponding response to the sequence
      `uvm_info(get_type_name(), 
              $sformatf("setting id global_txn_queue: ID=%0s(s)", ids_s), UVM_LOW )
      global_txn_queue[ids_s].push_front(req);

      if ( cfg.is_slave ) begin
         case ( txn_queue.m_txn_type )
            UVMA_AXI_READ_REQ       : ar_txn_queue.push_back(txn_queue);
            UVMA_AXI_READ_RSP       : r_txn_queue.push_back(txn_queue);
            UVMA_AXI_WRITE_ADD_REQ  : aw_txn_queue.push_back(txn_queue);
            UVMA_AXI_WRITE_DATA_REQ : w_txn_queue.push_back(txn_queue);
            UVMA_AXI_WRITE_RSP      : b_txn_queue.push_back(txn_queue);
         endcase
      end else begin
         case (req.m_txn_type)
           UVMA_AXI_WRITE_REQ : begin
             fork
               aw_txn_queue.push_front(txn_queue) ;
               w_txn_queue.push_front(txn_queue)  ;
             join_none
           end
           UVMA_AXI_READ_REQ  : begin ar_txn_queue.push_front(txn_queue) ; end
           UVMA_AXI_WRITE_RSP : begin `uvm_warning(get_type_name(), "This driver is on the master side, and can't drive slave controlled channel by sending a AXI_WRITE_RSP") end
           UVMA_AXI_READ_RSP  : begin `uvm_warning(get_type_name(), "This driver is on the master side, and can't drive slave controlled channel by sending a AXI_READ_RSP") end
         endcase 
      end

      seq_item_port.item_done();
   end

endtask


task uvma_axi_drv_c:: ar_rcv();

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


task uvma_axi_drv_c:: aw_rcv();

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


task uvma_axi_drv_c:: w_rcv();

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

// ----------------------------------------------------------------------------
// Receive B channel ( Master tasks ) 
// Task in charge of receiving the response on the B channel by managing
// the b_ready signal
// ----------------------------------------------------------------------------
task uvma_axi_drv_c::b_rcv();
  uvma_axi_transaction_c txn;
  string ids_s;

  `uvm_info(get_type_name(), "receive_B_channel task is starting", UVM_DEBUG)

  forever begin
    @(posedge this.master_mp.clk);

    if ( this.master_mp.b_valid && this.master_mp.b_ready ) begin

      // Get the IDS_s from the response, to identify the request associated
      // to this transaction in the associative array
      ids_s = $sformatf("%0s_%0h", "UVMA_AXI_WRITE_REQ", this.master_mp.b_id );

      // Get the original transaction from the associative array/queu
      if ( global_txn_queue.exists( ids_s ) ) begin
        // Extract the transaction from the associative array/queue and
        // override it with the response
        txn = global_txn_queue[ids_s].pop_back();
        if ( global_txn_queue[ids_s].size() == 0 )
          global_txn_queue.delete(ids_s);
        `uvm_info(get_type_name(),
         $sformatf("%0s", txn.convert2string()),
         UVM_DEBUG)

        txn.m_txn_type = UVMA_AXI_WRITE_RSP            ;
        txn.m_id       = this.master_mp.b_id    ;
        txn.m_user     = this.master_mp.b_user  ;
        txn.m_resp[0]  = uvma_axi_sig_resp_t'(this.master_mp.b_resp)  ;
        txn.m_trace    = this.master_mp.b_trace ;
        txn.m_loop     = this.master_mp.b_loop  ;

        // Sending the response to the sequencer on the posedge
        // @(posedge this.master_mp.clk);
        seq_item_port.put( txn );

      end else begin
        `uvm_error(get_type_name(), 
            $sformatf("No corresponding txn found in global_txn_queue: ID=%0s(s)", ids_s) )
      end
    end // if

  end // forever

endtask // receive_B_channel

// ----------------------------------------------------------------------------
// Receive R channel ( Master task ) 
// Task in charge of receiving the response on the R channel by managing
// the r_ready signal
// ----------------------------------------------------------------------------
task uvma_axi_drv_c::r_rcv();
  uvma_axi_transaction_c txn;
  uvma_axi_sig_data_t       m_data[$];
  uvma_axi_sig_resp_t       m_resp[$];
  string ids_s ;

  `uvm_info(get_type_name(), "receive_R_channel task is starting", UVM_DEBUG)

  forever begin
    @(posedge this.master_mp.clk);

    if ( this.master_mp.r_valid && this.master_mp.r_ready ) begin


      // Assign data 
      m_data.push_back(this.master_mp.r_data);
      m_resp.push_back(this.master_mp.r_resp);

      // Wait for the read response to be completed before sending the
      // response to the sequencer        
      if ( this.master_mp.r_last ) begin

        // Get the IDS_s from the response, to identify the request associated
        // to this transaction in the associative array
        ids_s = $sformatf("%0s_%0h", "UVMA_AXI_READ_REQ", this.master_mp.r_id );

        // Get the original transaction from the associative array/queu
        if ( global_txn_queue.exists( ids_s ) ) begin

          // Extract the transaction from the associative array/queue and
          // override it with the response
          txn = global_txn_queue[ids_s].pop_back();
          if ( global_txn_queue[ids_s].size() == 0 )
            global_txn_queue.delete(ids_s);

          txn.m_txn_type = UVMA_AXI_READ_RSP;
          txn.m_id       = this.master_mp.r_id     ;

          for ( int i = 0 ; i < txn.m_len + 1 ; i++ ) begin
            txn.set_data_flit( m_data[i] , i ) ;
            txn.set_resp_flit( uvma_axi_sig_resp_t'(m_resp[i]) , i ) ;
          end
          m_data.delete();
          m_resp.delete();

          // Sending the transaction to the sequencer
          seq_item_port.put( txn );

        end else begin
          `uvm_error(get_type_name(), 
              $sformatf("No corresponding txn found in global_txn_queue: ID=%0s(s)", ids_s) )
        end // elsif
      end // if
    end // if

  end // forever

endtask // receive_R_channel

// ----------------------------------------------------------------------------
// Drive AR channel 
// Task in charge of driving transactions on the AR channel.
// ----------------------------------------------------------------------------
task uvma_axi_drv_c::ar_drv();
  uvma_axi_transaction_c ar_txn ;

  `uvm_info(get_type_name(), "drive_AR_channel task is starting", UVM_DEBUG)
  forever begin

    // Drive bus signals to idle while waiting for a transaction.
    drive_AR_channel_signals();

    // Waiting and extracting the last request from the queue
    wait ( ar_txn_queue.size() != 0 );
    ar_txn = ar_txn_queue.pop_back() ;

    // Applying the delay of the transaction before enabling the valid
    // signal
    if ( ar_txn.m_delay_cycle_chan_X != 0 )
      wait_n_clock_cycle( ar_txn.m_delay_cycle_chan_X );

    // Driving all the signals of the interface with the transaction
    drive_AR_channel_signals( ar_txn );

    // Handshake process
    this.master_mp.ar_valid <= 1;
    do begin
      @(posedge this.master_mp.clk);
    end while ( this.master_mp.ar_ready == 0 );

    // End of the transaction
    this.master_mp.ar_valid <= 0;

  end // forever

endtask // drive_AR_channel


// ----------------------------------------------------------------------------
// Drive AW channel 
// Task in charge of driving transactions on the AW channel.
// ----------------------------------------------------------------------------
task uvma_axi_drv_c::aw_drv();
  uvma_axi_transaction_c aw_txn ;

  `uvm_info(get_type_name(), "drive_AW_channel task is starting", UVM_DEBUG)
  forever begin

    // Drive bus signals to idle while waiting for a transaction.
    drive_AW_channel_signals();

    // Waiting and extracting the last request from the queue
    wait ( aw_txn_queue.size() != 0 );
    aw_txn = aw_txn_queue.pop_back() ;

    // Applying the delay of the transaction before enabling the valid
    // signal
    if ( aw_txn.m_delay_cycle_chan_X != 0 )
      wait_n_clock_cycle( aw_txn.m_delay_cycle_chan_X );

    // Driving all the signals of the interface with the transaction
    drive_AW_channel_signals( aw_txn );

    `uvm_info(get_type_name(), "DRIVING VALID", UVM_DEBUG)
    // Handshake process
    this.master_mp.aw_valid <= 1;
    do begin
      @(posedge this.master_mp.clk);
      `uvm_info(get_type_name(), $sformatf("READY ARRIVE, %d", this.master_mp.aw_ready), UVM_DEBUG)
    end while ( this.master_mp.aw_ready == 0 );

    // End of the transaction
    this.master_mp.aw_valid <= 0;
    `uvm_info(get_type_name(), "READY ARRIVE", UVM_DEBUG)

  end // forever

endtask // drive_AW_channel

// ----------------------------------------------------------------------------
// Drive W channel 
// Task in charge of driving transactions on the W channel.
// ----------------------------------------------------------------------------
task uvma_axi_drv_c::w_drv();
  uvma_axi_transaction_c w_txn  ;
  uvma_axi_transaction_c w_flit ;
  `uvm_info(get_type_name(), "drive_W_channel task is starting", UVM_DEBUG)
  forever begin

    // Drive bus signals to idle while waiting for a transaction.
    drive_W_channel_signals();

    // Waiting and extracting the last request from the queue
    wait ( w_txn_queue.size() != 0 );
    w_txn = w_txn_queue.pop_back() ;

    // Applying the delay of the transaction before enabling the valid
    // signal
    if ( w_txn.m_delay_cycle_chan_W != 0 )
      wait_n_clock_cycle( w_txn.m_delay_cycle_chan_W );

    for ( int i = 0 ; i < w_txn.m_len + 1 ; i++ ) begin
      // Driving all the signals of the interface with the transaction
      w_flit = new();
      w_flit.m_data.push_front( w_txn.m_data[i]  );
      w_flit.m_wstrb.push_front( w_txn.m_wstrb[i] );
      w_flit.m_last.push_front( w_txn.m_last[i]  );
      w_flit.m_user    = w_txn.m_user     ;
      w_flit.m_datachk = w_txn.m_datachk  ;
      w_flit.m_poison  = w_txn.m_poison   ;
      w_flit.m_trace   = w_txn.m_trace    ;

      drive_W_channel_signals( w_flit ) ;

      // Handshake process
      this.master_mp.w_valid <= 1;
      do begin
        @(posedge this.master_mp.clk);
      end while ( this.master_mp.w_ready == 0 ); 

      // End of the first flit transaction
      this.master_mp.w_valid <= 0;
      if ( w_txn.m_delay_cycle_flits[i] != 0 )
        wait_n_clock_cycle( w_txn.m_delay_cycle_flits[i] );

    end // for
    this.master_mp.w_last <= 0;

  end // forever

endtask // drive_W_channel



task uvma_axi_drv_c::drive_R_channel_signals( uvma_axi_transaction_c  r_txn = null );

   if ( ( r_txn == null ) && ( cfg.driver_idle_value_cfg == RANDOM ) ) begin
     r_txn = new();
     r_txn.m_txn_config = cfg.txn_config;
     r_txn.m_id    = $urandom();
     r_txn.m_resp.push_back($urandom_range(3));
     r_txn.m_data.push_back($urandom());
     r_txn.m_last.push_back($urandom_range(1));
     r_txn.m_x_user.push_back($urandom());
     r_txn.m_datachk = $urandom_range(2**(MAX_DATA_WIDTH/8));
     r_txn.m_poison  = $urandom_range(2**(MAX_DATA_WIDTH/64));
     r_txn.m_trace   = $urandom_range(1);
     r_txn.m_loop    = $urandom_range(2**MAX_LOOP_WIDTH);
     r_txn.m_idunq   = $urandom_range(1);
   end

   if ( r_txn != null ) begin
     this.slave_mp.slv_axi_cb.r_id      <= r_txn.m_id      ;
     this.slave_mp.slv_axi_cb.r_data    <= r_txn.m_data[0] ;
     this.slave_mp.slv_axi_cb.r_resp    <= uvma_axi_sig_resp_t'(r_txn.m_resp[0]) ;
     this.slave_mp.slv_axi_cb.r_last    <= r_txn.m_last[0] ;
     this.slave_mp.slv_axi_cb.r_user    <= r_txn.m_x_user[0] ;
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
     b_txn.m_id    = $urandom();
     b_txn.m_resp.push_back($urandom_range(3));
     b_txn.m_user  = $urandom();
     b_txn.m_trace = $urandom_range(1);
     b_txn.m_loop  = $urandom_range(2**MAX_LOOP_WIDTH);
     b_txn.m_idunq = $urandom_range(1);

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

// ----------------------------------------------------------------------------
// Drive AW channel signals
// ----------------------------------------------------------------------------
task uvma_axi_drv_c::drive_AW_channel_signals( uvma_axi_transaction_c  aw_txn = null );

  if ( ( aw_txn == null ) && ( cfg.driver_idle_value_cfg == RANDOM ) ) begin
    aw_txn = new();
    aw_txn.m_txn_config = cfg.txn_config;
    if (!aw_txn.randomize() with 
      { m_txn_type           == UVMA_AXI_WRITE_REQ ;
        m_axi_version        == m_axi_version ;
      } )
      `uvm_error(get_type_name(),"Error randomizing the request metadata");
  end

  if ( aw_txn != null ) begin
    // Payload
    this.master_mp.aw_id          <= aw_txn.m_id                     ;
    this.master_mp.aw_addr        <= aw_txn.m_addr                   ;
    this.master_mp.aw_len         <= aw_txn.m_len                    ;
    this.master_mp.aw_size        <= uvma_axi_sig_size_t'(aw_txn.m_size)  ;
    this.master_mp.aw_burst       <= uvma_axi_sig_burst_t'(aw_txn.m_burst);
    this.master_mp.aw_lock        <= uvma_axi_sig_lock_t'(aw_txn.m_lock)  ;
    this.master_mp.aw_cache       <= aw_txn.m_cache                  ;
    this.master_mp.aw_prot        <= uvma_axi_sig_prot_t'(aw_txn.m_prot)  ;
    this.master_mp.aw_qos         <= aw_txn.m_qos                    ;
    this.master_mp.aw_region      <= aw_txn.m_region                 ;
    this.master_mp.aw_user        <= aw_txn.m_user                   ;
    this.master_mp.aw_atop        <= aw_txn.m_atop                   ;
    this.master_mp.aw_trace       <= aw_txn.m_trace                  ;
    this.master_mp.aw_loop        <= aw_txn.m_loop                   ;
    this.master_mp.aw_mmusecsid   <= aw_txn.m_mmusecsid              ;
    this.master_mp.aw_mmusid      <= aw_txn.m_mmusid                 ;
    this.master_mp.aw_mmussidv    <= aw_txn.m_mmussidv               ;
    this.master_mp.aw_mmussid     <= aw_txn.m_mmussid                ;
    this.master_mp.aw_mmuatst     <= aw_txn.m_mmuatst                ;
    this.master_mp.aw_nsaid       <= aw_txn.m_nsaid                  ;
    this.master_mp.aw_idunq       <= aw_txn.m_idunq                  ;
  end else begin
    // Payload
    this.master_mp.aw_id        <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_addr      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_len       <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_size      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_burst     <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_lock      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_cache     <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_prot      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_qos       <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_region    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_user      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_atop      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_trace     <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_loop      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_mmusecsid <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_mmusid    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_mmussidv  <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_mmussid   <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_mmuatst   <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_nsaid     <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.aw_idunq     <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
  end // if

  // Control signal
  this.master_mp.aw_valid <= 0 ;

endtask // drive_AW_channel_signals

// ----------------------------------------------------------------------------
// Drive idle AR channel signals
// ----------------------------------------------------------------------------
task uvma_axi_drv_c::drive_AR_channel_signals( uvma_axi_transaction_c  ar_txn = null );

  if ( ( ar_txn == null ) && ( cfg.driver_idle_value_cfg == RANDOM ) ) begin
    ar_txn = new();
    ar_txn.m_txn_config = cfg.txn_config;
    if (!ar_txn.randomize() with 
      { m_txn_type    == UVMA_AXI_READ_REQ ;
        m_axi_version == m_axi_version ;
      } )
      `uvm_error(get_type_name(),"Error randomizing the read request metadata");
  end

  if ( ar_txn != null ) begin
    this.master_mp.ar_id        <= ar_txn.m_id          ;
    this.master_mp.ar_addr      <= ar_txn.m_addr        ;
    this.master_mp.ar_len       <= ar_txn.m_len         ;
    this.master_mp.ar_size      <= uvma_axi_sig_size_t'(ar_txn.m_size)        ;
    this.master_mp.ar_burst     <= uvma_axi_sig_burst_t'(ar_txn.m_burst)       ;
    this.master_mp.ar_lock      <= uvma_axi_sig_lock_t'(ar_txn.m_lock)        ;
    this.master_mp.ar_cache     <= ar_txn.m_cache       ;
    this.master_mp.ar_prot      <= uvma_axi_sig_prot_t'(ar_txn.m_prot)        ;
    this.master_mp.ar_qos       <= ar_txn.m_qos         ;
    this.master_mp.ar_region    <= ar_txn.m_region      ;
    this.master_mp.ar_user      <= ar_txn.m_user        ;
    this.master_mp.ar_trace     <= ar_txn.m_trace       ;
    this.master_mp.ar_loop      <= ar_txn.m_loop        ;
    this.master_mp.ar_mmusecsid <= ar_txn.m_mmusecsid   ;
    this.master_mp.ar_mmusid    <= ar_txn.m_mmusid      ;
    this.master_mp.ar_mmussidv  <= ar_txn.m_mmussidv    ;
    this.master_mp.ar_mmussid   <= ar_txn.m_mmussid     ;
    this.master_mp.ar_mmuatst   <= ar_txn.m_mmuatst     ;
    this.master_mp.ar_nsaid     <= ar_txn.m_nsaid       ;
    this.master_mp.ar_idunq     <= ar_txn.m_idunq       ;
  end else begin
    // Payload
    this.master_mp.ar_id        <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_addr      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_len       <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_size      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_burst     <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_lock      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_cache     <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_prot      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_qos       <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_region    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_user      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_trace     <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_loop      <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_mmusecsid <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_mmusid    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_mmussidv  <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_mmussid   <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_mmuatst   <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_nsaid     <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.ar_idunq     <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
  end

  // Control signal
  this.master_mp.ar_valid <= 0 ;

endtask // drive_idle_AR_channel


// ----------------------------------------------------------------------------
// Drive W channel signals 
// ----------------------------------------------------------------------------
task uvma_axi_drv_c::drive_W_channel_signals( uvma_axi_transaction_c  w_txn = null );

  if ( ( w_txn == null ) && ( cfg.driver_idle_value_cfg == RANDOM ) ) begin
    w_txn = new();
    w_txn.m_txn_config = cfg.txn_config;
    if (!w_txn.randomize() with 
      { m_txn_type    == UVMA_AXI_WRITE_REQ ;
        m_len         == 0             ;
        m_axi_version == m_axi_version ;
      } )
      `uvm_error(get_type_name(),"Error randomizing the request data");
  end

  if ( w_txn != null ) begin
    this.master_mp.w_data    <= w_txn.m_data[0]  ;
    this.master_mp.w_strb    <= w_txn.m_wstrb[0] ;
    this.master_mp.w_last    <= w_txn.m_last[0]  ;
    this.master_mp.w_user    <= w_txn.m_user     ;
    this.master_mp.w_datachk <= w_txn.m_datachk  ;
    this.master_mp.w_poison  <= w_txn.m_poison   ;
    this.master_mp.w_trace   <= w_txn.m_trace    ;
  end else begin
    // Payload
    this.master_mp.w_data    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.w_strb    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.w_last    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.w_user    <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.w_datachk <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.w_poison  <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
    this.master_mp.w_trace   <= ( cfg.driver_idle_value_cfg == UNDEFINED  ) ? 'hx : 0 ;
  end 

  // Control signal
  this.master_mp.w_valid <= 0 ;

endtask // drive_idle_W_channel
`endif   // __UVMA_AXI_DRV_SV__
