// ----------------------------------------------------------------------------
// Copyright 2023 CEA*
// *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
// Copyright 2023 Thales DIS SAS
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//[END OF HEADER]
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//  Description : Monitor AXI requests and responses
//                Based on the IHI0022F_b_amba_axi_protocol_specification from
//                ARM(TM).
//                The monitor is connected on the AXI channels via an
//                AXI interface. By using the control signals, he samples
//                the transaction going through the interface and convert them
//                into uvm_transaction (uvma_axi_transaction_c) which are then sent to a scoreboard.
//
//                This monitor also that each request get a response and count
//                the number of transactons that are exchanged.
//                The number of request/response counted are printed in the report phase.
//
//                Only the mode AXI INCR is supported by this monitor
//                This monitor should be given just after the initialisation the name of
//                its AXI interface to search in the uvm database, in case of multiple AXI
//                interfaces in the same testbench
//
// ----------------------------------------------------------------------------

// -----------------------------------------------------------------------
// Class uvma_axi_monitor
//
// Passive monitor which monitor the uvma_axi interface and send informations to
// the scoreboard
// -----------------------------------------------------------------------
class uvma_axi_mon_c extends uvm_monitor;

   `uvm_component_utils( uvma_axi_mon_c )

   // Objects
   uvma_axi_cfg_c                                cfg;
   uvma_axi_cntxt_c                              cntxt;

   // -----------------------------------------------------------------------
   // Analysis Ports
   // -----------------------------------------------------------------------
   uvm_analysis_port #(uvma_axi_transaction_c) m_uvma_axi_read_req_packets_collected  ;
   uvm_analysis_port #(uvma_axi_transaction_c) m_uvma_axi_write_req_packets_collected ;
   uvm_analysis_port #(uvma_axi_transaction_c) m_uvma_axi_write_add_req_packets_collected ;
   uvm_analysis_port #(uvma_axi_transaction_c) m_uvma_axi_write_data_req_packets_collected ;
   uvm_analysis_port #(uvma_axi_transaction_c) m_uvma_axi_read_rsp_packets_collected  ;
   uvm_analysis_port #(uvma_axi_transaction_c) m_uvma_axi_write_rsp_packets_collected ;
   uvm_analysis_port #(uvma_axi_transaction_c) m_uvma_axi_req_packets_collected ;

   // ------------------------------------------------------------------------
   // Virtual interfaces
   // ------------------------------------------------------------------------
   virtual uvma_axi_mst_intf                 mst_mp;
   virtual uvma_axi_intf.passive             passive_mp;

   // ------------------------------------------------------------------------
   // Local variable
   // ------------------------------------------------------------------------
   protected string            name ;
   protected uvma_axi_dv_ver_t axi_version ;
   int                         ar_hck_status = -1;
   int                         aw_hck_status = -1;
   int                         w_hck_status  = -1;

   event reset_asserted ;
   event reset_deasserted ;

   // -----------------------------------------------------------------------
   // Transaction queue for write packect
   // -----------------------------------------------------------------------
   uvma_axi_transaction_c m_queue_write_req[$];
   uvma_axi_transaction_c m_queue_write_dat[$];

   // -----------------------------------------------------------------------
   // Counter for the number of request/response that the monitor detects
   // -----------------------------------------------------------------------
   int m_num_rreq_pkts ; // read request counter
   int m_num_wreq_pkts ; // write request counter
   int m_num_wdat_pkts ; // write data counter
   int m_num_rrsp_pkts ; // response counter
   int m_num_wrsp_pkts ; // response counter

   // ------------------------------------------------------------------------
   // Constructor
   // ------------------------------------------------------------------------
   function new(string name = "uvma_axi_mon_c", uvm_component parent = null);
      super.new(name, parent);
      this.name = name;
   endfunction

   // -----------------------------------------------------------------------
   // Build Phase
   // -----------------------------------------------------------------------
   function void build_phase(uvm_phase phase);
      string interface_name;
      int unsigned id_width   ;
      int unsigned addr_width ;
      int unsigned data_width ;
      int unsigned user_width ;

      super.build_phase(phase);

      // Instantiation of the uvm_analysis_port
      m_uvma_axi_write_req_packets_collected      = new("m_uvma_axi_write_req_packets_collected" , this) ;
      m_uvma_axi_write_add_req_packets_collected  = new("m_uvma_axi_write_add_req_packets_collected" , this) ;
      m_uvma_axi_write_data_req_packets_collected = new("m_uvma_axi_write_data_req_packets_collected" , this) ;
      m_uvma_axi_read_req_packets_collected       = new("m_uvma_axi_read_req_packets_collected"  , this) ;
      m_uvma_axi_write_rsp_packets_collected      = new("m_uvma_axi_write_rsp_packets_collected" , this) ;
      m_uvma_axi_read_rsp_packets_collected       = new("m_uvma_axi_read_rsp_packets_collected"  , this) ;
      m_uvma_axi_req_packets_collected            = new("m_uvma_axi_req_packets_collected"  , this) ;

      void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("build_phase", "monitor cntxt class failed")
      end


      void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("CFG", "Configuration handle is null")
      end

      if(!cfg.is_slave) mst_mp     = cntxt.axi_mst_vi;
      else              passive_mp = cntxt.axi_vi.passive;

      // Get the driver configuration from the agent configuration
      axi_version       = cfg.version;

      // Covergroup bus size configuration
      id_width         = cfg.txn_config.get_id_width();
      addr_width       = cfg.txn_config.get_addr_width();
      data_width       = cfg.txn_config.get_data_width();

      // Give the version of the interface to the virtual interface, to
      // activate the corresponding assertion depending of the version
      //mst_mp.axi_version = axi_version ;

      // Initialisation of the value of the counter
      m_num_rreq_pkts = 0 ;
      m_num_wreq_pkts = 0 ;
      m_num_rrsp_pkts = 0 ;
      m_num_wrsp_pkts = 0 ;


      `uvm_info(this.name, "Build stage complete.", UVM_DEBUG)
   endfunction : build_phase

   // ------------------------------------------------------------------------
   // Pre reset phase
   // ------------------------------------------------------------------------
   virtual task pre_reset_phase(uvm_phase phase);
      -> reset_asserted;
      `uvm_info(this.name, "Pre Reset stage complete.", UVM_DEBUG)
   endtask : pre_reset_phase

   // ------------------------------------------------------------------------
   // Reset phase
   // ------------------------------------------------------------------------
   virtual task reset_phase(uvm_phase phase);
      super.reset_phase(phase);
      m_queue_write_req.delete();
      m_queue_write_dat.delete();

      // Initialisation of the value of the counter
      m_num_rreq_pkts = 0 ;
      m_num_wreq_pkts = 0 ;
      m_num_rrsp_pkts = 0 ;
      m_num_wrsp_pkts = 0 ;

      cntxt.reset_state = UVMA_AXI_RESET_STATE_IN_RESET;

      `uvm_info(this.name, "Reset stage complete.", UVM_DEBUG)
   endtask : reset_phase

   // ------------------------------------------------------------------------
   // Post reset phase
   // ------------------------------------------------------------------------
   virtual task post_reset_phase(uvm_phase phase);
      -> reset_deasserted;
      cntxt.reset_state = UVMA_AXI_RESET_STATE_POST_RESET;
      `uvm_info(this.name, "Post Reset stage complete.", UVM_DEBUG)
   endtask : post_reset_phase

   // -----------------------------------------------------------------------
   // Run Phase
   // -----------------------------------------------------------------------
   task run_phase(uvm_phase phase);
       forever begin
           @(reset_deasserted);
           if(cfg.is_slave) begin
             fork
                 receive_AW_channel_transaction_task(phase);
                 receive_W_channel_transaction_task(phase);
                 combine_write_req_data_task(phase);
                 receive_AR_channel_transaction_task(phase);
                 receive_B_channel_transaction_task(phase);
                 receive_R_channel_transaction_task(phase);
                 synchronize_transaction(phase);
             join_none
           end else begin
             fork
                 receive_mst_AW_channel_transaction_task(phase);
                 receive_mst_W_channel_transaction_task(phase);
                 combine_mst_write_req_data_task(phase);
                 receive_mst_AR_channel_transaction_task(phase);
                 receive_mst_B_channel_transaction_task(phase);
                 receive_mst_R_channel_transaction_task(phase);
                 synchronize_mst_transaction(phase);
             join_none
           end
           @(reset_asserted);
           disable fork;
       end
   endtask : run_phase

   // SLAVE MONITOR 
   // -----------------------------------------------------------------------
   // Task receive write requests
   //
   // Collect input write requests on the AW channel of the  uvma_axi interface
   // -----------------------------------------------------------------------
   task synchronize_transaction(uvm_phase phase);
      uvma_axi_transaction_c  req;

      forever begin
         @(passive_mp.psv_axi_cb);

         // Creating a new object to send to the scoreboard,
         // and get requests informations into it
         req = new();
         m_uvma_axi_req_packets_collected.write(req);
      end // forever
   endtask : synchronize_transaction

   // -----------------------------------------------------------------------
   // Task receive write requests
   //
   // Collect input write requests on the AW channel of the  uvma_axi interface
   // -----------------------------------------------------------------------
   task receive_AW_channel_transaction_task(uvm_phase phase);
      uvma_axi_transaction_c  wreq;
      uvma_axi_transaction_c  wreq_atop ;

      forever begin
         @(passive_mp.psv_axi_cb);
         // -----------------------------------------------------------------------
         // Collect request on Write Address and Write data channels
         // -----------------------------------------------------------------------
         if (passive_mp.psv_axi_cb.aw_valid) begin

            aw_hck_status++;
            if (passive_mp.psv_axi_cb.aw_ready) begin

               // Creating a new object to send to the scoreboard,
               // and get requests informations into it
               wreq = new();
               wreq.m_id                       = passive_mp.psv_axi_cb.aw_id                                ;
               wreq.m_addr                     = passive_mp.psv_axi_cb.aw_addr                              ;
               wreq.m_len                      = passive_mp.psv_axi_cb.aw_len                               ;
               wreq.m_size                     = uvma_axi_dv_size_t'(passive_mp.psv_axi_cb.aw_size )             ;
               wreq.m_burst                    = uvma_axi_dv_burst_t'(passive_mp.psv_axi_cb.aw_burst)            ;
               wreq.m_lock                     = uvma_axi_dv_lock_t'(passive_mp.psv_axi_cb.aw_lock )             ;
               wreq.m_cache                    = passive_mp.psv_axi_cb.aw_cache                             ;
               //TODO
               //wreq.m_mem_type                 = get_mem_type(AXI_WRITE_REQ,passive_mp.psv_axi_cb.aw_cache) ;
               wreq.m_prot                     = uvma_axi_dv_prot_t'(passive_mp.psv_axi_cb.aw_prot)              ;
               wreq.m_qos                      = passive_mp.psv_axi_cb.aw_qos                               ;
               wreq.m_region                   = passive_mp.psv_axi_cb.aw_region                            ;
               wreq.m_user                     = passive_mp.psv_axi_cb.aw_user                              ;
               wreq.m_atop                     = passive_mp.psv_axi_cb.aw_atop                              ;
               wreq.m_trace                    = passive_mp.psv_axi_cb.aw_trace                             ;
               wreq.m_loop                     = passive_mp.psv_axi_cb.aw_loop                              ;
               wreq.m_mmusecsid                = passive_mp.psv_axi_cb.aw_mmusecsid                         ;
               wreq.m_mmusid                   = passive_mp.psv_axi_cb.aw_mmusid                            ;
               wreq.m_mmussidv                 = passive_mp.psv_axi_cb.aw_mmussidv                          ;
               wreq.m_mmussid                  = passive_mp.psv_axi_cb.aw_mmussid                           ;
               wreq.m_mmuatst                  = passive_mp.psv_axi_cb.aw_mmuatst                           ;
               wreq.m_nsaid                    = passive_mp.psv_axi_cb.aw_nsaid                             ;
               wreq.m_idunq                    = passive_mp.psv_axi_cb.aw_idunq                             ;
               wreq.ready_delay_cycle_chan_ax  = aw_hck_status                                              ;

               wreq.m_txn_type     = UVMA_AXI_WRITE_ADD_REQ;
               wreq.m_axi_version  = axi_version;
               wreq.m_timestamp_ax = $time;
               wreq.m_timestamp.push_back($time);

               aw_hck_status = -1;

               // Print information about the transaction
               `uvm_info( this.name, $sformatf("WRITE_REQ=%0d(d), Info: %0s",m_num_wreq_pkts, wreq.convert2string()) , UVM_DEBUG)

               // Pushing a dummy read transaction into the protocol checker
               // if a atomic needing an additional read response is
               // detected.
               // This allows to receive the read response in the protocol
               // checker before the entire write transaction (AW + W) is
               // sent
               if ( wreq.m_atop[5] ) begin
                  wreq_atop = new();
                  $cast( wreq_atop, wreq.clone() );
                  if (wreq_atop.m_atop == 49) begin
                     if (wreq_atop.m_len > 0) wreq_atop.m_len = wreq_atop.m_len/2;
                     else wreq_atop.m_size = wreq_atop.m_size/2;
                  end
                  wreq_atop.m_txn_type = UVMA_AXI_READ_REQ ;
                  m_uvma_axi_read_req_packets_collected.write(wreq_atop);
               end

               // Push the write address request into a queue for the
               // combine_write_req_data_task
               m_queue_write_req.push_back(wreq);
               m_uvma_axi_write_add_req_packets_collected.write(wreq);

               // Increment Write Address counter
               m_num_wreq_pkts++;

            end // if
         end // if
      end // forever
   endtask : receive_AW_channel_transaction_task

   // ----------------------------------------------------------------------
   // ask receive write data
   //
   // ollect input write requests on the W channel of the uvma_axi interface
   // ----------------------------------------------------------------------
   task receive_W_channel_transaction_task(uvm_phase phase);
      uvma_axi_transaction_c   wreq_data;

      forever begin
         @(passive_mp.psv_axi_cb);
         // -----------------------------------------------------------------------
         // Collect request on Write Address and Write data channels
         // -----------------------------------------------------------------------
         if (passive_mp.psv_axi_cb.w_valid) begin

            w_hck_status++;
            if (passive_mp.psv_axi_cb.w_ready) begin

               // A new txn arrived, raise the uvm objection until its
               // response comes out
               // phase.raise_objection(this);

               // Creating a new object to send to the scoreboard,
               // and get requests informations into it
               wreq_data = new();

               wreq_data.m_data.push_back( passive_mp.psv_axi_cb.w_data)  ;
               wreq_data.m_wstrb.push_back(passive_mp.psv_axi_cb.w_strb)  ;
               wreq_data.m_last.push_back( passive_mp.psv_axi_cb.w_last)  ;
               wreq_data.m_x_user.push_back(passive_mp.psv_axi_cb.w_user) ;
               wreq_data.m_w_trace      = passive_mp.psv_axi_cb.w_trace   ;
               wreq_data.m_datachk      = passive_mp.psv_axi_cb.w_datachk ;
               wreq_data.m_poison       = passive_mp.psv_axi_cb.w_poison  ;
               wreq_data.m_poison       = passive_mp.psv_axi_cb.w_poison  ;
               wreq_data.ready_delay_cycle_chan_w.push_back(w_hck_status) ;

               wreq_data.m_txn_type     = UVMA_AXI_WRITE_DATA_REQ ;
               wreq_data.m_axi_version  = axi_version   ;
               wreq_data.m_timestamp.push_back($time)   ;

               w_hck_status = -1;

               // Print informations about the transaction
               `uvm_info( this.name, $sformatf("WRITE_DAT=%0d(d), Info: %0s",m_num_wdat_pkts, wreq_data.convert2string()) , UVM_DEBUG)

               // Push the Write data packet into the queue for the
               // combine_write_req_data_task
               m_queue_write_dat.push_back(wreq_data);

               m_uvma_axi_write_data_req_packets_collected.write(wreq_data);

               // Increment the Write data counter
               m_num_wdat_pkts++;

            end // if
         end
      end // forever
   endtask : receive_W_channel_transaction_task

   // -----------------------------------------------------------------------
   // Task combine write req data
   //
   // Collect input write address requests and write data requests on the uvma_axi
   // interface, on the AW and W channels, and combine their data into
   // transaction to send to the scoreboard
   // -----------------------------------------------------------------------
   task combine_write_req_data_task( uvm_phase phase );
      uvma_axi_transaction_c  wreq_addr ;
      uvma_axi_transaction_c  wreq_data ;
      uvma_axi_transaction_c  wreq_txn  ;

      uvma_axi_sig_len_t  req_len;
      int counter_data_pkt = 0   ;
      int counter_txn_pkt  = 0   ;

      forever begin
         wreq_addr = new();

         // Waiting for a new write address request
         wait( m_queue_write_req.size() != 0 );
         `uvm_info( this.name, $sformatf("WRITE address detected") , UVM_DEBUG)
         wreq_addr = m_queue_write_req.pop_front() ;
         $cast( wreq_txn, wreq_addr.clone() );
         wreq_txn.m_txn_type = UVMA_AXI_WRITE_REQ;
         req_len = wreq_txn.m_len ;

         // For each packet of a burst of a write data request, get the
         // data packet transaction from the queue
         for(int i = 0 ; i < wreq_addr.m_len + 1 ; i ++) begin
            wreq_data = new();
            // Waiting for a new write data request
            wait( m_queue_write_dat.size() != 0 );
            `uvm_info( this.name, $sformatf("WRITE data detected") , UVM_DEBUG)
            wreq_data = m_queue_write_dat.pop_front();

            // Creating a new object to send to the scoreboard,
            // and get requests informations into it by combining
            // write address and write data requests informations
            wreq_txn.append_write_flit(wreq_data.m_data[0],
                                       wreq_data.m_wstrb[0],
                                       wreq_data.m_last[0]);
            wreq_txn.m_datachk        = wreq_data.m_datachk      ;
            wreq_txn.m_poison         = wreq_data.m_poison       ;
            wreq_txn.m_timestamp.push_back(wreq_data.m_timestamp[0]) ;

            // Fixing the change of len introduced by the append_write_flit
            // function
            wreq_txn.m_len = req_len ;

            // Print informations about the transaction
            `uvm_info( this.name, $sformatf("WRITE_COMB_DAT=%0d(d), Info: %0s", counter_data_pkt, wreq_txn.convert2string()) , UVM_DEBUG)

            // Increment the Write data counter
            counter_data_pkt++;

         end // for

         // Increment the txn counter
         counter_txn_pkt++;

         `uvm_info( this.name, $sformatf("WRITE_TXN=%0d(d), Info: %0s", counter_txn_pkt, wreq_txn.convert2string()) , UVM_DEBUG)

         // Sending the transaction to the scoreboard
         m_uvma_axi_write_req_packets_collected.write(wreq_txn);

         fork
            begin
                int unsigned wreq_handle;
                uvma_axi_transaction_c req_write;
                req_write = new;
                $cast(req_write, wreq_data.clone());
                wreq_handle = begin_tr(req_write, "WRITE_REQ" );
                @(passive_mp.psv_axi_cb);
                end_tr( req_write );
            end
         join_none

      end // forever
   endtask : combine_write_req_data_task

   // -----------------------------------------------------------------------
   // Task receive read requests
   //
   // Collect input read requests on the uvma_axi interface, on the AR channel
   // -----------------------------------------------------------------------
   task receive_AR_channel_transaction_task(uvm_phase phase);
      uvma_axi_transaction_c rreq;

      forever begin
         @(passive_mp.psv_axi_cb);

         // -----------------------------------------------------------------------
         // Collect request on Read Address channel
         // -----------------------------------------------------------------------
         if (passive_mp.psv_axi_cb.ar_valid) begin
            ar_hck_status++;
            if (passive_mp.psv_axi_cb.ar_ready) begin

               // Creating a new object to send to the scoreboard,
               // and get requests informations into it
               rreq = new() ;
               rreq.m_id                       = passive_mp.psv_axi_cb.ar_id                               ;
               rreq.m_addr                     = passive_mp.psv_axi_cb.ar_addr                             ;
               rreq.m_len                      = passive_mp.psv_axi_cb.ar_len                              ;
               rreq.m_size                     = uvma_axi_dv_size_t'(passive_mp.psv_axi_cb.ar_size)             ;
               rreq.m_burst                    = uvma_axi_dv_burst_t'(passive_mp.psv_axi_cb.ar_burst)           ;
               rreq.m_lock                     = uvma_axi_dv_lock_t'(passive_mp.psv_axi_cb.ar_lock)             ;
               rreq.m_cache                    = passive_mp.psv_axi_cb.ar_cache                            ;
             //rreq.m_mem_type                 = get_mem_type(AXI_READ_REQ,passive_mp.psv_axi_cb.ar_cache) ;
               rreq.m_prot                     = uvma_axi_dv_prot_t'(passive_mp.psv_axi_cb.ar_prot)             ;
               rreq.m_qos                      = passive_mp.psv_axi_cb.ar_qos                              ;
               rreq.m_region                   = passive_mp.psv_axi_cb.ar_region                           ;
               rreq.m_user                     = passive_mp.psv_axi_cb.ar_user                             ;
               rreq.m_trace                    = passive_mp.psv_axi_cb.ar_trace                            ;
               rreq.m_loop                     = passive_mp.psv_axi_cb.ar_loop                             ;
               rreq.m_mmusecsid                = passive_mp.psv_axi_cb.ar_mmusecsid                        ;
               rreq.m_mmusid                   = passive_mp.psv_axi_cb.ar_mmusid                           ;
               rreq.m_mmussidv                 = passive_mp.psv_axi_cb.ar_mmussidv                         ;
               rreq.m_mmussid                  = passive_mp.psv_axi_cb.ar_mmussid                          ;
               rreq.m_mmuatst                  = passive_mp.psv_axi_cb.ar_mmuatst                          ;
               rreq.m_nsaid                    = passive_mp.psv_axi_cb.ar_nsaid                            ;
               rreq.m_idunq                    = passive_mp.psv_axi_cb.ar_idunq                            ;
               rreq.m_idunq                    = passive_mp.psv_axi_cb.ar_idunq                            ;
               rreq.ready_delay_cycle_chan_ax  = ar_hck_status                                             ;
               rreq.m_atop                     = 0                                                         ;
               rreq.m_txn_type     = UVMA_AXI_READ_REQ ;
               rreq.m_axi_version  = axi_version  ;
               rreq.m_timestamp_ax = $time        ;
               rreq.m_timestamp.push_back($time)  ;

               ar_hck_status = -1;

               // Print the information about the transaction
               `uvm_info( this.name, $sformatf("READ_REQ=%0d(d), Info: %0s",m_num_rreq_pkts, rreq.convert2string()) , UVM_DEBUG)
               // Send object to the scoreboard
               m_uvma_axi_read_req_packets_collected.write(rreq);

               // Increment the Read request counter
               m_num_rreq_pkts++;

               fork
                  begin
                     int unsigned rreq_handle;
                     uvma_axi_transaction_c req_read;
                     req_read = new;
                     $cast(req_read, rreq.clone());
                     rreq_handle = begin_tr(req_read, "READ_REQ" );
                     @(passive_mp.psv_axi_cb);
                     end_tr( req_read );
                  end
               join_none
            end // if
         end // if
      end // forever
   endtask : receive_AR_channel_transaction_task

   // -----------------------------------------------------------------------
   // Task receive response
   //
   // Collect input response on the uvma_axi interface, on the B channel
   // -----------------------------------------------------------------------
   task receive_B_channel_transaction_task(uvm_phase phase);
      uvma_axi_transaction_c wrsp;

      forever begin
         @(passive_mp.psv_axi_cb);

         // -----------------------------------------------------------------------
         // Collect response on Write response channel
         // -----------------------------------------------------------------------
         if (passive_mp.psv_axi_cb.b_valid && passive_mp.psv_axi_cb.b_ready) begin
            // Creating a new object to send to the scoreboard,
            // and get requests informations into it
            wrsp = new();
            wrsp.m_id            = passive_mp.psv_axi_cb.b_id    ;
            wrsp.m_user          = passive_mp.psv_axi_cb.b_user  ;
            wrsp.m_resp.push_back(uvma_axi_dv_resp_t'(passive_mp.psv_axi_cb.b_resp))  ;
            wrsp.m_trace         = passive_mp.psv_axi_cb.b_trace ;
            wrsp.m_loop          = passive_mp.psv_axi_cb.b_loop  ;
            wrsp.m_idunq         = passive_mp.psv_axi_cb.b_idunq ;

            wrsp.m_txn_type     = UVMA_AXI_WRITE_RSP ;
            wrsp.m_axi_version  = axi_version   ;
            wrsp.m_timestamp_b  = $time         ;
            wrsp.m_timestamp.push_back($time)   ;

            // Print information about the transaction
            `uvm_info( this.name, $sformatf("WRITE_RSP=%0d(d), Info: %0s",m_num_wrsp_pkts, wrsp.convert2string()) , UVM_DEBUG)

            // Send object to the scoreboard
            m_uvma_axi_write_rsp_packets_collected.write(wrsp);

            // Increment the Write response counter
            m_num_wrsp_pkts++;

            fork
               begin
                  int unsigned wrsp_handle;
                  uvma_axi_transaction_c rsp_write;
                  rsp_write = new;
                  $cast(rsp_write, wrsp.clone());
                  wrsp_handle = begin_tr(rsp_write, "WRITE_RSP" );
                  @(passive_mp.psv_axi_cb);
                  end_tr( rsp_write );
               end
            join_none
         end // if
      end // forever
   endtask : receive_B_channel_transaction_task

   // -----------------------------------------------------------------------
   // Task receive read response
   //
   // Collect input response on the uvma_axi interface, on the R channel
   // -----------------------------------------------------------------------
   task receive_R_channel_transaction_task(uvm_phase phase);
      uvma_axi_transaction_c rrsp;
      uvma_axi_transaction_c rdat;
      int flag_last;

      forever begin
         @(passive_mp.psv_axi_cb);

         // -----------------------------------------------------------------------
         // Collect response on Read data channel
         // -----------------------------------------------------------------------
         if (passive_mp.psv_axi_cb.r_valid && passive_mp.psv_axi_cb.r_ready) begin
            // Creating a new object to send to the scoreboard,
            // and get requests informations into it
            rrsp = new() ;
            flag_last = 0 ;

            while ( !flag_last ) begin
               if (passive_mp.psv_axi_cb.r_valid && passive_mp.psv_axi_cb.r_ready) begin
                  // Creating a dummy transaction only to sample it for
                  // the read data covergroup
                  rdat = new();
                  rdat.m_txn_type        = UVMA_AXI_READ_RSP ;
                  rdat.append_read_flit(passive_mp.psv_axi_cb.r_data,
                                        uvma_axi_dv_resp_t'(passive_mp.psv_axi_cb.r_resp),
                                        passive_mp.psv_axi_cb.r_last);

                  // Creating a read response transaction to sample it
                  // and send it to the scoreboard
                  rrsp.m_id         = passive_mp.psv_axi_cb.r_id     ;
                  rrsp.append_read_flit(passive_mp.psv_axi_cb.r_data,
                                        uvma_axi_dv_resp_t'(passive_mp.psv_axi_cb.r_resp),
                                        passive_mp.psv_axi_cb.r_last);
                  rrsp.m_user       = passive_mp.psv_axi_cb.r_user   ;
                  rrsp.m_trace      = passive_mp.psv_axi_cb.r_trace  ;
                  rrsp.m_loop       = passive_mp.psv_axi_cb.r_loop   ;
                  rrsp.m_idunq      = passive_mp.psv_axi_cb.r_idunq  ;
                  rrsp.m_poison     = passive_mp.psv_axi_cb.r_poison ;

                  rrsp.m_txn_type        = UVMA_AXI_READ_RSP ;
                  rrsp.m_axi_version     = axi_version  ;
                  rrsp.m_timestamp.push_back($time)     ;
                  rrsp.m_timestamp_x.push_back($time)   ;

                  // Checking if this flit is the last of the
                  // transaction
                  flag_last = rrsp.m_last[rrsp.m_last.size() - 1] ;
               end
               if ( !flag_last )
                 @(passive_mp.psv_axi_cb);
            end // while

            // Print the information about the transaction
            `uvm_info( this.name, $sformatf("READ_RSP=%0d(d), Info: %0s",m_num_rrsp_pkts, rrsp.convert2string()) , UVM_DEBUG)

            // Send object to the scoreboard
            m_uvma_axi_read_rsp_packets_collected.write(rrsp);

            // Increment the Read response counter
            m_num_rrsp_pkts++;

            fork
               begin
                  int unsigned rrsp_handle;
                  uvma_axi_transaction_c rsp_read;
                  rsp_read = new;
                  $cast(rsp_read, rrsp.clone());
                  rrsp_handle = begin_tr(rsp_read, "READ_RSP" );
                  @(passive_mp.psv_axi_cb);
                  end_tr( rsp_read );
               end
            join_none
         end // if
      end // forever
   endtask : receive_R_channel_transaction_task

   // MASTER MONITOR 
   //
   // -----------------------------------------------------------------------
   // Task receive write requests
   //
   // Collect input write requests on the AW channel of the  uvma_axi interface
   // -----------------------------------------------------------------------
   task synchronize_mst_transaction(uvm_phase phase);
      uvma_axi_transaction_c  req;

      forever begin
         @(mst_mp.clk);

         // Creating a new object to send to the scoreboard,
         // and get requests informations into it
         req = new();
         m_uvma_axi_req_packets_collected.write(req);
      end // forever
   endtask : synchronize_mst_transaction

   // -----------------------------------------------------------------------
   // Task receive write requests
   //
   // Collect input write requests on the AW channel of the  uvma_axi interface
   // -----------------------------------------------------------------------
   task receive_mst_AW_channel_transaction_task(uvm_phase phase);
      uvma_axi_transaction_c  wreq;
      uvma_axi_transaction_c  wreq_atop ;

      forever begin
         @(posedge mst_mp.clk);
         // -----------------------------------------------------------------------
         // Collect request on Write Address and Write data channels
         // -----------------------------------------------------------------------
         if (mst_mp.aw_valid) begin

            aw_hck_status++;
            if (mst_mp.aw_ready) begin

               // Creating a new object to send to the scoreboard,
               // and get requests informations into it
               wreq = new();
               wreq.m_id                       = mst_mp.aw_id                                ;
               wreq.m_addr                     = mst_mp.aw_addr                              ;
               wreq.m_len                      = mst_mp.aw_len                               ;
               wreq.m_size                     = uvma_axi_dv_size_t'(mst_mp.aw_size )             ;
               wreq.m_burst                    = uvma_axi_dv_burst_t'(mst_mp.aw_burst)            ;
               wreq.m_lock                     = uvma_axi_dv_lock_t'(mst_mp.aw_lock )             ;
               wreq.m_cache                    = mst_mp.aw_cache                             ;
               //TODO
               //wreq.m_mem_type                 = get_mem_type(AXI_WRITE_REQ,mst_mp.aw_cache) ;
               wreq.m_prot                     = uvma_axi_dv_prot_t'(mst_mp.aw_prot)              ;
               wreq.m_qos                      = mst_mp.aw_qos                               ;
               wreq.m_region                   = mst_mp.aw_region                            ;
               wreq.m_user                     = mst_mp.aw_user                              ;
               wreq.m_atop                     = mst_mp.aw_atop                              ;
               wreq.m_trace                    = mst_mp.aw_trace                             ;
               wreq.m_loop                     = mst_mp.aw_loop                              ;
               wreq.m_mmusecsid                = mst_mp.aw_mmusecsid                         ;
               wreq.m_mmusid                   = mst_mp.aw_mmusid                            ;
               wreq.m_mmussidv                 = mst_mp.aw_mmussidv                          ;
               wreq.m_mmussid                  = mst_mp.aw_mmussid                           ;
               wreq.m_mmuatst                  = mst_mp.aw_mmuatst                           ;
               wreq.m_nsaid                    = mst_mp.aw_nsaid                             ;
               wreq.m_idunq                    = mst_mp.aw_idunq                             ;
               wreq.ready_delay_cycle_chan_ax  = aw_hck_status                                              ;

               wreq.m_txn_type     = UVMA_AXI_WRITE_ADD_REQ;
               wreq.m_axi_version  = axi_version;
               wreq.m_timestamp_ax = $time;
               wreq.m_timestamp.push_back($time);

               aw_hck_status = -1;

               // Print information about the transaction
               `uvm_info( this.name, $sformatf("WRITE_REQ=%0d(d), Info: %0s",m_num_wreq_pkts, wreq.convert2string()) , UVM_DEBUG)

               // Pushing a dummy read transaction into the protocol checker
               // if a atomic needing an additional read response is
               // detected.
               // This allows to receive the read response in the protocol
               // checker before the entire write transaction (AW + W) is
               // sent
               if ( wreq.m_atop[5] ) begin
                  wreq_atop = new();
                  $cast( wreq_atop, wreq.clone() );
                  if (wreq_atop.m_atop == 49) begin
                     if (wreq_atop.m_len > 0) wreq_atop.m_len = wreq_atop.m_len/2;
                     else wreq_atop.m_size = wreq_atop.m_size/2;
                  end
                  wreq_atop.m_txn_type = UVMA_AXI_READ_REQ ;
                  m_uvma_axi_read_req_packets_collected.write(wreq_atop);
               end

               // Push the write address request into a queue for the
               // combine_write_req_data_task
               m_queue_write_req.push_back(wreq);
               m_uvma_axi_write_add_req_packets_collected.write(wreq);

               // Increment Write Address counter
               m_num_wreq_pkts++;

            end // if
         end // if
      end // forever
   endtask : receive_mst_AW_channel_transaction_task

   // ----------------------------------------------------------------------
   // ask receive write data
   //
   // ollect input write requests on the W channel of the uvma_axi interface
   // ----------------------------------------------------------------------
   task receive_mst_W_channel_transaction_task(uvm_phase phase);
      uvma_axi_transaction_c   wreq_data;

      forever begin
         @(posedge mst_mp.clk);
         // -----------------------------------------------------------------------
         // Collect request on Write Address and Write data channels
         // -----------------------------------------------------------------------
         if (mst_mp.w_valid) begin

            w_hck_status++;
            if (mst_mp.w_ready) begin

               // A new txn arrived, raise the uvm objection until its
               // response comes out
               // phase.raise_objection(this);

               // Creating a new object to send to the scoreboard,
               // and get requests informations into it
               wreq_data = new();

               wreq_data.m_data.push_back( mst_mp.w_data)  ;
               wreq_data.m_wstrb.push_back(mst_mp.w_strb)  ;
               wreq_data.m_last.push_back( mst_mp.w_last)  ;
               wreq_data.m_x_user.push_back(mst_mp.w_user) ;
               wreq_data.m_w_trace      = mst_mp.w_trace   ;
               wreq_data.m_datachk      = mst_mp.w_datachk ;
               wreq_data.m_poison       = mst_mp.w_poison  ;
               wreq_data.m_poison       = mst_mp.w_poison  ;
               wreq_data.ready_delay_cycle_chan_w.push_back(w_hck_status) ;

               wreq_data.m_txn_type     = UVMA_AXI_WRITE_DATA_REQ ;
               wreq_data.m_axi_version  = axi_version   ;
               wreq_data.m_timestamp.push_back($time)   ;

               w_hck_status = -1;

               // Print informations about the transaction
               `uvm_info( this.name, $sformatf("WRITE_DAT=%0d(d), Info: %0s",m_num_wdat_pkts, wreq_data.convert2string()) , UVM_DEBUG)

               // Push the Write data packet into the queue for the
               // combine_write_req_data_task
               m_queue_write_dat.push_back(wreq_data);

               m_uvma_axi_write_data_req_packets_collected.write(wreq_data);

               // Increment the Write data counter
               m_num_wdat_pkts++;

            end // if
         end
      end // forever
   endtask : receive_mst_W_channel_transaction_task

   // -----------------------------------------------------------------------
   // Task combine write req data
   //
   // Collect input write address requests and write data requests on the uvma_axi
   // interface, on the AW and W channels, and combine their data into
   // transaction to send to the scoreboard
   // -----------------------------------------------------------------------
   task combine_mst_write_req_data_task( uvm_phase phase );
      uvma_axi_transaction_c  wreq_addr ;
      uvma_axi_transaction_c  wreq_data ;
      uvma_axi_transaction_c  wreq_txn  ;

      uvma_axi_sig_len_t  req_len;
      int counter_data_pkt = 0   ;
      int counter_txn_pkt  = 0   ;

      forever begin
         wreq_addr = new();

         // Waiting for a new write address request
         wait( m_queue_write_req.size() != 0 );
         `uvm_info( this.name, $sformatf("WRITE address detected") , UVM_DEBUG)
         wreq_addr = m_queue_write_req.pop_front() ;
         $cast( wreq_txn, wreq_addr.clone() );
         wreq_txn.m_txn_type = UVMA_AXI_WRITE_REQ;
         req_len = wreq_txn.m_len ;

         // For each packet of a burst of a write data request, get the
         // data packet transaction from the queue
         for(int i = 0 ; i < wreq_addr.m_len + 1 ; i ++) begin
            wreq_data = new();
            // Waiting for a new write data request
            wait( m_queue_write_dat.size() != 0 );
            `uvm_info( this.name, $sformatf("WRITE data detected") , UVM_DEBUG)
            wreq_data = m_queue_write_dat.pop_front();

            // Creating a new object to send to the scoreboard,
            // and get requests informations into it by combining
            // write address and write data requests informations
            wreq_txn.append_write_flit(wreq_data.m_data[0],
                                       wreq_data.m_wstrb[0],
                                       wreq_data.m_last[0]);
            wreq_txn.m_datachk        = wreq_data.m_datachk      ;
            wreq_txn.m_poison         = wreq_data.m_poison       ;
            wreq_txn.m_timestamp.push_back(wreq_data.m_timestamp[0]) ;

            // Fixing the change of len introduced by the append_write_flit
            // function
            wreq_txn.m_len = req_len ;

            // Print informations about the transaction
            `uvm_info( this.name, $sformatf("WRITE_COMB_DAT=%0d(d), Info: %0s", counter_data_pkt, wreq_txn.convert2string()) , UVM_DEBUG)

            // Increment the Write data counter
            counter_data_pkt++;

         end // for

         // Increment the txn counter
         counter_txn_pkt++;

         `uvm_info( this.name, $sformatf("WRITE_TXN=%0d(d), Info: %0s", counter_txn_pkt, wreq_txn.convert2string()) , UVM_DEBUG)

         // Sending the transaction to the scoreboard
         m_uvma_axi_write_req_packets_collected.write(wreq_txn);

         fork
            begin
                int unsigned wreq_handle;
                uvma_axi_transaction_c req_write;
                req_write = new;
                $cast(req_write, wreq_data.clone());
                wreq_handle = begin_tr(req_write, "WRITE_REQ" );
                @(posedge mst_mp.clk);
                end_tr( req_write );
            end
         join_none

      end // forever
   endtask : combine_mst_write_req_data_task

   // -----------------------------------------------------------------------
   // Task receive read requests
   //
   // Collect input read requests on the uvma_axi interface, on the AR channel
   // -----------------------------------------------------------------------
   task receive_mst_AR_channel_transaction_task(uvm_phase phase);
      uvma_axi_transaction_c rreq;

      forever begin
         @(posedge mst_mp.clk);

         // -----------------------------------------------------------------------
         // Collect request on Read Address channel
         // -----------------------------------------------------------------------
         if (mst_mp.ar_valid) begin
            ar_hck_status++;
            if (mst_mp.ar_ready) begin

               // Creating a new object to send to the scoreboard,
               // and get requests informations into it
               rreq = new() ;
               rreq.m_id                       = mst_mp.ar_id                               ;
               rreq.m_addr                     = mst_mp.ar_addr                             ;
               rreq.m_len                      = mst_mp.ar_len                              ;
               rreq.m_size                     = uvma_axi_dv_size_t'(mst_mp.ar_size)             ;
               rreq.m_burst                    = uvma_axi_dv_burst_t'(mst_mp.ar_burst)           ;
               rreq.m_lock                     = uvma_axi_dv_lock_t'(mst_mp.ar_lock)             ;
               rreq.m_cache                    = mst_mp.ar_cache                            ;
             //rreq.m_mem_type                 = get_mem_type(AXI_READ_REQ,mst_mp.ar_cache) ;
               rreq.m_prot                     = uvma_axi_dv_prot_t'(mst_mp.ar_prot)             ;
               rreq.m_qos                      = mst_mp.ar_qos                              ;
               rreq.m_region                   = mst_mp.ar_region                           ;
               rreq.m_user                     = mst_mp.ar_user                             ;
               rreq.m_trace                    = mst_mp.ar_trace                            ;
               rreq.m_loop                     = mst_mp.ar_loop                             ;
               rreq.m_mmusecsid                = mst_mp.ar_mmusecsid                        ;
               rreq.m_mmusid                   = mst_mp.ar_mmusid                           ;
               rreq.m_mmussidv                 = mst_mp.ar_mmussidv                         ;
               rreq.m_mmussid                  = mst_mp.ar_mmussid                          ;
               rreq.m_mmuatst                  = mst_mp.ar_mmuatst                          ;
               rreq.m_nsaid                    = mst_mp.ar_nsaid                            ;
               rreq.m_idunq                    = mst_mp.ar_idunq                            ;
               rreq.m_idunq                    = mst_mp.ar_idunq                            ;
               rreq.ready_delay_cycle_chan_ax  = ar_hck_status                                             ;
               rreq.m_atop                     = 0                                                         ;
               rreq.m_txn_type     = UVMA_AXI_READ_REQ ;
               rreq.m_axi_version  = axi_version  ;
               rreq.m_timestamp_ax = $time        ;
               rreq.m_timestamp.push_back($time)  ;

               ar_hck_status = -1;

               // Print the information about the transaction
               `uvm_info( this.name, $sformatf("READ_REQ=%0d(d), Info: %0s",m_num_rreq_pkts, rreq.convert2string()) , UVM_DEBUG)
               // Send object to the scoreboard
               m_uvma_axi_read_req_packets_collected.write(rreq);

               // Increment the Read request counter
               m_num_rreq_pkts++;

               fork
                  begin
                     int unsigned rreq_handle;
                     uvma_axi_transaction_c req_read;
                     req_read = new;
                     $cast(req_read, rreq.clone());
                     rreq_handle = begin_tr(req_read, "READ_REQ" );
                     @(posedge mst_mp.clk);
                     end_tr( req_read );
                  end
               join_none
            end // if
         end // if
      end // forever
   endtask : receive_mst_AR_channel_transaction_task

   // -----------------------------------------------------------------------
   // Task receive response
   //
   // Collect input response on the uvma_axi interface, on the B channel
   // -----------------------------------------------------------------------
   task receive_mst_B_channel_transaction_task(uvm_phase phase);
      uvma_axi_transaction_c wrsp;

      forever begin
         @(posedge mst_mp.clk);

         // -----------------------------------------------------------------------
         // Collect response on Write response channel
         // -----------------------------------------------------------------------
         if (mst_mp.b_valid && mst_mp.b_ready) begin
            // Creating a new object to send to the scoreboard,
            // and get requests informations into it
            wrsp = new();
            wrsp.m_id            = mst_mp.b_id    ;
            wrsp.m_user          = mst_mp.b_user  ;
            wrsp.m_resp.push_back(uvma_axi_dv_resp_t'(mst_mp.b_resp))  ;
            wrsp.m_trace         = mst_mp.b_trace ;
            wrsp.m_loop          = mst_mp.b_loop  ;
            wrsp.m_idunq         = mst_mp.b_idunq ;

            wrsp.m_txn_type     = UVMA_AXI_WRITE_RSP ;
            wrsp.m_axi_version  = axi_version   ;
            wrsp.m_timestamp_b  = $time         ;
            wrsp.m_timestamp.push_back($time)   ;

            // Print information about the transaction
            `uvm_info( this.name, $sformatf("WRITE_RSP=%0d(d), Info: %0s",m_num_wrsp_pkts, wrsp.convert2string()) , UVM_DEBUG)

            // Send object to the scoreboard
            m_uvma_axi_write_rsp_packets_collected.write(wrsp);

            // Increment the Write response counter
            m_num_wrsp_pkts++;

            fork
               begin
                  int unsigned wrsp_handle;
                  uvma_axi_transaction_c rsp_write;
                  rsp_write = new;
                  $cast(rsp_write, wrsp.clone());
                  wrsp_handle = begin_tr(rsp_write, "WRITE_RSP" );
                  @(posedge mst_mp.clk);
                  end_tr( rsp_write );
               end
            join_none
         end // if
      end // forever
   endtask : receive_mst_B_channel_transaction_task

   // -----------------------------------------------------------------------
   // Task receive read response
   //
   // Collect input response on the uvma_axi interface, on the R channel
   // -----------------------------------------------------------------------
   task receive_mst_R_channel_transaction_task(uvm_phase phase);
      uvma_axi_transaction_c rrsp;
      uvma_axi_transaction_c rdat;
      int flag_last;

      forever begin
         @(posedge mst_mp.clk);

         // -----------------------------------------------------------------------
         // Collect response on Read data channel
         // -----------------------------------------------------------------------
         if (mst_mp.r_valid && mst_mp.r_ready) begin
            // Creating a new object to send to the scoreboard,
            // and get requests informations into it
            rrsp = new() ;
            flag_last = 0 ;

            while ( !flag_last ) begin
               if (mst_mp.r_valid && mst_mp.r_ready) begin
                  // Creating a dummy transaction only to sample it for
                  // the read data covergroup
                  rdat = new();
                  rdat.m_txn_type        = UVMA_AXI_READ_RSP ;
                  rdat.append_read_flit(mst_mp.r_data,
                                        uvma_axi_dv_resp_t'(mst_mp.r_resp),
                                        mst_mp.r_last);

                  // Creating a read response transaction to sample it
                  // and send it to the scoreboard
                  rrsp.m_id         = mst_mp.r_id     ;
                  rrsp.append_read_flit(mst_mp.r_data,
                                        uvma_axi_dv_resp_t'(mst_mp.r_resp),
                                        mst_mp.r_last);
                  rrsp.m_user       = mst_mp.r_user   ;
                  rrsp.m_trace      = mst_mp.r_trace  ;
                  rrsp.m_loop       = mst_mp.r_loop   ;
                  rrsp.m_idunq      = mst_mp.r_idunq  ;
                  rrsp.m_poison     = mst_mp.r_poison ;

                  rrsp.m_txn_type        = UVMA_AXI_READ_RSP ;
                  rrsp.m_axi_version     = axi_version  ;
                  rrsp.m_timestamp.push_back($time)     ;
                  rrsp.m_timestamp_x.push_back($time)   ;

                  // Checking if this flit is the last of the
                  // transaction
                  flag_last = rrsp.m_last[rrsp.m_last.size() - 1] ;
               end
               if ( !flag_last )
                 @(posedge mst_mp.clk);
            end // while

            // Print the information about the transaction
            `uvm_info( this.name, $sformatf("READ_RSP=%0d(d), Info: %0s",m_num_rrsp_pkts, rrsp.convert2string()) , UVM_DEBUG)

            // Send object to the scoreboard
            m_uvma_axi_read_rsp_packets_collected.write(rrsp);

            // Increment the Read response counter
            m_num_rrsp_pkts++;

            fork
               begin
                  int unsigned rrsp_handle;
                  uvma_axi_transaction_c rsp_read;
                  rsp_read = new;
                  $cast(rsp_read, rrsp.clone());
                  rrsp_handle = begin_tr(rsp_read, "READ_RSP" );
                  @(posedge mst_mp.clk);
                  end_tr( rsp_read );
               end
            join_none
         end // if
      end // forever
   endtask : receive_mst_R_channel_transaction_task

   // -----------------------------------------------------------------------
   // Report Phase
   // -----------------------------------------------------------------------
   virtual function void report_phase(uvm_phase phase);
      `uvm_info($sformatf("%s%s", this.name, "_REPORT_PHASE"),
                $sformatf("REPORT: COLLECTED WRITE REQ PACKETS = %0d", m_num_wreq_pkts),
                UVM_DEBUG)
      `uvm_info($sformatf("%s%s", this.name, "_REPORT_PHASE"),
                $sformatf("REPORT: COLLECTED WRITE DAT PACKETS = %0d", m_num_wdat_pkts),
                UVM_DEBUG)
      `uvm_info($sformatf("%s%s", this.name, "_REPORT_PHASE"),
                $sformatf("REPORT: COLLECTED WRITE RSP PACKETS = %0d", m_num_wrsp_pkts),
                UVM_DEBUG)
      `uvm_info($sformatf("%s%s", this.name, "_REPORT_PHASE"),
                $sformatf("REPORT: COLLECTED READ REQ PACKETS = %0d",  m_num_rreq_pkts),
                UVM_DEBUG)
      `uvm_info($sformatf("%s%s", this.name, "_REPORT_PHASE"),
                $sformatf("REPORT: COLLECTED READ RSP PACKETS = %0d",  m_num_rrsp_pkts),
                UVM_DEBUG)

      if ( m_queue_write_req.size() != 0)
        `uvm_error($sformatf("%s%s", this.name, "_REPORT_PHASE"),
                $sformatf("REPORT: WRITE_REQ_QUEUE NOT EMPTY SIZE=%0d",  m_queue_write_req.size()))
      if ( m_queue_write_dat.size() != 0)
        `uvm_error($sformatf("%s%s", this.name, "_REPORT_PHASE"),
                $sformatf("REPORT: WRITE_DAT_QUEUE NOT EMPTY SIZE=%0d", m_queue_write_dat.size()))

   endfunction: report_phase

endclass : uvma_axi_mon_c
