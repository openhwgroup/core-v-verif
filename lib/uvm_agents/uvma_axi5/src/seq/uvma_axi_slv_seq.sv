// Copyright 2023 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


//=============================================================================
// Description: Sequence for agent axi_ar
//=============================================================================

`ifndef UVMA_AXI_SLV_SEQ_SV
`define UVMA_AXI_SLV_SEQ_SV

/**
 * Virtual sequence implementing the CVA6 memory iterface virtual peripheral.
 */
class uvma_axi_slv_seq_c extends uvma_axi_base_seq_c;

   uvma_axi_synchronizer_c  synchronizer;

   int ar_seq_status = 0;
   int aw_seq_status = 0;
   int w_seq_status = 0;

   int last_ar_ready_delay = 0;
   int last_aw_ready_delay = 0;
   int last_w_ready_delay = 0;

   `uvm_object_utils_begin(uvma_axi_slv_seq_c)
   `uvm_object_utils_end

   extern function new(string name = "uvma_axi_slv_seq_c");

   /**
    * Assigns synchronizer handles from p_sequencer.
    */
   extern virtual task pre_body();

   /**
    * TODO Describe uvma_axi_slv_base_seq_c::body()
    */
   extern task body();

   /**
    * TODO Describe uvma_axi_slv_seq_c::do_response()
    */
   extern virtual task do_response();

   /**
    * Convenience function to encapsulate the axi request in the synchronizer
    */
   extern virtual task trs_registration(uvma_axi_transaction_c mon_req);

   /**
    * TODO Describe uvma_axi_slv_seq_c::do_mem_operation()
    */
   extern virtual task do_mem_operation(uvma_axi_transaction_c mon_req);

   /**
    * Method to prepare the write response in the B channel
    */
   extern virtual task prepare_w_resp();

   /**
    * Method to prepare the read response in the R channel
    */
   extern virtual task prepare_r_resp();

   /**
    * Method to prepare the read response in the R channel
    */
   extern virtual task prepare_ar_resp();

   /**
    * Method to prepare the read response in the R channel
    */
   extern virtual task prepare_aw_resp();

   /**
    * Method to prepare the read response in the R channel
    */
   extern virtual task prepare_wdata_resp();

endclass : uvma_axi_slv_seq_c


function uvma_axi_slv_seq_c::new(string name = "uvma_axi_slv_seq_c");

   super.new(name);

endfunction : new

task uvma_axi_slv_seq_c::pre_body();

   synchronizer   = p_sequencer.synchronizer;

endtask : pre_body

task uvma_axi_slv_seq_c::body();

   uvma_axi_transaction_c   ar_mon_trn;
   uvma_axi_transaction_c   aw_mon_trn;
   uvma_axi_transaction_c   w_mon_trn;
   uvma_axi_transaction_c   mon_trn;

   ar_mon_trn = uvma_axi_transaction_c::type_id::create("ar_mon_trn");
   aw_mon_trn = uvma_axi_transaction_c::type_id::create("aw_mon_trn");
   w_mon_trn  = uvma_axi_transaction_c::type_id::create("w_mon_trn");
   mon_trn    = uvma_axi_transaction_c::type_id::create("mon_trn");

   // Wait for the monitor to send us the mstr's "req" with an access request
   fork
      begin
         forever begin
            p_sequencer.ar_mon2seq_fifo_port.get(ar_mon_trn);
            do_mem_operation(ar_mon_trn);
         end
      end

      begin
         forever begin
            p_sequencer.aw_mon2seq_fifo_port.get(aw_mon_trn);
            do_mem_operation(aw_mon_trn);
         end
      end

      begin
         forever begin
            p_sequencer.w_mon2seq_fifo_port.get(w_mon_trn);
            do_mem_operation(w_mon_trn);
         end
      end

      begin
         forever begin
            p_sequencer.mon2seq_fifo_port.get(mon_trn);
            do_response();
         end
      end
   join_none

endtask : body

task uvma_axi_slv_seq_c::do_response();

   if(cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET) begin
      prepare_w_resp();
      prepare_r_resp();
      prepare_ar_resp();
      prepare_aw_resp();
      prepare_wdata_resp();
   end else begin
      synchronizer.w_trs_queue.delete();
      synchronizer.r_trs_queue.delete();
      synchronizer.w_trs_item_bp.delete();
      synchronizer.w_trs_class.delete();
      synchronizer.w_finished_trs_id.delete();
      synchronizer.r_finished_trs_id.delete();
      synchronizer.exclusive_r_access.delete();
      synchronizer.exclusive_w_access.delete();

      synchronizer.outstanding_read_call_times  = 0;
      synchronizer.outstanding_write_call_times = 0;

      ar_seq_status = 0;
      aw_seq_status = 0;
      w_seq_status = 0;

      last_ar_ready_delay = 0;
      last_aw_ready_delay = 0;
      last_w_ready_delay = 0;
   end

endtask : do_response

task uvma_axi_slv_seq_c::do_mem_operation(uvma_axi_transaction_c mon_req);

   if(cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET) begin
      `uvm_info(get_type_name(), $sformatf("TRX TYPE = %s", mon_req.m_txn_type), UVM_HIGH)
      trs_registration(mon_req);
   end

endtask : do_mem_operation

task uvma_axi_slv_seq_c::trs_registration(uvma_axi_transaction_c mon_req);

   if(mon_req.m_txn_type == UVMA_AXI_WRITE_ADD_REQ || mon_req.m_txn_type == UVMA_AXI_WRITE_DATA_REQ) begin
      `uvm_info(get_type_name(), $sformatf("Write trx registration "), UVM_HIGH)
      synchronizer.add_w_trs(mon_req);
   end else if(mon_req.m_txn_type == UVMA_AXI_READ_REQ) begin
      `uvm_info(get_type_name(), $sformatf("Read trx registration "), UVM_HIGH)
      synchronizer.add_r_trs(mon_req);
   end

endtask : trs_registration

task uvma_axi_slv_seq_c::prepare_w_resp();

   uvma_axi_transaction_c w_slv_rsp;
   int exc_resp = 0;
   int w_selected_id;

   w_selected_id = synchronizer.w_select_id(synchronizer.w_finished_trs_id);

   if(w_selected_id != -1) begin
      `uvm_create(w_slv_rsp)

      w_slv_rsp = new synchronizer.w_trs_queue[w_selected_id][0];
      `uvm_info(get_type_name(), $sformatf("Write Response Transaction is created"), UVM_HIGH)

      exc_resp = synchronizer.check_exclusive_resp(w_selected_id);
      if(exc_resp == 1) w_slv_rsp.m_resp.push_back(1)   ;
      else w_slv_rsp.m_resp.push_back(0);

      w_slv_rsp.m_id         = w_selected_id;
      w_slv_rsp.m_user       = 0;
      w_slv_rsp.m_txn_type   = UVMA_AXI_WRITE_RSP;

      w_slv_rsp.set_config(cfg.txn_config) ;

      if(!cfg.disable_trs_randomization) begin
         w_slv_rsp.m_id.rand_mode(0);
         w_slv_rsp.m_txn_type.rand_mode(0);
         w_slv_rsp.m_axi_version.rand_mode(0);
         w_slv_rsp.m_lite.rand_mode(0);
         w_slv_rsp.m_err.rand_mode(0);
//         w_slv_rsp.lower_byte_lane.rand_mode(0);
//         w_slv_rsp.upper_byte_lane.rand_mode(0);

         if(!cfg.resp_randomization_enabled) begin
            w_slv_rsp.m_resp.rand_mode(0);
         end
         if(!cfg.user_randomization_enabled) begin
            w_slv_rsp.m_user.rand_mode(0);
         end

         if(!cfg.rand_channel_delay_enabled) begin
            w_slv_rsp.m_delay_cycle_chan_X.rand_mode(0);
            w_slv_rsp.m_delay_cycle_chan_X = 0;
         end

         // Randomization of the transaction
         w_slv_rsp.randomize();
      end else begin
         w_slv_rsp.m_delay_cycle_chan_X = 0;
      end

      `uvm_info(get_type_name(), $sformatf("FINICH WRITE TRANSACTION"), UVM_HIGH)
      synchronizer.write_burst_complete(w_selected_id);

      w_slv_rsp.set_sequencer(p_sequencer);

      `uvm_send(w_slv_rsp)
   end

endtask : prepare_w_resp

task uvma_axi_slv_seq_c::prepare_r_resp();

   uvma_axi_transaction_c r_slv_rsp;
   int r_selected_id = -1;

   synchronizer.r_select_id(synchronizer.r_finished_trs_id, r_selected_id);

   if(r_selected_id != -1) begin
      `uvm_create(r_slv_rsp)

      foreach(synchronizer.r_trs_queue[r_selected_id][i]) begin
         if(synchronizer.r_trs_queue[r_selected_id][i].m_trs_status == WAITING_RESP) begin
            r_slv_rsp = new synchronizer.r_trs_queue[r_selected_id][i];
            break;
         end
      end

      if(r_slv_rsp.m_last[0]) synchronizer.read_burst_complete(r_selected_id);
      else synchronizer.read_data_complete(r_selected_id);

      r_slv_rsp.set_config(cfg.txn_config) ;
      r_slv_rsp.m_txn_type = UVMA_AXI_READ_RSP;

      if(!cfg.disable_trs_randomization) begin
         r_slv_rsp.m_id.rand_mode(0);
         r_slv_rsp.m_txn_type.rand_mode(0);
         r_slv_rsp.m_axi_version.rand_mode(0);
         r_slv_rsp.m_lite.rand_mode(0);
         r_slv_rsp.m_err.rand_mode(0);
//         r_slv_rsp.lower_byte_lane.rand_mode(0);
//         r_slv_rsp.upper_byte_lane.rand_mode(0);
         if(!cfg.resp_randomization_enabled == 1) begin
            r_slv_rsp.m_resp.rand_mode(0);
         end
         if(!cfg.user_randomization_enabled == 1) begin
            r_slv_rsp.m_x_user.rand_mode(0);
         end
         if(!cfg.rand_channel_delay_enabled) begin
            r_slv_rsp.m_delay_cycle_flits.rand_mode(0);
            for(int i = 0; i <= r_slv_rsp.m_len; i++)
               r_slv_rsp.m_delay_cycle_flits.push_back(0);
         end
         r_slv_rsp.m_last.rand_mode(0);
         r_slv_rsp.m_data.rand_mode(0);
         r_slv_rsp.c_last.constraint_mode(0);

	     // Randomization of the transaction
         r_slv_rsp.randomize();
      end else begin
         for(int i = 0; i <= r_slv_rsp.m_len; i++)
            r_slv_rsp.m_delay_cycle_flits.push_back(0);
      end
      r_slv_rsp.set_sequencer(p_sequencer);

      `uvm_send(r_slv_rsp)
   end

endtask : prepare_r_resp


task uvma_axi_slv_seq_c::prepare_ar_resp();
   uvma_axi_transaction_c ar_slv_rsp;
   `uvm_info(get_type_name(), $sformatf("ARREADY Transaction Response Started"), UVM_HIGH)
   if(ar_seq_status == last_ar_ready_delay) begin
      `uvm_create(ar_slv_rsp)

      ar_seq_status = -1;

      ar_slv_rsp.set_config(cfg.txn_config) ;
      ar_slv_rsp.m_txn_type = UVMA_AXI_READ_REQ;
      ar_slv_rsp.m_txn_type.rand_mode(0);

      // Randomization of the transaction
      if(cfg.rand_channel_delay_enabled) ar_slv_rsp.randomize();
      else ar_slv_rsp.ready_delay_cycle_chan_ax = 0;

      ar_slv_rsp.set_sequencer(p_sequencer);
      last_ar_ready_delay = ar_slv_rsp.ready_delay_cycle_chan_ax;

      `uvm_send(ar_slv_rsp)
   end
   ar_seq_status++;

endtask : prepare_ar_resp

task uvma_axi_slv_seq_c::prepare_aw_resp();
   uvma_axi_transaction_c aw_slv_rsp;

   `uvm_info(get_type_name(), $sformatf("AWREADY Transaction Response Started"), UVM_HIGH)
   if(aw_seq_status == last_aw_ready_delay) begin
      `uvm_create(aw_slv_rsp)

      aw_seq_status = -1;

      aw_slv_rsp.set_config(cfg.txn_config) ;
      aw_slv_rsp.m_txn_type = UVMA_AXI_WRITE_ADD_REQ;
      aw_slv_rsp.m_txn_type.rand_mode(0);

      // Randomization of the transaction
      if(cfg.rand_channel_delay_enabled) aw_slv_rsp.randomize();
      else aw_slv_rsp.ready_delay_cycle_chan_ax = 0;

      aw_slv_rsp.set_sequencer(p_sequencer);
      last_aw_ready_delay = aw_slv_rsp.ready_delay_cycle_chan_ax;

      `uvm_send(aw_slv_rsp)
   end
   aw_seq_status++;

endtask : prepare_aw_resp

task uvma_axi_slv_seq_c::prepare_wdata_resp();

   uvma_axi_transaction_c wdata_slv_rsp;
   `uvm_info(get_type_name(), $sformatf("WREADY Transaction Response Started"), UVM_HIGH)
   if(w_seq_status == last_w_ready_delay) begin
      `uvm_create(wdata_slv_rsp)

      w_seq_status = -1;

      wdata_slv_rsp.set_config(cfg.txn_config) ;
      wdata_slv_rsp.m_txn_type = UVMA_AXI_WRITE_DATA_REQ;
      wdata_slv_rsp.m_txn_type.rand_mode(0);

      // Randomization of the transaction
      if(cfg.rand_channel_delay_enabled) wdata_slv_rsp.randomize();
      else wdata_slv_rsp.ready_delay_cycle_chan_w.push_back(0);

      wdata_slv_rsp.set_sequencer(p_sequencer);
      last_w_ready_delay = wdata_slv_rsp.ready_delay_cycle_chan_w[0];

      `uvm_send(wdata_slv_rsp)
   end
   w_seq_status++;

endtask : prepare_wdata_resp

`endif   // __UVMA_AXI_SLV_SEQ_SV

