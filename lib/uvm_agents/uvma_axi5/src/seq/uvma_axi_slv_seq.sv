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
class uvma_axi_slv_seq_c extends uvma_axi_slv_base_seq_c;


   uvma_axi_slv_seq_item_c r_slv_resp;
   uvma_axi_slv_seq_item_c w_slv_resp;

   uvma_axi_slv_seq_item_c slv_rsp;
   uvma_axi_slv_seq_item_c slv_rsp_bp;

   int w_selected_id = -1;
   int r_selected_id = -1;

   int w_rand_status = 0;
   int r_rand_status = 0;

   int r_done = 1;
   int w_done = 1;

   `uvm_object_utils_begin(uvma_axi_slv_seq_c)
   `uvm_object_utils_end

   extern function new(string name = "uvma_axi_slv_seq_c");

   /**
    * Main sequence body
    */
   extern virtual task body();

   /**
    * TODO Describe uvma_axi_slv_seq_c::do_response()
    */
   extern virtual task do_response(ref uvma_axi_base_seq_item_c mon_req);

   /**
    * TODO Describe uvma_axi_slv_seq_c::do_mem_operation()
    */
   extern virtual task do_mem_operation(ref uvma_axi_base_seq_item_c mon_req);

   /**
    * TODO Describe uvma_axi_slv_seq_c::do_mem_operation()
    */
   extern virtual task do_axi_operation(ref  uvma_axi_base_seq_item_c mon_req);

   /**
    * Method to prepare the write response in the B channel
    */
   extern virtual function void prepare_w_resp(ref uvma_axi_slv_seq_item_c slv_resp);

   /**
    * Method to prepare the read response in the R channel
    */
   extern virtual function void prepare_r_resp(ref uvma_axi_slv_seq_item_c slv_resp);

endclass : uvma_axi_slv_seq_c


function uvma_axi_slv_seq_c::new(string name = "uvma_axi_slv_seq_c");
   super.new(name);

   r_slv_resp = uvma_axi_slv_seq_item_c::type_id::create("r_slv_resp");
   w_slv_resp = uvma_axi_slv_seq_item_c::type_id::create("w_slv_resp");
   slv_rsp    = uvma_axi_slv_seq_item_c::type_id::create("slv_rsp");
   slv_rsp_bp = uvma_axi_slv_seq_item_c::type_id::create("slv_rsp_bp");

endfunction : new

task uvma_axi_slv_seq_c::body();

   uvma_axi_base_seq_item_c  mon_trn;
   `uvm_info(get_full_name(), $sformatf("Started AXI slave sequence"), UVM_HIGH)
   forever begin
      // Wait for the monitor to send us the mstr's "req" with an access request
      p_sequencer.mon_req_fifo.get(mon_trn);
      do_response(mon_trn);
   end

endtask : body

task uvma_axi_slv_seq_c::do_response(ref uvma_axi_base_seq_item_c mon_req);

   if(cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET) begin
      if (mon_req.is_pure()) begin
         do_mem_operation(mon_req);
      end
      else begin
         do_axi_operation(mon_req);
      end
   end else begin

      w_selected_id = -1;
      r_selected_id = -1;

      w_rand_status = 0;
      r_rand_status = 0;

      synchronizer.w_trs_queue.delete();
      synchronizer.r_trs_queue.delete();
      synchronizer.w_trs_item_bp.delete();
      synchronizer.w_trs_class.delete();
      synchronizer.w_trs_id.delete();

      synchronizer.w_finished_trs_id.delete();
      synchronizer.r_finished_trs_id.delete();

      synchronizer.exclusive_r_access.delete();
      synchronizer.exclusive_w_access.delete();

   end

endtask : do_response

task uvma_axi_slv_seq_c::do_mem_operation(ref uvma_axi_base_seq_item_c mon_req);

   `uvm_create(slv_rsp)
   slv_rsp.mon_req = new mon_req;

   trs_registration(slv_rsp.mon_req);
   prepare_w_resp(slv_rsp);
   prepare_r_resp(slv_rsp);
   slv_rsp.ar_ready.rand_mode(0);
   slv_rsp.aw_ready.rand_mode(0);
   slv_rsp.w_ready.rand_mode(0);

   slv_rsp.randomize();

   //TODO : slv_rsp_bp.r_copy(slv_rsp);
   //slv_rsp_bp.do_copy(slv_rsp);

   slv_rsp_bp.r_id    = slv_rsp.r_id;
   slv_rsp_bp.r_data  = slv_rsp.r_data;
   slv_rsp_bp.r_last  = slv_rsp.r_last;
   slv_rsp_bp.r_valid = slv_rsp.r_valid;
   slv_rsp_bp.r_resp  = slv_rsp.r_resp;
   slv_rsp_bp.r_user  = slv_rsp.r_user;
   slv_rsp_bp.r_resp_status  = slv_rsp.r_resp_status;

   slv_rsp_bp.b_id    = slv_rsp.b_id;
   slv_rsp_bp.b_valid = slv_rsp.b_valid;
   slv_rsp_bp.b_resp  = slv_rsp.b_resp;
   slv_rsp_bp.b_user  = slv_rsp.b_user;
   slv_rsp_bp.b_resp_status  = slv_rsp.b_resp_status;

   slv_rsp.set_sequencer(p_sequencer);

   `uvm_send(slv_rsp)

endtask : do_mem_operation

function void uvma_axi_slv_seq_c::prepare_w_resp(ref uvma_axi_slv_seq_item_c slv_resp);

   int exc_resp = 0;
   if(slv_rsp_bp.b_resp_status == UVMA_AXI_RESP_WAITING_HANDSHAKE) begin
      if(slv_resp.mon_req.b_ready) begin

         w_done = 1;
         `uvm_info(get_type_name(), $sformatf("size of w_finished_trs_id = %d  ||  selected id = %d", synchronizer.w_finished_trs_id.size(), w_selected_id), UVM_HIGH)
         synchronizer.write_burst_complete(w_selected_id, slv_rsp_bp);
         w_selected_id = synchronizer.w_select_id(synchronizer.w_finished_trs_id);
         w_rand_status = 0;

      end else begin

         slv_resp.b_id    = slv_rsp_bp.b_id;
         slv_resp.b_valid = slv_rsp_bp.b_valid;
         slv_resp.b_resp  = slv_rsp_bp.b_resp;
         slv_resp.b_user  = slv_rsp_bp.b_user;
         slv_resp.b_resp_status  = slv_rsp_bp.b_resp_status;

      end
   end else begin

      `uvm_info(get_type_name(), $sformatf("NEW trs"), UVM_HIGH)
      w_selected_id = synchronizer.w_select_id(synchronizer.w_finished_trs_id);

   end
   if(w_selected_id != -1 && w_done == 1) begin

      w_done = 0;
      `uvm_info(get_type_name(), $sformatf("Write Transaction response is created"), UVM_HIGH)
      exc_resp = synchronizer.check_exclusive_resp(w_selected_id);
      if(exc_resp == 1) w_slv_resp.b_resp  = 1;
      else if(exc_resp == 0) w_slv_resp.b_resp  = 0;
      else w_slv_resp.b_resp  = 0;

      w_slv_resp.b_valid      = 1;
      w_slv_resp.b_id         = w_selected_id;
      w_slv_resp.b_user       = 0;
      w_slv_resp.write_trs_id = synchronizer.w_trs_id[w_selected_id].pop_front();

      // TODO : copy
      if(w_rand_status == 1) begin
         slv_resp.b_resp  = slv_rsp_bp.b_resp;
         slv_resp.b_user  = slv_rsp_bp.b_user;
      end else begin
         slv_resp.b_resp  = w_slv_resp.b_resp;
         slv_resp.b_user  = w_slv_resp.b_user;
      end
      slv_resp.b_valid = w_slv_resp.b_valid;
      slv_resp.b_id    = w_slv_resp.b_id;
      slv_resp.write_trs_id = w_slv_resp.write_trs_id;
      slv_resp.b_resp_status = UVMA_AXI_RESP_WAITING_HANDSHAKE;

      slv_resp.b_valid.rand_mode(0);
      slv_resp.b_id.rand_mode(0);
      if(w_rand_status == 0 && cfg.randomization_enabled == 1) begin
         slv_resp.b_resp.rand_mode(1);
         slv_resp.b_user.rand_mode(1);
      end else begin
         slv_resp.b_resp.rand_mode(0);
         slv_resp.b_user.rand_mode(0);
      end
      slv_resp.b_channel_constraint.constraint_mode(0);
      w_rand_status = 1;

   end else if(w_selected_id == -1 && w_done == 1) begin

      slv_resp.b_valid.rand_mode(1);
      slv_resp.b_id.rand_mode(1);
      slv_resp.b_resp.rand_mode(1);
      slv_resp.b_user.rand_mode(1);
      slv_resp.b_resp_status = UVMA_AXI_RESP_WAITING_DATA;
      slv_resp.b_channel_constraint.constraint_mode(1);
      w_rand_status= 0;

   end else begin
      slv_resp.b_valid.rand_mode(0);
      slv_resp.b_id.rand_mode(0);
      slv_resp.b_resp.rand_mode(0);
      slv_resp.b_user.rand_mode(0);
      slv_resp.b_channel_constraint.constraint_mode(0);
   end

endfunction : prepare_w_resp

function void uvma_axi_slv_seq_c::prepare_r_resp(ref uvma_axi_slv_seq_item_c slv_resp);

   uvma_axi_access_type_enum acc_type = UVMA_AXI_ACCESS_READ;
   if(slv_rsp_bp.r_resp_status == UVMA_AXI_RESP_WAITING_HANDSHAKE) begin
      if(slv_resp.mon_req.r_ready) begin

         r_done = 1;
         if(r_slv_resp.mon_req.r_trs_status == LAST_READ_DATA) begin
            `uvm_info(get_type_name(), $sformatf("Read burst complete"), UVM_HIGH)
            synchronizer.read_burst_complete(r_selected_id, slv_rsp_bp);
         end else begin
            synchronizer.read_data_complete(r_selected_id, slv_rsp_bp);
            `uvm_info(get_type_name(), $sformatf("Read data complete"), UVM_HIGH)
         end
         r_selected_id = synchronizer.r_select_id(synchronizer.r_finished_trs_id);
         r_rand_status = 0;

      end else begin

         slv_resp.r_id    = slv_rsp_bp.r_id;
         slv_resp.r_data  = slv_rsp_bp.r_data;
         slv_resp.r_last  = slv_rsp_bp.r_last;
         slv_resp.r_valid = slv_rsp_bp.r_valid;
         slv_resp.r_resp  = slv_rsp_bp.r_resp;
         slv_resp.r_user  = slv_rsp_bp.r_user;
         slv_resp.r_resp_status  = slv_rsp_bp.r_resp_status;

      end
   end else begin

      `uvm_info(get_type_name(), $sformatf("NEW trs"), UVM_HIGH)
      r_selected_id = synchronizer.r_select_id(synchronizer.r_finished_trs_id);

   end

   if(r_selected_id != -1 && r_done == 1) begin
      r_done = 0;
      //TODO : Use find method
      foreach(synchronizer.r_trs_queue[r_selected_id][i]) begin
         if(synchronizer.r_trs_queue[r_selected_id][i].mon_req.r_trs_status == READ_DATA_NOT_COMPLETE || synchronizer.r_trs_queue[r_selected_id][i].mon_req.r_trs_status == LAST_READ_DATA) begin
            r_slv_resp = new synchronizer.r_trs_queue[r_selected_id][i];
            break;
         end
      end
      if(synchronizer.check_memory_access(r_slv_resp.mon_req, acc_type)) begin
         // TODO : add constraint to randomize r_data
         for(int i = r_slv_resp.mon_req.Ar_Lower_Byte_Lane; i <= r_slv_resp.mon_req.Ar_Upper_Byte_Lane; i++) begin
            r_slv_resp.r_data [((i+1)*8-1)-:8]   = cntxt.mem.read(r_slv_resp.mon_req.ar_addr + i);
            //[(i*8)+:7]
         end
         for(int i = 0; i < r_slv_resp.mon_req.Ar_Lower_Byte_Lane; i++) begin
            r_slv_resp.r_data[((i+1)*8-1)-:8] = $urandom();
         end
         for(int i = r_slv_resp.mon_req.Ar_Upper_Byte_Lane+1; i < (AXI_ADDR_WIDTH/8); i++) begin
            r_slv_resp.r_data[((i+1)*8-1)-:8] = $urandom();
         end
      end else if(synchronizer.check_memory_access(r_slv_resp.mon_req, acc_type) == 0) begin
         `uvm_info(get_type_name(), " No need to read data from this memory location", UVM_LOW)
      end else begin
         `uvm_error(get_type_name(), "YOU CAN NOT READ DATA FROM THIS ADDRESS LOCATION")
      end

      if(r_slv_resp.mon_req.ar_lock && cfg.axi_lock_enabled) r_slv_resp.r_resp  = 1;
      else r_slv_resp.r_resp  = 0;

      r_slv_resp.r_user  = 0;

      //TODO: r_copy
      slv_resp.r_id          = r_slv_resp.mon_req.ar_id;
      slv_resp.r_data        = r_slv_resp.r_data;
      slv_resp.r_valid       = 1;
      slv_resp.read_trs_id   = r_slv_resp.mon_req.read_trs_id;
      slv_resp.r_resp_status = UVMA_AXI_RESP_WAITING_HANDSHAKE;
      if(r_rand_status == 1) begin
         slv_resp.r_resp  = slv_rsp_bp.r_resp;
         slv_resp.r_user  = slv_rsp_bp.r_user;
      end else begin
         slv_resp.r_resp  = r_slv_resp.r_resp;
         slv_resp.r_user  = r_slv_resp.r_user;
      end

      if(r_slv_resp.mon_req.r_trs_status == LAST_READ_DATA) begin
         slv_resp.r_last  = 1;
      end else begin
         slv_resp.r_last  = 0;
      end

      slv_resp.r_valid.rand_mode(0);
      slv_resp.r_id.rand_mode(0);
      if(r_rand_status == 0 && cfg.randomization_enabled == 1) begin
         slv_resp.r_resp.rand_mode(1);
         slv_resp.r_user.rand_mode(1);
      end else begin
         slv_resp.r_resp.rand_mode(0);
         slv_resp.r_user.rand_mode(0);
      end
      slv_resp.r_last.rand_mode(0);
      slv_resp.r_data.rand_mode(0);
      slv_resp.r_channel_constraint.constraint_mode(0);
      r_rand_status = 1;

   end else if(r_selected_id == -1 && r_done == 1) begin

      slv_resp.r_valid.rand_mode(1);
      slv_resp.r_id.rand_mode(1);
      slv_resp.r_resp.rand_mode(1);
      slv_resp.r_user.rand_mode(1);
      slv_resp.r_last.rand_mode(1);
      slv_resp.r_data.rand_mode(1);
      slv_resp.r_resp_status = UVMA_AXI_RESP_WAITING_DATA;
      slv_resp.r_channel_constraint.constraint_mode(1);
      r_rand_status = 0;

   end else begin

      slv_resp.r_data.rand_mode(0);
      slv_resp.r_id.rand_mode(0);
      slv_resp.r_last.rand_mode(0);
      slv_resp.r_user.rand_mode(0);
      slv_resp.r_resp.rand_mode(0);
      slv_resp.r_valid.rand_mode(0);
      slv_resp.r_channel_constraint.constraint_mode(0);

   end

endfunction : prepare_r_resp

task uvma_axi_slv_seq_c::do_axi_operation(ref uvma_axi_base_seq_item_c mon_req);

  /////

endtask : do_axi_operation

`endif   // __UVMA_AXI_SLV_SEQ_SV

