// Copyright 2023 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVMA_AXI_SYNCHRONIZER_SV__
`define __UVMA_AXI_SYNCHRONIZER_SV__

/**
 * Component that prepares the request for sequences to facilitate response generation.
 */
class uvma_axi_synchronizer_c extends uvm_component;

   `uvm_component_utils(uvma_axi_synchronizer_c)

   //Object
   uvma_axi_cntxt_c  cntxt;
   uvma_axi_cfg_c    cfg;

   // Sequence items queue
   static uvma_axi_slv_seq_item_c w_trs_queue[int][$];
   static uvma_axi_slv_seq_item_c r_trs_queue[int][$];
   static uvma_axi_base_seq_item_c w_trs_item_bp[$];

   // Handles to the monitor ports
   uvm_analysis_port #(uvma_axi_transaction_c)       uvma_sqr_trs_port;

   // Exclusive transactions queue
   static uvma_axi_slv_seq_item_c exclusive_r_access[int][int];
   static uvma_axi_slv_seq_item_c exclusive_w_access[int][int];

   // Queue of finished transactions
   static int w_finished_trs_id[$];
   static int r_finished_trs_id[$];

   // Items that encapsulate all the transfers of a transaction to send it to other component outside the agent
   static uvma_axi_transaction_c axi_r_transaction;
   static uvma_axi_transaction_c axi_w_transaction;

   static int w_trs_class[$];

   static int w_trs_id[int][$];

   static longint read_trs_id  = 0;
   static longint write_trs_id = 0;

   static int access_w_trs[][];
   static int access_r_trs[][];


   /**
    * Default constructor.
    */
   extern function new(string name = "uvma_axi_synchronizer_c", uvm_component parent);

   /**
    * 1. Ensures cntxt handles are not null
    * 2. Builds all components
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * 1. Add transaction to w_trs_queue
    * 2. Change the state of the transaction for each transfer
    */
   extern virtual function void add_w_trs(uvma_axi_base_seq_item_c axi_item);

   /**
    * 1. Add transaction to r_trs_queue
    * 2. Change the state of the transaction for each transfer
    */
   extern virtual function void add_r_trs(uvma_axi_base_seq_item_c axi_item);

   /**
    * List all write transfer that is ready to write in the memory
    */
   extern virtual function void write_data();

   /**
    * change the state of transaction for each read response
    */
   extern virtual function void read_data_complete(int selected_id, uvma_axi_slv_seq_item_c slv_resp);

   /**
    * 1. prepare a transaction to send it to other component
    * 2. Delete the completed transactions the transaction from r queue
    */
   extern virtual function void read_burst_complete(int selected_id, uvma_axi_slv_seq_item_c slv_resp);

   /**
    * 1. prepare a transaction to send it to other component
    * 2. Delete the completed transactions the transaction from w queue
    */
   extern virtual function void write_burst_complete(int selected_id, uvma_axi_slv_seq_item_c slv_resp);

   /**
    * Return the b_resp of an exclusive write access
    */
   extern virtual function int check_exclusive_resp(int selected_id);

   /**
    * Standard method to select the ID from a table according to fifo
    */
   extern virtual function int select_id(int tab[]);

   /**
    * Standard method to select the Write ID from a table
    */
   extern virtual function int w_select_id(int tab[]);

   /**
    * Standard method to select the READ ID from a table
    */
   extern virtual function int r_select_id(int tab[]);

   /**
   * check the memory access permission
   */
   extern virtual function int check_memory_access(uvma_axi_base_seq_item_c item, uvma_axi_access_type_enum type_access);

endclass : uvma_axi_synchronizer_c


function uvma_axi_synchronizer_c::new(string name = "uvma_axi_synchronizer_c", uvm_component parent);

      super.new(name, parent);

endfunction

function void uvma_axi_synchronizer_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   axi_r_transaction = uvma_axi_transaction_c::type_id::create("axi_r_transaction");

   this.uvma_sqr_trs_port   = new("uvma_sqr_trs_port", this);

   void'(uvm_config_db#(uvma_axi_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_fatal("build_phase", "monitor cntxt class failed")
      end

   void'(uvm_config_db#(uvma_axi_cfg_c)::get(this, "", "cfg", cfg));
      if (cfg == null) begin
         `uvm_fatal("build_phase", "monitor cfg class failed")
      end

endfunction

function void uvma_axi_synchronizer_c::add_w_trs(uvma_axi_base_seq_item_c axi_item);

   uvma_axi_base_seq_item_c  last_w_req;
   uvma_axi_slv_seq_item_c   slv_rsp;
   int size;
   int i = w_trs_queue[axi_item.aw_id].size();
   longint addr, Aligned_Address, Lower_Wrap_Boundary, Upper_Wrap_Boundary;
   int Number_Bytes, dtsize;
   bit aligned;

   last_w_req = uvma_axi_base_seq_item_c::type_id::create("last_w_req");
   slv_rsp    = uvma_axi_slv_seq_item_c::type_id::create("slv_rsp");

   if(axi_item.aw_valid && axi_item.aw_ready) begin

      if(access_w_trs.size() <= axi_item.aw_id) begin
         access_w_trs = new [axi_item.aw_id +1] (access_w_trs);
         access_w_trs[axi_item.aw_id] = new[1];
         access_w_trs[axi_item.aw_id][0] = 1;
      end else begin
         access_w_trs[axi_item.aw_id] = new[access_w_trs[axi_item.aw_id].size()+1] (access_w_trs[axi_item.aw_id]);
         access_w_trs[axi_item.aw_id][access_w_trs[axi_item.aw_id].size()-1] = 1;
      end

      size = w_trs_queue[axi_item.aw_id].size();
      addr = axi_item.aw_addr; // Variable for current address
      Number_Bytes = 2**axi_item.aw_size;
      Aligned_Address = (int'(addr/Number_Bytes) * Number_Bytes);
      aligned = (Aligned_Address == addr); // Check whether addr is aligned to nbytes
      dtsize = Number_Bytes * axi_item.aw_len; // Maximum total data transaction size
      write_trs_id++;
      axi_item.write_trs_id = write_trs_id;
      if (axi_item.aw_burst == 2) begin
         Lower_Wrap_Boundary = (int'(addr/dtsize) * dtsize);
         // addr must be aligned for a wrapping burst
         Upper_Wrap_Boundary = Lower_Wrap_Boundary + dtsize;
      end

      for(int i=0; i < axi_item.aw_len+1; i++) begin

         axi_item.Aw_Lower_Byte_Lane = addr - (int'(addr/(AXI_ADDR_WIDTH/8))) * (AXI_ADDR_WIDTH/8);
         if (aligned)
            axi_item.Aw_Upper_Byte_Lane = axi_item.Aw_Lower_Byte_Lane + Number_Bytes - 1;
         else
            axi_item.Aw_Upper_Byte_Lane = Aligned_Address + Number_Bytes - 1 - (int'(addr/(AXI_ADDR_WIDTH/8))) * (AXI_ADDR_WIDTH/8);

         axi_item.aw_addr =  addr - addr%(AXI_ADDR_WIDTH/8);
         slv_rsp.mon_req = new axi_item;
         w_trs_queue[axi_item.aw_id][w_trs_queue[axi_item.aw_id].size()] = new slv_rsp;
         w_trs_queue[axi_item.aw_id][size + i].mon_req.w_trs_status = ADDR_DATA_NOT_COMPLETE;

         // Increment address if necessary
         if (axi_item.aw_burst != 0) begin
            if (aligned) begin

               addr = addr + Number_Bytes;
               if (axi_item.aw_burst == 2 && addr >= Upper_Wrap_Boundary) addr = Lower_Wrap_Boundary;

            end else begin

               addr = Aligned_Address + Number_Bytes;
               aligned = 1; // All transfers after the first are aligned

            end
         end
      end
      w_trs_class.push_back(axi_item.aw_id);

      if(w_trs_item_bp.size() > 0) begin
         do begin

            w_trs_queue[axi_item.aw_id][i].mon_req.w_valid      = w_trs_item_bp[0].w_valid;
            w_trs_queue[axi_item.aw_id][i].mon_req.w_data       = w_trs_item_bp[0].w_data;
            w_trs_queue[axi_item.aw_id][i].mon_req.w_strb       = w_trs_item_bp[0].w_strb;
            w_trs_queue[axi_item.aw_id][i].mon_req.w_last       = w_trs_item_bp[0].w_last;
            w_trs_queue[axi_item.aw_id][i].mon_req.w_user       = w_trs_item_bp[0].w_user;
            w_trs_queue[axi_item.aw_id][i].mon_req.w_latency    = w_trs_item_bp[0].w_latency;
            w_trs_queue[axi_item.aw_id][i].mon_req.w_start_time = w_trs_item_bp[0].w_start_time;
            w_trs_queue[axi_item.aw_id][i].mon_req.w_trs_status = ADDR_DATA_COMPLETE;
            last_w_req = new w_trs_item_bp[0];
            w_trs_item_bp.delete(0);
            i++;

         end while(w_trs_item_bp.size() > 0 && !last_w_req.w_last);

         if(last_w_req.w_last == 1) begin
            w_finished_trs_id.push_back(w_trs_queue[axi_item.aw_id][i-1].mon_req.aw_id);
            w_trs_id[w_trs_queue[axi_item.aw_id][i-1].mon_req.aw_id].push_back(axi_item.write_trs_id);
            w_trs_class.delete(0);
         end
      end
   end

   if(axi_item.w_valid && axi_item.w_ready) begin
      if(w_trs_queue.size() > 0 && w_trs_queue[w_trs_class[0]].size() > 0) begin

         `uvm_info( "Core Test", $sformatf("NEW W_TRS"), UVM_HIGH)
         foreach(w_trs_queue[w_trs_class[0]][i]) begin
            if(w_trs_queue[w_trs_class[0]][i].mon_req.w_trs_status == ADDR_DATA_NOT_COMPLETE) begin

               w_trs_queue[w_trs_class[0]][i].mon_req.w_valid      = axi_item.w_valid;
               w_trs_queue[w_trs_class[0]][i].mon_req.w_data       = axi_item.w_data;
               w_trs_queue[w_trs_class[0]][i].mon_req.w_strb       = axi_item.w_strb;
               w_trs_queue[w_trs_class[0]][i].mon_req.w_last       = axi_item.w_last;
               w_trs_queue[w_trs_class[0]][i].mon_req.w_user       = axi_item.w_user;
               w_trs_queue[w_trs_class[0]][i].mon_req.w_latency    = axi_item.w_latency;
               w_trs_queue[w_trs_class[0]][i].mon_req.w_start_time = axi_item.w_start_time;
               w_trs_queue[w_trs_class[0]][i].mon_req.w_trs_status = ADDR_DATA_COMPLETE;
               if(axi_item.w_last) begin
                  w_finished_trs_id.push_back(w_trs_class[0]);
                  w_trs_class.delete(0);
                  w_trs_id[axi_item.aw_id].push_back(axi_item.write_trs_id);
               end
               break;

            end
         end
      end else begin

         w_trs_item_bp.push_back(axi_item);
      end
   end
   write_data();

endfunction : add_w_trs

function void uvma_axi_synchronizer_c::add_r_trs(uvma_axi_base_seq_item_c axi_item);

   uvma_axi_slv_seq_item_c slv_rsp;
   longint addr, Aligned_Address, Lower_Wrap_Boundary, Upper_Wrap_Boundary;
   int Number_Bytes, dtsize;
   bit aligned;
   slv_rsp = uvma_axi_slv_seq_item_c::type_id::create("slv_rsp");

   read_trs_id++;
   axi_item.read_trs_id = read_trs_id;

   if(access_r_trs.size() <= axi_item.ar_id) begin
      access_r_trs = new [axi_item.ar_id +1] (access_r_trs);
      access_r_trs[axi_item.ar_id] = new[1];
      access_r_trs[axi_item.ar_id][0] = 1;
   end else begin
      access_r_trs[axi_item.ar_id] = new[access_r_trs[axi_item.ar_id].size()+1] (access_r_trs[axi_item.ar_id]);
      access_r_trs[axi_item.ar_id][access_r_trs[axi_item.ar_id].size()-1] = 1;
   end
   addr = axi_item.ar_addr; // Variable for current address
   Number_Bytes = 2**axi_item.ar_size;
   Aligned_Address = (int'(addr/Number_Bytes) * Number_Bytes);
   aligned = (Aligned_Address == addr); // Check whether addr is aligned to nbytes
   dtsize = Number_Bytes * axi_item.ar_len; // Maximum total data transaction size
   if (axi_item.ar_burst == 2) begin
      Lower_Wrap_Boundary = (int'(addr/dtsize) * dtsize);
      // addr must be aligned for a wrapping burst
      Upper_Wrap_Boundary = Lower_Wrap_Boundary + dtsize;
   end
   for(int i=0; i < axi_item.ar_len+1; i++) begin

      axi_item.Ar_Lower_Byte_Lane = addr - (int'(addr/(AXI_ADDR_WIDTH/8))) * (AXI_ADDR_WIDTH/8);
      if (aligned)
         axi_item.Ar_Upper_Byte_Lane = axi_item.Ar_Lower_Byte_Lane + Number_Bytes - 1;
      else
         axi_item.Ar_Upper_Byte_Lane = Aligned_Address + Number_Bytes - 1 - (int'(addr/(AXI_ADDR_WIDTH/8))) * (AXI_ADDR_WIDTH/8);

      axi_item.ar_addr =  addr - addr%(AXI_ADDR_WIDTH/8);
      if(i == axi_item.ar_len) begin
         axi_item.r_trs_status = LAST_READ_DATA;
      end else begin
         axi_item.r_trs_status = READ_DATA_NOT_COMPLETE;
      end

      slv_rsp.mon_req = new axi_item;
      r_trs_queue[axi_item.ar_id][r_trs_queue[axi_item.ar_id].size()] = new slv_rsp;

      // Increment address if necessary
      if (axi_item.ar_burst != 0) begin
         if (aligned) begin
            addr = addr + Number_Bytes;
            if (axi_item.ar_burst == 2 && addr >= Upper_Wrap_Boundary) addr = Lower_Wrap_Boundary;
         end else begin
            addr = Aligned_Address + Number_Bytes;
            aligned = 1; // All transfers after the first are aligned
         end
      end
   end
   r_finished_trs_id.push_back(axi_item.ar_id);

endfunction : add_r_trs

function void uvma_axi_synchronizer_c::write_data();

   longint exclusive_data;
   longint original_data;
   uvma_axi_slv_seq_item_c ex_r_data;
   int last_trs = -1;
   int checkexclusive;
   uvma_axi_access_type_enum acc_type = UVMA_AXI_ACCESS_WRITE;

   ex_r_data = uvma_axi_slv_seq_item_c::type_id::create("ex_r_data");

   foreach(w_trs_queue[i]) begin
      for(int j = 0; j < w_trs_queue[i].size(); j++) begin
         if(w_trs_queue[i][j].mon_req.w_trs_status == ADDR_DATA_COMPLETE) begin

            `uvm_info(get_type_name(), $sformatf("write request ready with id = %d", w_trs_queue[i][j].mon_req.aw_id), UVM_HIGH)
            if(w_trs_queue[i][j].mon_req.aw_lock == 1 && cfg.axi_lock_enabled) begin

               `uvm_info(get_type_name(), $sformatf("EXCLUSIVE ACCESS"), UVM_HIGH)

               exclusive_w_access[w_trs_queue[i][j].mon_req.aw_id][exclusive_w_access[w_trs_queue[i][j].mon_req.aw_id].size()] = new w_trs_queue[i][j];
               for(int k = w_trs_queue[i][j].mon_req.Aw_Lower_Byte_Lane; k <= w_trs_queue[i][j].mon_req.Aw_Upper_Byte_Lane; k++) begin
                  exclusive_data[((k+1)*8-1)-:8] = cntxt.mem.read(w_trs_queue[i][j].mon_req.aw_addr + k);
               end

               foreach(exclusive_r_access[w_trs_queue[i][j].mon_req.aw_id][k]) begin
                  ex_r_data = new exclusive_r_access[w_trs_queue[i][j].mon_req.aw_id][k];
                  if(ex_r_data.mon_req.ar_addr == w_trs_queue[i][j].mon_req.aw_addr && ex_r_data.mon_req.Ar_Lower_Byte_Lane == w_trs_queue[i][j].mon_req.Aw_Lower_Byte_Lane && ex_r_data.mon_req.Ar_Upper_Byte_Lane == w_trs_queue[i][j].mon_req.Aw_Upper_Byte_Lane) begin
                     original_data = ex_r_data.r_data;
                     last_trs = k;
                     `uvm_info(get_type_name(), $sformatf("find first match trs req"), UVM_HIGH)
                     break;
                  end
               end
               checkexclusive = 1;

               for(int k = w_trs_queue[i][j].mon_req.Aw_Lower_Byte_Lane; k <= w_trs_queue[i][j].mon_req.Aw_Upper_Byte_Lane; k++) begin
                  `uvm_info(get_type_name(), $sformatf("DATA CHECK ITERATION = %d", k), UVM_HIGH)
                  if(exclusive_data[((k+1)*8-1)-:8] != original_data[((k+1)*8-1)-:8]) begin
                     checkexclusive = 0;
                     `uvm_info(get_type_name(), $sformatf("Data in the request addr not match exclusive read data (exclusive_data = %h et  original_data = %h", exclusive_data[((k+1)*8-1)-:8], original_data[((k+1)*8-1)-:8]), UVM_HIGH)
                     break;
                  end
               end

               if(last_trs == -1) begin
                  checkexclusive = -1;
               end

               if(checkexclusive == 1) begin
                  exclusive_w_access[w_trs_queue[i][j].mon_req.aw_id][exclusive_w_access[w_trs_queue[i][j].mon_req.aw_id].size()-1].b_resp = 1;
                  foreach(exclusive_r_access[w_trs_queue[i][j].mon_req.aw_id][k]) begin
                     if(k >= last_trs && last_trs != -1 && k < (exclusive_r_access[w_trs_queue[i][j].mon_req.aw_id].size()-1)) begin
                        exclusive_r_access[w_trs_queue[i][j].mon_req.aw_id][k] =  exclusive_r_access[w_trs_queue[i][j].mon_req.aw_id][k+1];
                     end
                  end
                  exclusive_r_access[w_trs_queue[i][j].mon_req.aw_id].delete(exclusive_r_access[w_trs_queue[i][j].mon_req.aw_id].size()-1);
               end else begin
                  exclusive_w_access[w_trs_queue[i][j].mon_req.aw_id][exclusive_w_access[w_trs_queue[i][j].mon_req.aw_id].size()-1].b_resp = 0;
               end
               last_trs = -1;
            end else begin
               `uvm_info(get_type_name(), $sformatf("NORMAL ACCESS"), UVM_HIGH)
               checkexclusive = 1;
            end

            if(check_memory_access(w_trs_queue[i][j].mon_req, acc_type) == 1) begin

               if(checkexclusive == 1) begin
                  for(int k = w_trs_queue[i][j].mon_req.Aw_Lower_Byte_Lane; k <= w_trs_queue[i][j].mon_req.Aw_Upper_Byte_Lane; k++) begin
                      if(w_trs_queue[i][j].mon_req.w_strb[k]) cntxt.mem.write(w_trs_queue[i][j].mon_req.aw_addr + k, w_trs_queue[i][j].mon_req.w_data[((k+1)*8-1)-:8]);
                  end
               end else if(checkexclusive == 0) begin
                  `uvm_error(get_full_name(), "The memory location has been modified by another master");
               end else begin
                  `uvm_error(get_full_name(), "We cannot find any read exclusive access with the same parameters");
               end
            end else if(check_memory_access(w_trs_queue[i][j].mon_req, acc_type) == 0) begin
               `uvm_info(get_type_name(), " No need to write data in this memory location", UVM_LOW)
            end else begin
               `uvm_error(get_full_name(), "YOU CAN NOT WRITE DATA IN THIS ADDRESS LOCATION")
            end
            w_trs_queue[i][j].mon_req.w_trs_status = WAITING_RESP;

         end
      end
   end

endfunction : write_data


function void uvma_axi_synchronizer_c::write_burst_complete(int selected_id, uvma_axi_slv_seq_item_c slv_resp);

   uvma_axi_base_seq_item_c mon_req;
   uvma_axi_slv_seq_item_c slv_exc_resp;
   int j = -1;

   mon_req      = uvma_axi_base_seq_item_c::type_id::create("mon_req");
   slv_exc_resp = uvma_axi_slv_seq_item_c::type_id::create("slv_exc_resp");

   access_w_trs[selected_id] = new[access_w_trs[selected_id].size()-1] (access_w_trs[selected_id]);

   foreach(w_trs_queue[selected_id][i]) begin
      if(w_trs_queue[selected_id][i].mon_req.w_last) begin
         w_trs_queue[selected_id][i].b_id         = slv_resp.b_id;
         w_trs_queue[selected_id][i].b_valid      = slv_resp.b_valid;
         w_trs_queue[selected_id][i].b_resp       = slv_resp.b_resp;
         w_trs_queue[selected_id][i].b_user       = slv_resp.b_user;
         w_trs_queue[selected_id][i].b_start_time = $time;
         break;
      end
   end

   axi_w_transaction = uvma_axi_transaction_c::type_id::create("axi_w_transaction");

   axi_w_transaction.access_type   = UVMA_AXI_ACCESS_WRITE;
   axi_w_transaction.aw_lock       = w_trs_queue[selected_id][0].mon_req.aw_lock;
   axi_w_transaction.aw_id         = w_trs_queue[selected_id][0].mon_req.aw_id;
   axi_w_transaction.aw_addr       = w_trs_queue[selected_id][0].mon_req.aw_addr;
   axi_w_transaction.aw_len        = w_trs_queue[selected_id][0].mon_req.aw_len;
   axi_w_transaction.aw_size       = w_trs_queue[selected_id][0].mon_req.aw_size;
   axi_w_transaction.aw_burst      = w_trs_queue[selected_id][0].mon_req.aw_burst;
   axi_w_transaction.aw_cache      = w_trs_queue[selected_id][0].mon_req.aw_cache;
   axi_w_transaction.aw_atop       = w_trs_queue[selected_id][0].mon_req.aw_atop;
   axi_w_transaction.aw_delay      = w_trs_queue[selected_id][0].mon_req.aw_latency;
   axi_w_transaction.aw_start_time = w_trs_queue[selected_id][0].mon_req.aw_start_time;

   do begin
      j++;
      axi_w_transaction.w_data_trs[j].w_data       = w_trs_queue[selected_id][j].mon_req.w_data;
      axi_w_transaction.w_data_trs[j].w_last       = w_trs_queue[selected_id][j].mon_req.w_last;
      axi_w_transaction.w_data_trs[j].w_strb       = w_trs_queue[selected_id][j].mon_req.w_strb;
      axi_w_transaction.w_data_trs[j].w_delay      = w_trs_queue[selected_id][j].mon_req.w_latency;
      axi_w_transaction.w_data_trs[j].w_start_time = w_trs_queue[selected_id][j].mon_req.w_start_time;
   end while(!w_trs_queue[selected_id][j].mon_req.w_last);

   axi_w_transaction.b_id         = w_trs_queue[selected_id][j].b_id;
   axi_w_transaction.b_resp       = w_trs_queue[selected_id][j].b_resp;
   axi_w_transaction.b_start_time = w_trs_queue[selected_id][j].b_start_time;

   uvma_sqr_trs_port.write(axi_w_transaction);

   if(check_exclusive_resp(selected_id) == 1 || check_exclusive_resp(selected_id) == 0) begin
      `uvm_info(get_type_name(), $sformatf("Finish exclusive transaction"), UVM_HIGH)
      do begin
         slv_exc_resp = new exclusive_w_access[selected_id][0];
         exclusive_w_access[selected_id].delete(0);
      end while(!slv_exc_resp.mon_req.w_last);
   end

   foreach(w_finished_trs_id[i]) begin
      if(w_finished_trs_id[i] == selected_id) begin
         w_finished_trs_id.delete(i);
         break;
      end
   end

   do begin
      mon_req = new w_trs_queue[selected_id][0].mon_req;
      void'(w_trs_queue[selected_id].pop_front());
   end while(!mon_req.w_last);

endfunction : write_burst_complete


function void uvma_axi_synchronizer_c::read_data_complete(int selected_id, uvma_axi_slv_seq_item_c slv_resp);

   int size;

   foreach(r_trs_queue[selected_id][i]) begin
      if(r_trs_queue[selected_id][i].mon_req.r_trs_status == READ_DATA_NOT_COMPLETE) begin

         r_trs_queue[selected_id][i].mon_req.r_trs_status = READ_DATA_COMPLETE;
         r_trs_queue[selected_id][i].r_id         = slv_resp.r_id;
         r_trs_queue[selected_id][i].r_data       = slv_resp.r_data;
         r_trs_queue[selected_id][i].r_last       = slv_resp.r_last;
         r_trs_queue[selected_id][i].r_valid      = slv_resp.r_valid;
         r_trs_queue[selected_id][i].r_resp       = slv_resp.r_resp;
         r_trs_queue[selected_id][i].r_user       = slv_resp.r_user;
         r_trs_queue[selected_id][i].r_start_time = $time;
         if(r_trs_queue[selected_id][i].mon_req.ar_lock) begin
            if(exclusive_r_access[slv_resp.r_id].size() > 0) begin
               if(exclusive_r_access[slv_resp.r_id][exclusive_r_access[slv_resp.r_id].size() - 1].r_last == 1) begin
                  exclusive_r_access[slv_resp.r_id].delete();
                  exclusive_r_access[slv_resp.r_id][exclusive_r_access[slv_resp.r_id].size()] = new r_trs_queue[selected_id][i];
               end else begin
                  exclusive_r_access[slv_resp.r_id][exclusive_r_access[slv_resp.r_id].size()] = new r_trs_queue[selected_id][i];
               end
            end else begin
               exclusive_r_access[slv_resp.r_id][exclusive_r_access[slv_resp.r_id].size()] = new r_trs_queue[selected_id][i];
            end
            `uvm_info( "uvma_axi_synchronizer_c", $sformatf("add exclyusive read trs with id = %d", slv_resp.r_id), UVM_HIGH)
         end
         break;

      end
   end

endfunction : read_data_complete

function void uvma_axi_synchronizer_c::read_burst_complete(int selected_id, uvma_axi_slv_seq_item_c slv_resp);

   int j = -1;
   int size;
   int lenght;

   access_r_trs[selected_id] = new[access_r_trs[selected_id].size()-1] (access_r_trs[selected_id]);

   foreach(r_trs_queue[selected_id][i]) begin
      if(r_trs_queue[selected_id][i].mon_req.r_trs_status == LAST_READ_DATA) begin

         r_trs_queue[selected_id][i].r_id         = slv_resp.r_id;
         r_trs_queue[selected_id][i].r_data       = slv_resp.r_data;
         r_trs_queue[selected_id][i].r_last       = slv_resp.r_last;
         r_trs_queue[selected_id][i].r_valid      = slv_resp.r_valid;
         r_trs_queue[selected_id][i].r_resp       = slv_resp.r_resp;
         r_trs_queue[selected_id][i].r_user       = slv_resp.r_user;
         r_trs_queue[selected_id][i].r_start_time = $time;
         if(r_trs_queue[selected_id][i].mon_req.ar_lock) begin
            if(exclusive_r_access[slv_resp.r_id].size() > 0) begin
               if(exclusive_r_access[slv_resp.r_id][exclusive_r_access[slv_resp.r_id].size() - 1].r_last == 1) begin
                  exclusive_r_access[slv_resp.r_id].delete();
                  exclusive_r_access[slv_resp.r_id][exclusive_r_access[slv_resp.r_id].size()] = new r_trs_queue[selected_id][i];
               end else begin
                  exclusive_r_access[slv_resp.r_id][exclusive_r_access[slv_resp.r_id].size()] = new r_trs_queue[selected_id][i];
               end
            end
            else begin
               exclusive_r_access[slv_resp.r_id][exclusive_r_access[slv_resp.r_id].size()] = new r_trs_queue[selected_id][i];
            end
            `uvm_info( "uvma_axi_synchronizer_c", $sformatf("add exclyusive read trs with id = %d", slv_resp.r_id), UVM_HIGH)
         end
         break;

      end
   end

   axi_r_transaction = uvma_axi_transaction_c::type_id::create("axi_r_transaction");

   axi_r_transaction.access_type   = UVMA_AXI_ACCESS_READ;
   axi_r_transaction.ar_lock       = r_trs_queue[selected_id][0].mon_req.ar_lock;
   axi_r_transaction.ar_id         = r_trs_queue[selected_id][0].mon_req.ar_id;
   axi_r_transaction.ar_addr       = r_trs_queue[selected_id][0].mon_req.ar_addr;
   axi_r_transaction.ar_len        = r_trs_queue[selected_id][0].mon_req.ar_len;
   axi_r_transaction.ar_size       = r_trs_queue[selected_id][0].mon_req.ar_size;
   axi_r_transaction.ar_burst      = r_trs_queue[selected_id][0].mon_req.ar_burst;
   axi_r_transaction.ar_delay      = r_trs_queue[selected_id][0].mon_req.ar_latency;
   axi_r_transaction.ar_start_time = r_trs_queue[selected_id][0].mon_req.ar_start_time;

   do begin
      j++;
      size = axi_r_transaction.r_data_trs.size();
      axi_r_transaction.r_data_trs[size].r_data       = r_trs_queue[selected_id][j].r_data;
      axi_r_transaction.r_data_trs[size].r_last       = r_trs_queue[selected_id][j].r_last;
      axi_r_transaction.r_data_trs[size].r_id         = r_trs_queue[selected_id][j].r_id;
      axi_r_transaction.r_data_trs[size].r_resp       = r_trs_queue[selected_id][j].r_resp;
      axi_r_transaction.r_data_trs[size].r_start_time = r_trs_queue[selected_id][j].r_start_time;
   end while(!r_trs_queue[selected_id][j].r_last);

   uvma_sqr_trs_port.write(axi_r_transaction);

   lenght = r_trs_queue[selected_id][0].mon_req.ar_len;
   for(int i = 0; i <= lenght; i++) begin
      r_trs_queue[selected_id].delete(0);
   end

   foreach(r_finished_trs_id[i]) begin
      if(r_finished_trs_id[i] == selected_id) begin
         r_finished_trs_id.delete(i);
         break;
      end
   end

endfunction : read_burst_complete


function int uvma_axi_synchronizer_c::check_exclusive_resp(int selected_id);
   int exc_resp = -1;

   if(w_trs_queue[selected_id][0].mon_req.aw_lock == 1) begin

      exc_resp = 1;
      foreach(exclusive_w_access[selected_id][i]) begin
         if(exclusive_w_access[selected_id][i].b_resp != 1) begin
            exc_resp = 0;
            `uvm_info(get_type_name(), $sformatf("Find resp don't match"), UVM_HIGH)
            break;
         end
         if(exclusive_w_access[selected_id][i].mon_req.w_last) begin
            break;
         end
      end

   end
   return exc_resp;

endfunction : check_exclusive_resp

function int uvma_axi_synchronizer_c::select_id(int tab[]);

   int id;
   if(tab.size() > 0) begin
      id = tab[0];
   end else begin
      id = -1;
   end
   return id;

endfunction : select_id

function int uvma_axi_synchronizer_c::w_select_id(int tab[]);

   return select_id(tab);

endfunction : w_select_id

function int uvma_axi_synchronizer_c::r_select_id(int tab[]);

   return select_id(tab);

endfunction : r_select_id

function int uvma_axi_synchronizer_c::check_memory_access(uvma_axi_base_seq_item_c item, uvma_axi_access_type_enum type_access);

   int access = 1;

   //TODO: check the memory region attribute for each access to a memory location
   case (type_access)

      UVMA_AXI_ACCESS_WRITE: begin
         foreach(access_w_trs[i]) begin
            if(i == item.aw_id) begin
               access = access_w_trs[i][0];
               break;
            end
         end
      end

      UVMA_AXI_ACCESS_READ: begin
         foreach(access_r_trs[i]) begin
            if(i == item.ar_id) begin
               access = access_r_trs[i][0];
               break;
            end
         end
      end

   endcase

   return access;

endfunction : check_memory_access

`endif //__UVMA_AXI_SYNCHRONIZER_SV__
