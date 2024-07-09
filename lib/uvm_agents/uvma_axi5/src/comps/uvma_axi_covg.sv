// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVMA_AXI_COVG_SV__
`define __UVMA_AXI_COVG_SV__

   /*
   * Covergroups
   * Decalred at package-level to enable mutliple instances per monitor class (e.g. read/write)
   */

covergroup cg_write_channel(string name)
   with function sample(uvma_axi_transaction_c item);

   option.per_instance = 1;
   option.name         = name;

   awready_to_valid: coverpoint (item.ready_delay_cycle_chan_ax) {
      bins dly[] = {[0:16]};
   }

   wready_to_valid: coverpoint (item.ready_delay_cycle_chan_w[0]) {
      bins dly[] = {[0:16]};
   }

   awsize: coverpoint item.m_size;

   awlen: coverpoint (item.m_len);

   awburst: coverpoint (item.m_burst) {
      bins FIXE = {0};
      bins INCR = {1};
      bins WRAP = {2};
   }

   awregion: coverpoint item.m_region;

   awprot: coverpoint item.m_prot;

   awlock: coverpoint item.m_lock;

   wstrb: coverpoint item.m_wstrb[0];

   aw_axi_cross: cross awready_to_valid, wready_to_valid, awsize, awlock, awlen, awburst, awregion, awprot {
   ignore_bins IGN_CROSS  = binsof(awlen) intersect{[1:255]} &&  binsof(awsize) intersect{[0:$clog2(MAX_DATA_WIDTH/8)-1]};
   ignore_bins IGN_CROSS2 = binsof(awlen) intersect{[16:255]} &&  binsof(awburst) intersect{0,2};
   }

   aw_axi_strb_cross: cross awready_to_valid, wready_to_valid, wstrb, awlock, awlen, awburst, awregion, awprot {
   ignore_bins IGN_CROSS     = binsof(awlen) intersect{[16:255]} &&  binsof(awburst) intersect{0,2};
   }
endgroup : cg_write_channel

covergroup cg_data_order(string name)
   with function sample(uvma_axi_transaction_c item, int t_aw_to_w, int index);

   option.per_instance = 1;
   option.name         = name;

   request_order: coverpoint (t_aw_to_w < 0){
      bins addr_data = {0};
      bins data_addr = {1};
   }

   ranking: coverpoint (index){
      bins index[] = {[0:15]};
   }

   awlen: coverpoint item.m_len;

   awburst: coverpoint (item.m_burst) {
      bins FIXE = {0};
      bins INCR = {1};
      bins WRAP = {2};
   }

   data_order_cross: cross request_order, ranking, awlen, awburst  {
      ignore_bins IGN_CROSS     = binsof(awlen) intersect{[16:255]} &&  binsof(awburst) intersect{0,2};
   }
endgroup : cg_data_order

covergroup cg_b_response_channel(string name)
   with function sample(uvma_axi_transaction_c item);

   option.per_instance = 1;
   option.name         = name;

   bid:   coverpoint item.m_id;

   bresp: coverpoint (item.m_resp[0]){
      bins zero  = {0};
      bins one   = {1};
      bins two   = {2};
      bins three = {3};
   }

   b_axi_cross: cross bid, bresp;
endgroup : cg_b_response_channel

covergroup cg_read_channel(string name)
   with function sample(uvma_axi_transaction_c item);

   option.per_instance = 1;
   option.name         = name;

   arready_to_valid: coverpoint (item.ready_delay_cycle_chan_ax) {
      bins dly[] = {[0:16]};
   }

   arid: coverpoint item.m_id;

   arlen: coverpoint (item.m_len);

   arsize: coverpoint item.m_size;

   arburst: coverpoint item.m_burst {
      bins FIXE = {0};
      bins INCR = {1};
      bins WRAP = {2};
   }

   arlock: coverpoint item.m_lock;

   arregion: coverpoint item.m_region;

   arprot: coverpoint item.m_prot;

   ar_axi_cross: cross arready_to_valid, arid, arsize, arlen, arburst, arlock, arregion, arprot {
   ignore_bins IGN_CROSS  = binsof(arlen) intersect{[1:255]} &&  binsof(arsize) intersect{[0:$clog2(MAX_DATA_WIDTH/8)-1]};
   ignore_bins IGN_CROSS2 = binsof(arlen) intersect{[16:255]} &&  binsof(arburst) intersect{0,2};
   }

endgroup : cg_read_channel

covergroup cg_r_response_channel(string name)
   with function sample(uvma_axi_transaction_c item, int index);

   option.per_instance = 1;
   option.name         = name;

   rid: coverpoint item.m_id;

   rlast: coverpoint item.m_last[index];

   rresp: coverpoint (item.m_resp[index]){
      bins zero  = {0};
      bins one   = {1};
      bins two   = {2};
      bins three = {3};
   }

   r_axi_cross: cross rid, rlast, rresp;
endgroup : cg_r_response_channel

/**
 * Component encapsulating Open Bus Interface functional coverage model.
 */
class uvma_axi_covg_c extends uvm_component;

   // TLM
   uvm_tlm_analysis_fifo #(uvma_axi_transaction_c)    uvma_axi_cov_aw_req_fifo;
   uvm_tlm_analysis_fifo #(uvma_axi_transaction_c)    uvma_axi_cov_b_resp_fifo;
   uvm_tlm_analysis_fifo #(uvma_axi_transaction_c)    uvma_axi_cov_ar_req_fifo;
   uvm_tlm_analysis_fifo #(uvma_axi_transaction_c)    uvma_axi_cov_r_resp_fifo;

   // Covergroup instances
   cg_write_channel        w_axi_cg;
   cg_data_order           order_axi_cg;
   cg_b_response_channel   b_axi_cg;
   cg_read_channel         ar_axi_cg;
   cg_r_response_channel   r_axi_cg;

   int t_aw_to_w;

   `uvm_component_utils_begin(uvma_axi_covg_c)
   `uvm_component_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_axi_covg", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds fifos.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Forks all sampling loops
    */
   extern virtual task run_phase(uvm_phase phase);

endclass : uvma_axi_covg_c


function uvma_axi_covg_c::new(string name="uvma_axi_covg", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


// A significant chunk of the build_phase method is common between this
// coverage model and the sequencer (uvma_obi_memory_sqr).  This is
// appropriate so the duplicated code has a lint waiver.
//
function void uvma_axi_covg_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   uvma_axi_cov_b_resp_fifo  = new("uvma_axi_cov_b_resp_fifo"   , this);
   uvma_axi_cov_r_resp_fifo  = new("uvma_axi_cov_r_resp_fifo"   , this);
   uvma_axi_cov_ar_req_fifo  = new("uvma_axi_cov_ar_req_fifo"   , this);
   uvma_axi_cov_aw_req_fifo  = new("uvma_axi_cov_aw_req_fifo"   , this);

   w_axi_cg     = new("w_axi_cg");
   order_axi_cg = new("order_axi_cg");
   b_axi_cg     = new("b_axi_cg");
   ar_axi_cg    = new("ar_axi_cg");
   r_axi_cg     = new("r_axi_cg");

endfunction : build_phase

task uvma_axi_covg_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   forever begin
      uvma_axi_transaction_c  aw_item;
      uvma_axi_transaction_c  b_item;
      uvma_axi_transaction_c  ar_item;
      uvma_axi_transaction_c  r_item;

      fork
         uvma_axi_cov_b_resp_fifo.get(aw_item);
         uvma_axi_cov_r_resp_fifo.get(b_item);
         uvma_axi_cov_ar_req_fifo.get(ar_item);
         uvma_axi_cov_aw_req_fifo.get(r_item);
      join_any

      if(aw_item != null) begin
         `uvm_info(get_type_name(), $sformatf("WRITE REQ ITEM DETECTED"), UVM_HIGH)
         w_axi_cg.sample(aw_item);
         for(int i = 1; i <= aw_item.m_len; i++) begin
            t_aw_to_w = aw_item.m_timestamp_x[i] - aw_item.m_timestamp_ax;
            order_axi_cg.sample(aw_item, t_aw_to_w, i);
         end
      end

      if(b_item != null) begin
          `uvm_info(get_type_name(), $sformatf("WRITE RESP ITEM DETECTED"), UVM_HIGH)
          b_axi_cg.sample(b_item);
      end

      if(ar_item != null) begin
         `uvm_info(get_type_name(), $sformatf("READ ADDRESS ITEM DETECTED"), UVM_HIGH)
         ar_axi_cg.sample(ar_item);
      end

      if(r_item != null) begin
         `uvm_info(get_type_name(), $sformatf("READ DATA ITEM DETECTED"), UVM_HIGH)
         for(int i = 0; i <= r_item.m_len; i++) begin
            r_axi_cg.sample(r_item, i);
         end
      end
   end

endtask : run_phase

`endif // __UVMA_AXI_COVG_SV__
