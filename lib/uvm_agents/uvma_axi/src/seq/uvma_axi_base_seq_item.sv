// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group

`ifndef __UVMA_AXI_BASE_SEQ_ITEM_SV__
`define __UVMA_AXI_BASE_SEQ_ITEM_SV__


/**
 * Object created by Open Bus Interface agent sequences extending uvma_obi_memory_seq_base_c.
 */
class uvma_axi_base_seq_item_c extends uvml_trn_seq_item_c;

   uvma_axi_channel_enum           channel;
   rand logic                      ar_valid;
   rand logic                      ar_ready;
   rand logic                      ar_lock;
   rand logic [AXI_ID_WIDTH-1:0]   ar_id;
   rand logic [AXI_ADDR_WIDTH-1:0] ar_addr;
   rand logic [7:0]                ar_len;
   rand logic [2:0]                ar_size;
   rand logic [1:0]                ar_burst;
   rand logic [1:0]                ar_user;
   int                             ar_latency;

   rand logic [AXI_ID_WIDTH-1:0]   r_id;
   rand logic [AXI_ADDR_WIDTH-1:0] r_data;
   rand logic                      r_last;
   rand logic                      r_valid;
   rand logic [1:0]                r_resp;
   logic                           r_ready;
   rand logic                      r_user;

   rand logic                      aw_valid;
   rand logic                      aw_ready;
   rand logic                      aw_lock;
   rand logic [AXI_ID_WIDTH-1:0]   aw_id;
   rand logic [AXI_ADDR_WIDTH-1:0] aw_addr;
   rand logic [AXI_USER_WIDTH-1:0] aw_user;
   rand logic [7:0]                aw_len;
   rand logic [2:0]                aw_size;
   rand logic [1:0]                aw_burst;
   rand logic [3:0]                aw_cache;
   rand logic [2:0]                aw_prot;
   rand logic [3:0]                aw_qos;
   rand logic [3:0]                aw_region;
   rand logic [5:0]                aw_atop;
   int                             aw_latency;

   rand logic [AXI_DATA_WIDTH-1:0]   w_data;
   rand logic                        w_last;
   rand logic                        w_valid;
   rand logic                        w_ready;
   rand logic [AXI_DATA_WIDTH/8-1:0] w_strb;
   rand logic                        w_user;
   int                               w_latency;

   rand logic [AXI_ID_WIDTH-1:0]   b_id;
   rand logic [1:0]                b_resp;
   rand logic                      b_valid;
   rand logic                      b_ready;
   rand logic [1:0]                b_user;

   // Metadata
   uvma_axi_cfg_c  cfg; ///< Handle to agent's configuration object

    `uvm_object_utils_begin(uvma_axi_base_seq_item_c)
      `uvm_field_int(aw_id, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_addr, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_ready, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_lock, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_len, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_size, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_burst, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_cache, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_user, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_prot, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_qos, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_region, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_atop, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE);

      `uvm_field_int(w_data, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_last, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_ready, UVM_ALL_ON | UVM_NOPACK);
       `uvm_field_int(w_strb, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_user, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE);

      `uvm_field_int(b_id, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(b_resp, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(b_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(b_ready, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(b_user, UVM_ALL_ON | UVM_NOPACK);

      `uvm_field_int(ar_id, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_addr, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_ready, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_lock, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_len, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_size, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_burst, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_user, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE);

      `uvm_field_int(r_id, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_data, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_resp, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_last, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_ready, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_user, UVM_ALL_ON | UVM_NOPACK);
   `uvm_object_utils_end
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_axi_base_seq_item");

endclass : uvma_axi_base_seq_item_c

function uvma_axi_base_seq_item_c::new(string name="uvma_axi_base_seq_item");

   super.new(name);

endfunction : new


`endif // __UVMA_AXI_BASE_SEQ_ITEM_SV__

