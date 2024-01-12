// Copyright 2023 Thales DIS SAS
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
 * Object created by AXI agent monitor extending uvma_axi_seq_base_c.
 */
class uvma_axi_base_seq_item_c extends uvml_trn_seq_item_c;

   int                        Aw_Lower_Byte_Lane;
   int                        Aw_Upper_Byte_Lane;

   int                        Ar_Lower_Byte_Lane;
   int                        Ar_Upper_Byte_Lane;

   uvma_axi_valid_l_t         ar_valid;
   uvma_axi_ready_l_t         ar_ready;
   uvma_axi_lock_l_t          ar_lock;
   uvma_axi_id_l_t            ar_id;
   uvma_axi_addr_l_t          ar_addr;
   uvma_axi_len_l_t           ar_len;
   uvma_axi_size_l_t          ar_size;
   uvma_axi_burst_l_t         ar_burst;
   uvma_axi_user_l_t          ar_user;
   uvma_axi_cache_l_t         ar_cache;
   int                        ar_latency;
   uvma_axi_region_l_t        ar_region;
   uvma_axi_prot_l_t          ar_prot;
   uvma_axi_qos_l_t           ar_qos;
   longint                    ar_start_time;

   uvma_axi_ready_l_t         r_ready;
   uvma_axi_r_trs_status_t    r_trs_status;

   uvma_axi_valid_l_t         aw_valid;
   uvma_axi_ready_l_t         aw_ready;
   uvma_axi_lock_l_t          aw_lock;
   uvma_axi_id_l_t            aw_id;
   uvma_axi_addr_l_t          aw_addr;
   uvma_axi_user_l_t          aw_user;
   uvma_axi_len_l_t           aw_len;
   uvma_axi_size_l_t          aw_size;
   uvma_axi_burst_l_t         aw_burst;
   uvma_axi_cache_l_t         aw_cache;
   uvma_axi_prot_l_t          aw_prot;
   uvma_axi_qos_l_t           aw_qos;
   uvma_axi_region_l_t        aw_region;
   uvma_axi_atop_l_t          aw_atop;
   int                        aw_latency;
   longint                    aw_start_time;
   logic                      aw_exclusive_access;

   uvma_axi_data_l_t          w_data;
   uvma_axi_last_l_t          w_last;
   uvma_axi_valid_l_t         w_valid;
   uvma_axi_ready_l_t         w_ready;
   uvma_axi_strb_l_t          w_strb;
   uvma_axi_user_l_t          w_user;
   int                        w_latency;
   uvma_axi_w_trs_status_t    w_trs_status;
   longint                    w_start_time;

   uvma_axi_ready_l_t         b_ready;


   longint read_trs_id  = 0;
   longint write_trs_id = 0;

    `uvm_object_utils_begin(uvma_axi_base_seq_item_c)
      `uvm_field_int(aw_id, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_addr, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_valid, UVM_ALL_ON | UVM_NOPACK);
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
      `uvm_field_int(w_strb, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_user, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE);

      `uvm_field_int(b_ready, UVM_ALL_ON | UVM_NOPACK);

      `uvm_field_int(ar_id, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_addr, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_lock, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_len, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_size, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_burst, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_user, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE);

      `uvm_field_int(r_ready, UVM_ALL_ON | UVM_NOPACK);
   `uvm_object_utils_end
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_axi_base_seq_item");

   extern virtual function bit is_pure();

endclass : uvma_axi_base_seq_item_c

function uvma_axi_base_seq_item_c::new(string name="uvma_axi_base_seq_item");

   super.new(name);

endfunction : new

function bit uvma_axi_base_seq_item_c::is_pure();

   bit ispure = 1;

   return ispure;

endfunction : is_pure

`endif // __UVMA_AXI_BASE_SEQ_ITEM_SV__

