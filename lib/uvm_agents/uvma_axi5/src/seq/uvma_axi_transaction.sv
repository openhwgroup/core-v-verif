// Copyright 2023 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVMA_AXI_TRANSACTION_SV__
`define __UVMA_AXI_TRANSACTION_SV__


/**
 * Object created by AXI agent synchronizer extending uvml_trn_seq_item_c.
 */
class uvma_axi_transaction_c extends uvml_trn_seq_item_c;

   uvma_axi_access_type_enum  access_type;

   uvma_axi_lock_l_t          aw_lock;
   uvma_axi_id_l_t            aw_id;
   uvma_axi_addr_l_t          aw_addr;
   uvma_axi_len_l_t           aw_len;
   uvma_axi_size_l_t          aw_size;
   uvma_axi_burst_l_t         aw_burst;
   uvma_axi_cache_l_t         aw_cache;
   uvma_axi_atop_l_t          aw_atop;
   int                        aw_delay;
   longint                    aw_start_time;

   uvma_axi_w_data_trs_st     w_data_trs[int];

   uvma_axi_id_l_t            b_id;
   rand uvma_axi_resp_l_t     b_resp;
   longint                    b_start_time;

   uvma_axi_lock_l_t          ar_lock;
   uvma_axi_id_l_t            ar_id;
   uvma_axi_addr_l_t          ar_addr;
   uvma_axi_len_l_t           ar_len;
   uvma_axi_size_l_t          ar_size;
   uvma_axi_burst_l_t         ar_burst;
   int                        ar_delay;
   longint                    ar_start_time;

   uvma_axi_r_data_trs_st     r_data_trs[int];

   `uvm_object_utils_begin(uvma_axi_transaction_c)
     `uvm_field_int(aw_id, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(aw_addr, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(aw_lock, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(aw_len, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(aw_size, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(aw_burst, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(aw_atop, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(aw_delay, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(aw_start_time, UVM_ALL_ON | UVM_NOPACK);

     `uvm_field_int(ar_id, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(ar_addr, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(ar_lock, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(ar_len, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(ar_size, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(ar_burst, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(ar_delay, UVM_ALL_ON | UVM_NOPACK);
     `uvm_field_int(ar_start_time, UVM_ALL_ON | UVM_NOPACK);
   `uvm_object_utils_end
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_axi_transaction");

endclass : uvma_axi_transaction_c

function uvma_axi_transaction_c::new(string name="uvma_axi_transaction");

   super.new(name);

endfunction : new

`endif // __UVMA_AXI_TRANSACTION_SV__

