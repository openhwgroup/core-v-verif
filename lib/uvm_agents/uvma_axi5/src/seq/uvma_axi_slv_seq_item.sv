// Copyright 2023 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVMA_AXI_SLV_SEQ_ITEM_SV__
`define __UVMA_AXI_SLV_SEQ_ITEM_SV__


/**
 * Object created by AXI agent sequences extending uvml_trn_seq_item_c.
 */
class uvma_axi_slv_seq_item_c extends uvml_trn_seq_item_c;

   rand uvma_axi_ready_l_t  ar_ready;
   rand int                 ar_delay;

   rand uvma_axi_id_l_t     r_id;
   rand uvma_axi_data_l_t   r_data;
   rand uvma_axi_last_l_t   r_last;
   rand uvma_axi_valid_l_t  r_valid;
   rand uvma_axi_resp_l_t   r_resp;
   rand uvma_axi_user_l_t   r_user;
   longint                  r_start_time;

   uvma_axi_slv_handshake_resp_status   r_resp_status;

   rand uvma_axi_ready_l_t  aw_ready;
   rand int                 aw_delay;

   rand uvma_axi_ready_l_t  w_ready;
   rand int                 w_delay;

   rand uvma_axi_id_l_t     b_id;
   rand uvma_axi_resp_l_t   b_resp;
   rand uvma_axi_valid_l_t  b_valid;
   rand uvma_axi_user_l_t   b_user;
   longint                  b_start_time;

   uvma_axi_slv_handshake_resp_status   b_resp_status;

   uvma_axi_base_seq_item_c mon_req;

   longint read_trs_id  = 0;
   longint write_trs_id = 0;

    `uvm_object_utils_begin(uvma_axi_slv_seq_item_c)
      `uvm_field_int(aw_ready, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_delay, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE);

      `uvm_field_int(w_ready, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_delay, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE);

      `uvm_field_int(b_id, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(b_resp, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(b_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(b_user, UVM_ALL_ON | UVM_NOPACK);

      `uvm_field_int(ar_ready, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_delay, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE);

      `uvm_field_int(r_id, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_data, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_resp, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_last, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_user, UVM_ALL_ON | UVM_NOPACK);

      `uvm_field_object(mon_req, UVM_DEFAULT + UVM_NOCOMPARE)
   `uvm_object_utils_end


   constraint aw_channel_constraint {
      aw_delay   inside {[0:16]};
   }

   constraint w_channel_constraint {
      w_delay   inside {[0:16]};
   }

   constraint b_channel_constraint {
      b_resp   inside {[0:3]};
      b_valid == 0;
   }

   constraint ar_channel_constraint {
      ar_delay   inside {[0:16]};
   }

   constraint r_channel_constraint {
      r_last   dist { 0 := 1, 1 := 9};
      r_resp   inside {[0:3]};
      r_valid == 0;
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_axi_slv_seq_item_c");

endclass : uvma_axi_slv_seq_item_c

function uvma_axi_slv_seq_item_c::new(string name="uvma_axi_slv_seq_item_c");

   super.new(name);

   mon_req = new;

endfunction : new


`endif // __UVMA_AXI_SLV_SEQ_ITEM_SV__

