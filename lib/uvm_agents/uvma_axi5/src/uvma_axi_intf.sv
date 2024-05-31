// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group
// Co-Author: Abdelaali Khardazi

/**** AXI4 interface with parametrized :  ****/

interface uvma_axi_intf (
   input bit clk,
   input bit rst_n
   );

   import uvma_axi_pkg::*;

   uvma_axi_dv_ver_t axi_version ;

   // AXI4 signals
   // Write Address channel
   uvma_axi_sig_id_t          aw_id;
   uvma_axi_sig_addr_t        aw_addr;
   uvma_axi_sig_user_t        aw_user;
   uvma_axi_sig_len_t         aw_len;
   uvma_axi_sig_size_t        aw_size;
   uvma_axi_sig_burst_t       aw_burst;
   uvma_axi_sig_lock_t        aw_lock;
   uvma_axi_sig_cache_t       aw_cache;
   uvma_axi_sig_prot_t        aw_prot;
   uvma_axi_sig_qos_t         aw_qos;
   uvma_axi_sig_region_t      aw_region;
   logic                      aw_valid;
   logic                      aw_ready;
   uvma_axi_sig_atop_t        aw_atop;
   logic                      aw_trace;
   uvma_axi_sig_loop_t        aw_loop;
   logic                      aw_mmusecsid;
   uvma_axi_sig_mmusid_t      aw_mmusid;
   logic                      aw_mmussidv;
   uvma_axi_sig_mmussid_t     aw_mmussid;
   logic                      aw_mmuatst;
   uvma_axi_sig_nsaid_t       aw_nsaid;
   logic                      aw_idunq;

   //write data channel
   uvma_axi_sig_data_t        w_data;
   uvma_axi_sig_wstrb_t       w_strb;
   uvma_axi_sig_user_t        w_user;
   logic                      w_last;
   uvma_axi_sig_datachk_t     w_datachk;
   uvma_axi_sig_poison_t      w_poison;
   logic                      w_trace;
   logic                      w_valid;
   logic                      w_ready;

   // write response channel
   uvma_axi_sig_id_t          b_id;
   uvma_axi_sig_user_t        b_user;
   uvma_axi_sig_resp_t        b_resp;
   logic                      b_trace;
   uvma_axi_sig_loop_t        b_loop;
   logic                      b_idunq;
   logic                      b_valid;
   logic                      b_ready;

   // read address channel
   uvma_axi_sig_id_t          ar_id;
   uvma_axi_sig_addr_t        ar_addr;
   uvma_axi_sig_user_t        ar_user;
   uvma_axi_sig_len_t         ar_len;
   uvma_axi_sig_size_t        ar_size;
   uvma_axi_sig_burst_t       ar_burst;
   uvma_axi_sig_lock_t        ar_lock;
   uvma_axi_sig_cache_t       ar_cache;
   uvma_axi_sig_prot_t        ar_prot;
   uvma_axi_sig_qos_t         ar_qos;
   uvma_axi_sig_region_t      ar_region;
   logic                      ar_valid;
   logic                      ar_ready;
   logic                      ar_trace;
   uvma_axi_sig_loop_t        ar_loop;
   logic                      ar_mmusecsid;
   uvma_axi_sig_mmusid_t      ar_mmusid;
   logic                      ar_mmussidv;
   uvma_axi_sig_mmussid_t     ar_mmussid;
   logic                      ar_mmuatst;
   uvma_axi_sig_nsaid_t       ar_nsaid;
   logic                      ar_idunq;

   //read data channel
   uvma_axi_sig_id_t          r_id;
   uvma_axi_sig_data_t        r_data;
   uvma_axi_sig_user_t        r_user;
   uvma_axi_sig_resp_t        r_resp;
   logic                      r_last;
   uvma_axi_sig_datachk_t     r_datachk;
   uvma_axi_sig_poison_t      r_poison;
   logic                      r_trace;
   uvma_axi_sig_loop_t        r_loop;
   logic                      r_idunq;
   logic                      r_valid;
   logic                      r_ready;

   bit                        aw_assertion_enabled;
   bit                        w_assertion_enabled;
   bit                        b_assertion_enabled;
   bit                        ar_assertion_enabled;
   bit                        r_assertion_enabled;
   bit                        axi_assertion_enabled;
   bit                        axi_amo_assertion_enabled;


   clocking slv_axi_cb @(posedge clk or rst_n);
      output   ar_ready,
               r_id, r_data, r_resp, r_last, r_valid, r_user, r_datachk, r_poison, r_trace, r_loop, r_idunq,
               aw_ready,
               w_ready,
               b_id, b_resp, b_user, b_valid, b_trace, b_loop, b_idunq;
      input    ar_id, ar_addr, ar_user, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_valid,
               r_ready,
               aw_id, aw_addr, aw_user, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_valid, aw_atop,
               w_data, w_strb, w_last, w_user, w_valid,
               b_ready;
   endclocking: slv_axi_cb

   clocking psv_axi_cb @(posedge clk or rst_n);
      input    ar_id, ar_addr, ar_user, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_valid, ar_ready,ar_trace, ar_loop, ar_mmusecsid, ar_mmusid, ar_mmussidv, ar_mmussid, ar_mmuatst, ar_nsaid, ar_idunq,
               r_ready, r_id, r_data, r_resp, r_user, r_last, r_valid, r_datachk, r_poison, r_trace, r_loop, r_idunq,
               aw_id, aw_addr, aw_user, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_valid, aw_atop, aw_ready, aw_trace, aw_loop, aw_mmusecsid, aw_mmusid, aw_mmussidv, aw_mmussid, aw_mmuatst, aw_nsaid, aw_idunq,
               w_data, w_strb, w_last, w_user, w_valid, w_ready, w_datachk, w_poison, w_trace,
               b_id, b_resp, b_user, b_trace, b_loop, b_idunq, b_valid, b_ready;
   endclocking: psv_axi_cb

   modport slave (clocking slv_axi_cb);
   modport passive (clocking psv_axi_cb);

endinterface : uvma_axi_intf
