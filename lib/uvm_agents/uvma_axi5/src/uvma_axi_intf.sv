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
   wire [MAX_ID_WIDTH-1:0]      aw_id;
   wire [MAX_ADDR_WIDTH-1:0]    aw_addr;
   wire [MAX_USER_WIDTH-1:0]    aw_user;
   wire [7:0]                   aw_len;
   wire [2:0]                   aw_size;
   wire [1:0]                   aw_burst;
   wire                         aw_lock;
   wire [3:0]                   aw_cache;
   wire [2:0]                   aw_prot;
   wire [3:0]                   aw_qos;
   wire [3:0]                   aw_region;
   wire                         aw_valid;
   wire                         aw_ready;
   wire [5:0]                   aw_atop;
   wire                         aw_trace;
   wire [MAX_LOOP_WIDTH-1:0]    aw_loop;
   wire                         aw_mmusecsid;
   wire [MAX_MMUSID_WIDTH-1:0]  aw_mmusid;
   wire                         aw_mmussidv;
   wire [MAX_MMUSSID_WIDTH-1:0] aw_mmussid;
   wire                         aw_mmuatst;
   wire [3:0]                   aw_nsaid;
   wire                         aw_idunq;

   //write data channel
   wire [MAX_DATA_WIDTH-1:0]    w_data;
   wire [MAX_DATA_WIDTH/8-1:0]  w_strb;
   wire [MAX_USER_WIDTH-1:0]    w_user;
   wire                         w_last;
   wire [MAX_DATA_WIDTH/8-1:0]  w_datachk;
   wire [MAX_DATA_WIDTH/64-1:0] w_poison;
   wire                         w_trace;
   wire                         w_valid;
   wire                         w_ready;

   // write response channel
   wire [MAX_ID_WIDTH-1:0]      b_id;
   wire [MAX_USER_WIDTH-1:0]    b_user;
   wire [1:0]                   b_resp;
   wire                         b_trace;
   wire [MAX_LOOP_WIDTH-1:0]    b_loop;
   wire                         b_idunq;
   wire                         b_valid;
   wire                         b_ready;

   // read address channel
   wire [MAX_ID_WIDTH-1:0]      ar_id;
   wire [MAX_ADDR_WIDTH-1:0]    ar_addr;
   wire [MAX_USER_WIDTH-1:0]    ar_user;
   wire [7:0]                   ar_len;
   wire [2:0]                   ar_size;
   wire [1:0]                   ar_burst;
   wire                         ar_lock;
   wire [3:0]                   ar_cache;
   wire [2:0]                   ar_prot;
   wire [3:0]                   ar_qos;
   wire [3:0]                   ar_region;
   wire                         ar_valid;
   wire                         ar_ready;
   wire                         ar_trace;
   wire [MAX_LOOP_WIDTH-1:0]    ar_loop;
   wire                         ar_mmusecsid;
   wire [MAX_MMUSID_WIDTH-1:0]  ar_mmusid;
   wire                         ar_mmussidv;
   wire [MAX_MMUSSID_WIDTH-1:0] ar_mmussid;
   wire                         ar_mmuatst;
   wire logic [3:0]             ar_nsaid;
   wire                         ar_idunq;

   //read data channel
   wire [MAX_ID_WIDTH-1:0]      r_id;
   wire [MAX_DATA_WIDTH-1:0]    r_data;
   wire [MAX_USER_WIDTH-1:0]    r_user;
   wire [1:0]                   r_resp;
   wire                         r_last;
   wire [MAX_DATA_WIDTH/8-1:0]  r_datachk;
   wire [MAX_DATA_WIDTH/64-1:0] r_poison;
   wire                         r_trace;
   wire [MAX_LOOP_WIDTH-1:0]    r_loop;
   wire                         r_idunq;
   wire                         r_valid;
   wire                         r_ready;

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
