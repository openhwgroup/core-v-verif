// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group
// Co-Author: Abdelaali Khardazi

`ifndef __UVMA_AXI_TDEFS_SV__
`define __UVMA_AXI_TDEFS_SV__

   // Logic vectors
   typedef logic [(`UVMA_AXI_ID_MAX_WIDTH      -1):0]  uvma_axi_id_l_t;
   typedef logic [(`UVMA_AXI_ADDR_MAX_WIDTH    -1):0]  uvma_axi_addr_l_t;
   typedef logic [(`UVMA_AXI_DATA_MAX_WIDTH    -1):0]  uvma_axi_data_l_t;
   typedef logic [(`UVMA_AXI_USER_MAX_WIDTH    -1):0]  uvma_axi_user_l_t;
   typedef logic [(`UVMA_AXI_LEN_MAX_WIDTH     -1):0]  uvma_axi_len_l_t;
   typedef logic [(`UVMA_AXI_SIZE_MAX_WIDTH    -1):0]  uvma_axi_size_l_t;
   typedef logic [(`UVMA_AXI_STRB_MAX_WIDTH    -1):0]  uvma_axi_strb_l_t;
   typedef logic [(`UVMA_AXI_BURST_MAX_WIDTH   -1):0]  uvma_axi_burst_l_t;
   typedef logic [(`UVMA_AXI_ATOP_MAX_WIDTH    -1):0]  uvma_axi_atop_l_t;
   typedef logic [(`UVMA_AXI_CACHE_MAX_WIDTH   -1):0]  uvma_axi_cache_l_t;
   typedef logic [(`UVMA_AXI_PROT_MAX_WIDTH    -1):0]  uvma_axi_prot_l_t;
   typedef logic [(`UVMA_AXI_QOS_MAX_WIDTH     -1):0]  uvma_axi_qos_l_t;
   typedef logic [(`UVMA_AXI_REGION_MAX_WIDTH  -1):0]  uvma_axi_region_l_t;
   typedef logic [(`UVMA_AXI_RESP_MAX_WIDTH    -1):0]  uvma_axi_resp_l_t;
   typedef logic                                       uvma_axi_ready_l_t;
   typedef logic                                       uvma_axi_last_l_t;
   typedef logic                                       uvma_axi_valid_l_t;
   typedef logic                                       uvma_axi_lock_l_t;

   typedef enum {
      ADDR_DATA_NOT_COMPLETE,
      ADDR_DATA_COMPLETE,
      WAITING_RESP
   }uvma_axi_w_trs_status_t;

   typedef enum {
      NONE,
      READ_DATA_NOT_COMPLETE,
      READ_DATA_COMPLETE,
      LAST_READ_DATA,
      LAST_READ_DATA_COMPLETE
   }uvma_axi_r_trs_status_t;

   typedef enum {
      UVMA_AXI_RESET_STATE_PRE_RESET,
      UVMA_AXI_RESET_STATE_IN_RESET,
      UVMA_AXI_RESET_STATE_POST_RESET
   } uvma_axi_reset_state_enum;

   typedef enum {
      UVMA_AXI_ACCESS_READ ,
      UVMA_AXI_ACCESS_WRITE
   } uvma_axi_access_type_enum;

   typedef enum {
      NULL,
      UVMA_AXI_RESP_WAITING_DATA,
      UVMA_AXI_RESP_WAITING_HANDSHAKE
   } uvma_axi_slv_handshake_resp_status;

   typedef struct packed {
           uvma_axi_data_l_t          w_data;
           uvma_axi_last_l_t          w_last;
           uvma_axi_strb_l_t          w_strb;
           int                        w_delay;
           longint                    w_start_time;
   } uvma_axi_w_data_trs_st;

   typedef struct packed {
             uvma_axi_id_l_t          r_id;
             uvma_axi_data_l_t        r_data;
             uvma_axi_last_l_t        r_last;
             uvma_axi_resp_l_t        r_resp;
             longint                  r_start_time;
   } uvma_axi_r_data_trs_st;

   typedef enum {
      UVMA_AXI_ORDERING_MODE_RANDOM,
      UVMA_AXI_OUTSTANDING_MODE,
      UVMA_AXI_ORDERING_MODE_FIFO
   } uvma_axi_slv_drv_ordering_mode;

   typedef enum {
      UVMA_AXI_VERSION_1P1,
      UVMA_AXI_VERSION_1P2,
      UVMA_AXI_VERSION_1P3
   } uvma_axi_version_enum;

`endif // __UVMA_AXI_TDEFS_SV__
