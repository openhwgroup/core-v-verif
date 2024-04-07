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

   typedef enum {
      NONE,
      ADDR_DATA_NOT_COMPLETE,
      ADDR_DATA_COMPLETE,
      WAITING_RESP
   }uvma_axi_trs_status_t;

   typedef enum {
      UVMA_AXI_RESET_STATE_PRE_RESET,
      UVMA_AXI_RESET_STATE_IN_RESET,
      UVMA_AXI_RESET_STATE_POST_RESET
   } uvma_axi_reset_state_enum;

   typedef enum {
      UVMA_AXI_ORDERING_MODE_RANDOM,
      UVMA_AXI_OUTSTANDING_MODE,
      UVMA_AXI_ORDERING_MODE_FIFO,
      UVMA_AXI_INTERLEAVING_MODE
   } uvma_axi_slv_drv_ordering_mode;

   //----------------------------------------------
   // uvma_axi agent configuration typedefs
   // ---------------------------------------------
   // Driver idle values configuration
   typedef enum {ZERO,
                 UNDEFINED,
                 RANDOM
               } uvma_axi_dv_driver_idle_t;

   //----------------------------------------------
   // uvma_axi transaction verification typedefs
   // ---------------------------------------------
   // Type of transaction supported
   typedef enum {DEFAULT,
                 UVMA_AXI_READ_REQ,
                 UVMA_AXI_WRITE_REQ,
                 UVMA_AXI_WRITE_ADD_REQ,
                 UVMA_AXI_WRITE_DATA_REQ,
                 UVMA_AXI_READ_RSP,
                 UVMA_AXI_WRITE_RSP
               } uvma_axi_dv_txn_type_t;

   // uvma_axi protocol supported
   typedef enum {AXI4,
                 AXI5
               } uvma_axi_dv_ver_t;

   // LITE protocol supported
   typedef enum {NO_LITE,
                 LITE
               } uvma_axi_dv_lite_t;

   // uvma_axi protocol errors
   typedef enum {NO_ERR
               } uvma_axi_dv_err_t;

   // Internal types to generate ATOP field
   typedef enum logic [5:0] {ATOP_NONE  = 6'h00 ,
                             ATOP_STORE = 6'h10 ,
                             ATOP_LOAD  = 6'h20 ,
                             ATOP_SWAP  = 6'h30 ,
                             ATOP_CMP   = 6'h31
                           } uvma_axi_sig_atop_type_t;

   typedef enum logic {ATOP_LITTLE_END = 0 ,
                       ATOP_BIG_END    = 1
                     } uvma_axi_sig_atop_endianness_t;

   typedef enum logic [2:0] {ATOP_ADD  = 0 ,
                             ATOP_CLR  = 1 ,
                             ATOP_EOR  = 2 ,
                             ATOP_SET  = 3 ,
                             ATOP_SMAX = 4 ,
                             ATOP_SMIN = 5 ,
                             ATOP_UMAX = 6 ,
                             ATOP_UMIN = 7
                           } uvma_axi_sig_atop_op_t;

   //----------------------------------------------
   // uvma_axi Fields typedefs
   // ---------------------------------------------
   typedef enum logic [2:0] {BYTES_1   = 3'h0 ,
                             BYTES_2   = 3'h1 ,
                             BYTES_4   = 3'h2 ,
                             BYTES_8   = 3'h3 ,
                             BYTES_16  = 3'h4 ,
                             BYTES_32  = 3'h5 ,
                             BYTES_64  = 3'h6 ,
                             BYTES_128 = 3'h7
                           } uvma_axi_dv_size_t;

   typedef enum logic [1:0] {FIXED    = 2'h0 ,
                             INCR     = 2'h1 ,
                             WRAP     = 2'h2 ,
                             RESERVED = 2'h3
                            } uvma_axi_dv_burst_t;

   typedef enum logic {NORMAL    = 'h0 ,
                       EXCLUSIVE = 'h1
                      } uvma_axi_dv_lock_t;

   typedef enum  {DEVICE_NON_BUFFERABLE                 ,
                  DEVICE_BUFFERABLE                     ,
                  NORMAL_NON_CACHEABLE_NON_BUFFERABLE   ,
                  NORMAL_NON_CACHEABLE_BUFFERABLE       ,
                  WRITE_THROUGH_NO_ALLOCATE             ,
                  WRITE_THROUGH_READ_ALLOCATE           ,
                  WRITE_THROUGH_WRITE_ALLOCATE          ,
                  WRITE_THROUGH_READ_AND_WRITE_ALLOCATE ,
                  WRITE_BACK_NO_ALLOCATE                ,
                  WRITE_BACK_READ_ALLOCATE              ,
                  WRITE_BACK_WRITE_ALLOCATE             ,
                  WRITE_BACK_READ_AND_WRITE_ALLOCATE    ,
                  CACHE_RESERVED
                } uvma_axi_dv_mem_type_t;

   typedef enum logic [2:0] {UNPRIVILEGED_SECURE_DATA_ACCESS            = 3'h0 ,
                             PRIVILEGED_SECURE_DATA_ACCESS              = 3'h1 ,
                             UNPRIVILEGED_NON_SECURE_DATA_ACCESS        = 3'h2 ,
                             PRIVILEGED_NON_SECURE_DATA_ACCESS          = 3'h3 ,
                             UNPRIVILEGED_SECURE_INSTRUCTION_ACCESS     = 3'h4 ,
                             PRIVILEGED_SECURE_INSTRUCTION_ACCESS       = 3'h5 ,
                             UNPRIVILEGED_NON_SECURE_INSTRUCTION_ACCESS = 3'h6 ,
                             PRIVILEGED_NON_SECURE_INSTRUCTION_ACCESS   = 3'h7
                           } uvma_axi_dv_prot_t;

   typedef enum logic [1:0] {OKAY   = 2'h0 ,
                             EXOKAY = 2'h1 ,
                             SLVERR = 2'h2 ,
                             DECERR = 2'h3
                           } uvma_axi_dv_resp_t;

   typedef logic [MAX_ID_WIDTH-1:0]      uvma_axi_sig_id_t      ;
   typedef logic [MAX_ADDR_WIDTH-1:0]    uvma_axi_sig_addr_t    ;
   typedef logic [MAX_DATA_WIDTH-1:0]    uvma_axi_sig_data_t    ;
   typedef logic [MAX_DATA_WIDTH/8-1:0]  uvma_axi_sig_wstrb_t   ;
   typedef logic [MAX_DATA_WIDTH/8-1:0]  uvma_axi_sig_datachk_t ;
   typedef logic [MAX_DATA_WIDTH/64-1:0] uvma_axi_sig_poison_t  ;
   typedef logic [MAX_USER_WIDTH-1:0]    uvma_axi_sig_user_t    ;
   typedef logic [MAX_LOOP_WIDTH-1:0]    uvma_axi_sig_loop_t    ;
   typedef logic [MAX_MMUSID_WIDTH-1:0]  uvma_axi_sig_mmusid_t  ;
   typedef logic [MAX_MMUSSID_WIDTH-1:0] uvma_axi_sig_mmussid_t ;

   typedef logic [7:0] uvma_axi_sig_len_t    ;
   typedef logic [2:0] uvma_axi_sig_size_t   ;
   typedef logic [1:0] uvma_axi_sig_burst_t  ;
   typedef logic       uvma_axi_sig_lock_t   ;
   typedef logic [3:0] uvma_axi_sig_cache_t  ;
   typedef logic [3:0] uvma_axi_sig_region_t ;
   typedef logic [3:0] uvma_axi_sig_qos_t    ;
   typedef logic [5:0] uvma_axi_sig_atop_t   ;
   typedef logic [3:0] uvma_axi_sig_nsaid_t  ;
   typedef logic [2:0] uvma_axi_sig_prot_t   ;
   typedef logic [1:0] uvma_axi_sig_resp_t   ;

`endif // __UVMA_AXI_TDEFS_SV__
