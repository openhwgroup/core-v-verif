// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_TDEFS_SV__
`define __UVMA_CVXIF_TDEFS_SV__


typedef struct packed {
   logic                               accept;
   logic  [X_DUALWRITE:0]              writeback;
   logic  [X_NUM_RS+X_DUALREAD-1:0]    register_read;
} x_issue_resp_t;

typedef struct packed {
   logic  [X_HARTID_WIDTH-1:0]                         hartid;
   logic  [X_ID_WIDTH-1:0]                             id;
   logic  [X_RFW_WIDTH-1:0]                            data;
   logic  [4:0]                                        rd;
   logic  [X_DUALWRITE:0]                              we;
} x_result_t ;

typedef struct packed {
   logic  [X_HARTID_WIDTH-1:0]                         hartid;
   logic  [X_ID_WIDTH-1:0]                             id;
   logic  [X_NUM_RS-1:0][X_RFR_WIDTH-1:0]              rs;
   logic  [X_NUM_RS+X_DUALREAD-1:0]                    rs_valid;
} x_register_t ;

typedef struct packed {
   logic  [31:0]                        instr;
   logic  [X_HARTID_WIDTH-1:0]          hartid;
   logic  [X_ID_WIDTH-1:0]              id;
} x_issue_req_t;

typedef struct packed {
   logic  [15:0]                        instr;
   logic  [X_HARTID_WIDTH-1:0]          hartid;
} x_compressed_req_t;

typedef struct packed {
   logic  [31:0]                        instr;
   logic                                accept;
} x_compressed_resp_t;

typedef struct packed {
   logic  [X_HARTID_WIDTH-1:0]          hartid;
   logic  [X_ID_WIDTH-1:0]              id;
   logic                                commit_kill;
} x_commit_t;

typedef enum {
   UVMA_CVXIF_ISSUE_READY_FIX,
   UVMA_CVXIF_ISSUE_READY_RANDOMIZED
} uvma_cvxif_issue_ready_mode_enum;

typedef enum {
   UVMA_CVXIF_COMPRESSED_READY_FIX,
   UVMA_CVXIF_COMPRESSED_READY_RANDOMIZED
} uvma_cvxif_compressed_ready_mode_enum;

typedef enum {
   UVMA_CVXIF_RESET_STATE_PRE_RESET,
   UVMA_CVXIF_RESET_STATE_IN_RESET,
   UVMA_CVXIF_RESET_STATE_POST_RESET
} uvma_cvxif_reset_state_enum;

typedef enum {
   UVMA_CVXIF_ORDERING_MODE_RANDOM,
   UVMA_CVXIF_ORDERING_MODE_IN_ORDER
} uvma_cvxif_slv_drv_ordering_mode;

`endif //__UVMA_CVXIF_TDEFS_SV__
