//
// Copyright 2023 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//


`ifndef __UVMT_CV32E40S_BASE_TEST_TDEFS_SV__
`define __UVMT_CV32E40S_BASE_TEST_TDEFS_SV__


/**
 * Test Program Type.  See the Verification Strategy for a discussion of this.
 */
typedef enum {
  PREEXISTING_SELFCHECKING,
  PREEXISTING_NOTSELFCHECKING,
  GENERATED_SELFCHECKING,
  GENERATED_NOTSELFCHECKING,
  NO_TEST_PROGRAM
} test_program_type;

typedef enum {
  FETCH_CONSTANT,
  FETCH_INITIAL_DELAY_CONSTANT,
  FETCH_RANDOM_TOGGLE
} fetch_toggle_t;


/**
 * PMP reasons for accepting a request
 */
typedef struct packed {
  logic r_mmode_r;
  logic r_mmode_lr;
  logic w_mmode_w;
  logic w_mmode_lw;
  logic x_mmode_x;
  logic x_mmode_lx;

  logic r_umode_r;
  logic w_umode_w;
  logic x_umode_x;

  logic r_umode_mml_w;
  logic r_umode_mml_wx;
  logic r_umode_mml_r;
  logic r_umode_mml_rx;
  logic r_umode_mml_rw;
  logic r_umode_mml_rwx;
  logic r_umode_mml_lrwx;

  logic r_mmode_mml_w;
  logic r_mmode_mml_wx;
  logic r_mmode_mml_lwx;
  logic r_mmode_mml_lr;
  logic r_mmode_mml_lrx;
  logic r_mmode_mml_lrw;
  logic r_mmode_mml_lrwx;

  logic w_umode_mml_wx;
  logic w_umode_mml_rw;
  logic w_umode_mml_rwx;

  logic w_mmode_mml_w;
  logic w_mmode_mml_wx;
  logic w_mmode_mml_lrw;

  logic x_mmode_mml_lx;
  logic x_mmode_mml_lw;
  logic x_mmode_mml_lwx;
  logic x_mmode_mml_lrx;

  logic x_umode_mml_x;
  logic x_umode_mml_rx;
  logic x_umode_mml_rwx;
  logic x_umode_mml_lw;
  logic x_umode_mml_lwx;

  logic r_mmode_nomatch_nommwp_r;
  logic w_mmode_nomatch_nommwp_w;
  logic x_mmode_nomatch_nommwp_x;
} access_rsn_t;


/**
 * PMP matching status
 */
typedef struct packed {
  logic         is_access_allowed;
  logic         is_access_allowed_no_match;
  logic         is_any_locked;
  logic         is_dm_override;
  logic         is_locked;
  logic         is_matched;
  logic         is_rwx_ok;
  access_rsn_t  val_access_allowed_reason;
  logic[$clog2(PMP_MAX_REGIONS)-1:0]  val_index;
} match_status_t;


/**
 * PMA Status
 */
typedef struct packed {
  logic                        allow;
  logic                        main;
  logic                        bufferable;
  logic                        cacheable;
  logic                        integrity;
  logic                        override_dm;
  logic [PMA_MAX_REGIONS-1:0]  match_list;
  logic [31:0]                 match_idx;
  logic                        have_match;
  logic                        accesses_dmregion;
  logic                        accesses_jvt;
} pma_status_t;

typedef struct packed {
  obi_data_req_t  req;
  obi_data_resp_t resp;
  logic           valid;
} obi_data_packet_t;

typedef struct packed {
  obi_inst_req_t  req;
  obi_inst_resp_t resp;
  logic           valid;
} obi_instr_packet_t;


`endif // __UVMT_CV32E40S_BASE_TEST_TDEFS_SV__
