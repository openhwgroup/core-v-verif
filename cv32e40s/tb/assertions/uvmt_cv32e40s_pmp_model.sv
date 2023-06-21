// Copyright 2022 Silicon Labs, Inc.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0.
//
// You may obtain a copy of the License at
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.

`default_nettype none

module uvmt_cv32e40s_pmp_model
  import cv32e40s_pkg::*;
  import uvm_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  #(
    parameter int           PMP_GRANULARITY,
    parameter int           PMP_NUM_REGIONS,
    parameter logic [31:0]  DM_REGION_START,
    parameter logic [31:0]  DM_REGION_END
  )
  (
   // Clock and Reset
   input wire  clk,
   input wire  rst_n,

   // CSRs
   input wire pmp_csr_t  csr_pmp_i,

   // Privilege Mode
   input wire privlvl_t  priv_lvl_i,

   // Access Checking
   input wire [33:0]     pmp_req_addr_i,
   input wire pmp_req_e  pmp_req_type_i,
   input wire            pmp_req_err_o,

   // Debug Mode
   input wire  debug_mode,

   // Match Status
   output match_status_t  match_status_o
  );


  // Defines

  `define max(a,b) ((a) > (b) ? (a) : (b))


  // Check legal reasons to accept access

  always_comb begin
    match_status_o = {<<{'0}};

    // Lock Detection
    for (int region = 0; region < PMP_NUM_REGIONS; region++) begin
      match_status_o.is_any_locked = csr_pmp_i.cfg[region].lock ? 1'b1 : match_status_o.is_any_locked;
    end

    // Match Detection
    for (int i = 0; i < PMP_NUM_REGIONS; i++) begin
      automatic logic [$clog2(PMP_MAX_REGIONS)-1:0]  region = i;

      if (is_match_na4(region) || is_match_tor(region) || is_match_napot(region)) begin
        match_status_o.val_index  = region;
        match_status_o.is_matched = 1'b1;
        break;
      end
    end

    // Debug Module Override
    match_status_o.is_dm_override =
      debug_mode && ((DM_REGION_START <= pmp_req_addr_i) && (pmp_req_addr_i <= DM_REGION_END));

    // Allowed access whitelist table
    if (match_status_o.is_matched) begin
      match_status_o.is_locked = csr_pmp_i.cfg[match_status_o.val_index].lock;
      if (csr_pmp_i.mseccfg.mml === 1'b1) begin
        case (pmp_req_type_i)
          PMP_ACC_READ: begin
            // ------------------------------------------------------------
            // Read access U-Mode
            // ------------------------------------------------------------
            // Read access U-mode - Shared data region, U-mode RO
            match_status_o.val_access_allowed_reason.r_umode_mml_w    = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b0
            );
            // Read access U-mode - Shared data region, U-mode RW
            match_status_o.val_access_allowed_reason.r_umode_mml_wx   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Read access U-mode - Read flag
            match_status_o.val_access_allowed_reason.r_umode_mml_r    = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b0
            );
            // Read access U-mode - Read/execute flag
            match_status_o.val_access_allowed_reason.r_umode_mml_rx   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Read access U-mode - Read/Write flag
            match_status_o.val_access_allowed_reason.r_umode_mml_rw   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b0
            );
            // Read access U-mode - Read/Write/Execute flag
            match_status_o.val_access_allowed_reason.r_umode_mml_rwx  = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Read access U-mode - Locked shared region
            match_status_o.val_access_allowed_reason.r_umode_mml_lrwx = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );

            // ------------------------------------------------------------
            // Read access M-Mode
            // ------------------------------------------------------------
            // Read access M-mode - Shared data region, U-mode RO
            match_status_o.val_access_allowed_reason.r_mmode_mml_w    = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b0
            );
            // Read access M-mode - Shared data region, U-mode RW
            match_status_o.val_access_allowed_reason.r_mmode_mml_wx   = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Read access M-mode - Shared code region, M-mode RX
            match_status_o.val_access_allowed_reason.r_mmode_mml_lwx  = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Read access M-mode - Locked/Read
            match_status_o.val_access_allowed_reason.r_mmode_mml_lr   = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b0
            );
            // Read access M-mode - Locked read/execute region
            match_status_o.val_access_allowed_reason.r_mmode_mml_lrx  = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Read access M-mode - Locked read/write region
            match_status_o.val_access_allowed_reason.r_mmode_mml_lrw  = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b0
            );
            // Read access M-mode - Locked shared region
            match_status_o.val_access_allowed_reason.r_mmode_mml_lrwx = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
          end // PMP_ACC_READ

          PMP_ACC_WRITE: begin
            // ------------------------------------------------------------
            // Write access U-Mode
            // ------------------------------------------------------------
            // Write access U-mode - Shared data region, U-mode RW
            match_status_o.val_access_allowed_reason.w_umode_mml_wx   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Write access U-mode - Read/write region
            match_status_o.val_access_allowed_reason.w_umode_mml_rw   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b0
            );
            // Write access U-mode - Read/write/execute region
            match_status_o.val_access_allowed_reason.w_umode_mml_rwx  = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );

            // ------------------------------------------------------------
            // Write access M-Mode
            // ------------------------------------------------------------
            // Write access M-mode - Shared data region, U-mode RO
            match_status_o.val_access_allowed_reason.w_mmode_mml_w    = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b0
            );
            // Write access M-mode - Shared data region, U-mode RW
            match_status_o.val_access_allowed_reason.w_mmode_mml_wx   = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Write access M-mode - Locked read/write region
            match_status_o.val_access_allowed_reason.w_mmode_mml_lrw  = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b0
            );
          end // PMP_ACC_WRITE

          PMP_ACC_EXEC: begin
            // ------------------------------------------------------------
            // Execute access U-Mode
            // ------------------------------------------------------------
            // Execute access U-mode - Executable region
            match_status_o.val_access_allowed_reason.x_umode_mml_x    = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Execute access U-mode - Read/execute region
            match_status_o.val_access_allowed_reason.x_umode_mml_rx   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Execute access U-mode - Read/write/execute region
            match_status_o.val_access_allowed_reason.x_umode_mml_rwx  = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Execute access U-mode - Locked shared code region, X only
            match_status_o.val_access_allowed_reason.x_umode_mml_lw   = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b0
            );
            // Execute access U-mode - Locked shared code region, M-mode RX
            match_status_o.val_access_allowed_reason.x_umode_mml_lwx  = (
              priv_lvl_i == PRIV_LVL_U &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );

            // ------------------------------------------------------------
            // Execute access M-Mode
            // ------------------------------------------------------------
            // Execute access M-mode - Locked executable region
            match_status_o.val_access_allowed_reason.x_mmode_mml_lx   = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Execute access M-mode - Locked shared code region, X-only
            match_status_o.val_access_allowed_reason.x_mmode_mml_lw   = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b0
            );
            // Execute access M-mode - Locked shared code region, M-mode RX
            match_status_o.val_access_allowed_reason.x_mmode_mml_lwx  = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
            // Execute access M-mode - Locked Read/Execute region
            match_status_o.val_access_allowed_reason.x_mmode_mml_lrx  = (
              priv_lvl_i == PRIV_LVL_M &&
              csr_pmp_i.cfg[match_status_o.val_index].lock  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].read  == 1'b1 &&
              csr_pmp_i.cfg[match_status_o.val_index].write == 1'b0 &&
              csr_pmp_i.cfg[match_status_o.val_index].exec  == 1'b1
            );
          end // PMP_ACC_EXEC
        endcase // case(pmp_req_type_i)

      end else begin // mmwp low
        case ( priv_lvl_i )
          PRIV_LVL_M:
            case ( {pmp_req_type_i, match_status_o.is_locked} )
              { PMP_ACC_READ,  1'b1 }: match_status_o.val_access_allowed_reason.r_mmode_lr = csr_pmp_i.cfg[match_status_o.val_index].read;
              { PMP_ACC_READ,  1'b0 }: match_status_o.val_access_allowed_reason.r_mmode_r  = 1'b1;
              { PMP_ACC_WRITE, 1'b1 }: match_status_o.val_access_allowed_reason.w_mmode_lw = csr_pmp_i.cfg[match_status_o.val_index].write;
              { PMP_ACC_WRITE, 1'b0 }: match_status_o.val_access_allowed_reason.w_mmode_w  = 1'b1;
              { PMP_ACC_EXEC,  1'b1 }: match_status_o.val_access_allowed_reason.x_mmode_lx = csr_pmp_i.cfg[match_status_o.val_index].exec;
              { PMP_ACC_EXEC,  1'b0 }: match_status_o.val_access_allowed_reason.x_mmode_x  = 1'b1;
            endcase
          PRIV_LVL_U:
            case ( pmp_req_type_i )
              PMP_ACC_READ:  match_status_o.val_access_allowed_reason.r_umode_r = csr_pmp_i.cfg[match_status_o.val_index].read;
              PMP_ACC_WRITE: match_status_o.val_access_allowed_reason.w_umode_w = csr_pmp_i.cfg[match_status_o.val_index].write;
              PMP_ACC_EXEC:  match_status_o.val_access_allowed_reason.x_umode_x = csr_pmp_i.cfg[match_status_o.val_index].exec;
            endcase
        endcase // case (priv_lvl_i)

      end

      match_status_o.is_rwx_ok = |match_status_o.val_access_allowed_reason;
    end else begin
      // ------------------------------------------------------------
      // NO MATCH REGION
      // ------------------------------------------------------------
      // No matching region found, allow only M-access, and only if MMWP bit is not set
      case ( {pmp_req_type_i, priv_lvl_i} )
        { PMP_ACC_READ,  PRIV_LVL_M }:
          match_status_o.val_access_allowed_reason.r_mmode_nomatch_nommwp_r = !csr_pmp_i.mseccfg.mmwp;
        { PMP_ACC_WRITE, PRIV_LVL_M }:
          match_status_o.val_access_allowed_reason.w_mmode_nomatch_nommwp_w = !csr_pmp_i.mseccfg.mmwp;
        { PMP_ACC_EXEC,  PRIV_LVL_M }:
          match_status_o.val_access_allowed_reason.x_mmode_nomatch_nommwp_x = !csr_pmp_i.mseccfg.mmwp && !csr_pmp_i.mseccfg.mml;
      endcase
      match_status_o.is_access_allowed_no_match = |match_status_o.val_access_allowed_reason;
    end

    // Access is allowed if any one of the above conditions matches (or DM override)
    match_status_o.is_access_allowed =
      |match_status_o.val_access_allowed_reason || match_status_o.is_dm_override;
  end


  // Helper functions

  function automatic int is_match_na4(input logic[$clog2(PMP_MAX_REGIONS)-1:0] region);
    is_match_na4 = (csr_pmp_i.cfg[region].mode   == PMP_MODE_NA4)  &&
                   (csr_pmp_i.addr[region][33:2] == pmp_req_addr_i[33:2]);
  endfunction : is_match_na4

  function automatic logic is_match_tor(input logic[$clog2(PMP_MAX_REGIONS)-1:0] region);
    logic [33:2+PMP_GRANULARITY] req, hi, lo;

    req  = pmp_req_addr_i[33:2+PMP_GRANULARITY];
    hi   = csr_pmp_i.addr[region][33:2+PMP_GRANULARITY];
    lo   = (region > 0) ? csr_pmp_i.addr[region - 1'b1][33:2+PMP_GRANULARITY] : '0;

    is_match_tor = (csr_pmp_i.cfg[region].mode == PMP_MODE_TOR) &&
                   (lo   <= req) &&
                   (req   < hi);
  endfunction : is_match_tor

  function automatic int is_match_napot(input logic[$clog2(PMP_MAX_REGIONS)-1:0] region);
    logic [31:0] mask = gen_mask(region);
    logic [31:0] csr_addr_masked = csr_pmp_i.addr[region][33:2] & mask;
    logic [31:0] req_addr_masked = pmp_req_addr_i[33:2] & mask;

    is_match_napot = (csr_pmp_i.cfg[region].mode == PMP_MODE_NAPOT) &&
                     (csr_addr_masked == req_addr_masked);
  endfunction : is_match_napot

  function automatic logic[31:0] gen_mask(input logic[$clog2(PMP_MAX_REGIONS)-1:0] i);
    logic [31:0] mask;
    logic [31:0] csr_addr;

    mask = '1;
    if (PMP_GRANULARITY >= 1) begin
      mask[`max(PMP_GRANULARITY-1, 0) : 0] = '0;  // TODO remove or assume+assert?
    end

    csr_addr = csr_pmp_i.addr[i][33:2];
    if (PMP_GRANULARITY >= 2) begin
      csr_addr[`max(PMP_GRANULARITY-2, 0) : 0] = '1;  // TODO should be assumed+assert?
    end

    for (int j = 0; j < 32; j++) begin
      mask[j] = 0;
      if (csr_addr[j] == 0) begin
        break;
      end
    end

    return mask;
  endfunction

endmodule : uvmt_cv32e40s_pmp_model

`default_nettype wire
