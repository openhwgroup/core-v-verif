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


module uvmt_cv32e40s_pmp_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  #(
    parameter int        PMP_GRANULARITY,
    parameter int        PMP_NUM_REGIONS,
    parameter int        IS_INSTR_SIDE,
    parameter mseccfg_t  PMP_MSECCFG_RV
  )
  (
   // Clock and Reset
   input wire            clk,
   input wire            rst_n,

   // CSRs
   input wire pmp_csr_t  csr_pmp_i,

   // Mode Info
   input wire privlvl_t  priv_lvl_i,
   input wire            bus_trans_dbg,

   // Access Checking
   input wire [33:0]     pmp_req_addr_i,
   input wire pmp_req_e  pmp_req_type_i,
   input wire            pmp_req_err_o,

   // OBI
   input wire         obi_req,
   input wire [31:0]  obi_addr,
   input wire         obi_gnt,

   // RVFI
   input wire         rvfi_valid,
   input wire [31:0]  rvfi_pc_rdata
  );


  string info_tag = "CV32E40S_PMP_ASSERT";


  // Defaults

  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n);


  // Helper logic

  match_status_t  match_status;
  uvmt_cv32e40s_pmp_model #(
    .PMP_GRANULARITY  (PMP_GRANULARITY),
    .PMP_NUM_REGIONS  (PMP_NUM_REGIONS),
    .DM_REGION_START  (CORE_PARAM_DM_REGION_START),
    .DM_REGION_END    (CORE_PARAM_DM_REGION_END)
  ) model_i (
    .debug_mode     (bus_trans_dbg),
    .match_status_o (match_status),
    .*
  );


  // Extra covers and asserts to comprehensively match the spec

  // Cover the helper-RTL internals
  generate
    if (IS_INSTR_SIDE === 1'b1 && PMP_NUM_REGIONS > 0) begin : gen_cp_instr_side
      covergroup cg_internals_instr_side @(posedge clk);
        option.per_instance = 1;

        // Machine mode execute accesses
        cp_x_mmode_x                : coverpoint match_status.val_access_allowed_reason.x_mmode_x                { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_mmode_lx               : coverpoint match_status.val_access_allowed_reason.x_mmode_lx               { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_mmode_mml_lx           : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_mmode_mml_lw           : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lw           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_mmode_mml_lwx          : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lwx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_mmode_mml_lrx          : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lrx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_mmode_nomatch_nommwp_x : coverpoint match_status.val_access_allowed_reason.x_mmode_nomatch_nommwp_x { bins low  = {1'b0}; bins high = {1'b1}; }
        // User mode execute accesses
        cp_x_umode_x                : coverpoint match_status.val_access_allowed_reason.x_umode_x                { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_umode_mml_x            : coverpoint match_status.val_access_allowed_reason.x_umode_mml_x            { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_umode_mml_rx           : coverpoint match_status.val_access_allowed_reason.x_umode_mml_rx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_umode_mml_rwx          : coverpoint match_status.val_access_allowed_reason.x_umode_mml_rwx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_umode_mml_lw           : coverpoint match_status.val_access_allowed_reason.x_umode_mml_lw           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_x_umode_mml_lwx          : coverpoint match_status.val_access_allowed_reason.x_umode_mml_lwx          { bins low  = {1'b0}; bins high = {1'b1}; }
        // Ignore bins for unreachable load/stores on instruction if
        // Machine mode l/s accesses
        cp_r_mmode_nomatch_nommwp_r : coverpoint match_status.val_access_allowed_reason.r_mmode_nomatch_nommwp_r { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_mmode_nomatch_nommwp_w : coverpoint match_status.val_access_allowed_reason.w_mmode_nomatch_nommwp_w { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_mmode_mml_w            : coverpoint match_status.val_access_allowed_reason.w_mmode_mml_w            { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_mmode_mml_wx           : coverpoint match_status.val_access_allowed_reason.w_mmode_mml_wx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_mmode_mml_lrw          : coverpoint match_status.val_access_allowed_reason.w_mmode_mml_lrw          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_r                : coverpoint match_status.val_access_allowed_reason.r_mmode_r                { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_lr               : coverpoint match_status.val_access_allowed_reason.r_mmode_lr               { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_mmode_w                : coverpoint match_status.val_access_allowed_reason.w_mmode_w                { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_mmode_lw               : coverpoint match_status.val_access_allowed_reason.w_mmode_lw               { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_w            : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_w            { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_wx           : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_wx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_lwx          : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lwx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_lr           : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lr           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_lrx          : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lrx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_lrw          : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lrw          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_mmode_mml_lrwx         : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lrwx         { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        // User mode l/s accesses
        cp_w_umode_mml_wx           : coverpoint match_status.val_access_allowed_reason.w_umode_mml_wx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_umode_mml_rw           : coverpoint match_status.val_access_allowed_reason.w_umode_mml_rw           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_umode_mml_rwx          : coverpoint match_status.val_access_allowed_reason.w_umode_mml_rwx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_r                : coverpoint match_status.val_access_allowed_reason.r_umode_r                { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_w_umode_w                : coverpoint match_status.val_access_allowed_reason.w_umode_w                { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_w            : coverpoint match_status.val_access_allowed_reason.r_umode_mml_w            { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_wx           : coverpoint match_status.val_access_allowed_reason.r_umode_mml_wx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_r            : coverpoint match_status.val_access_allowed_reason.r_umode_mml_r            { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_rx           : coverpoint match_status.val_access_allowed_reason.r_umode_mml_rx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_rw           : coverpoint match_status.val_access_allowed_reason.r_umode_mml_rw           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_rwx          : coverpoint match_status.val_access_allowed_reason.r_umode_mml_rwx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_r_umode_mml_lrwx         : coverpoint match_status.val_access_allowed_reason.r_umode_mml_lrwx         { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        // TODO:silabs-robin  Try swapping all "ignore_bins" with "illegal_bins" in fv
      endgroup : cg_internals_instr_side
      cg_internals_instr_side cg_instr = new();
    end
    else if (IS_INSTR_SIDE === 1'b0 && PMP_NUM_REGIONS > 0) begin : gen_cp_data_side
      covergroup cg_internals_data_side @(posedge clk);
        option.per_instance = 1;

        // Ignore bins for unreachable execute accesses on lsu if
        // Machine mode execute accesses
        cp_x_mmode_x                : coverpoint match_status.val_access_allowed_reason.x_mmode_x                { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_mmode_lx               : coverpoint match_status.val_access_allowed_reason.x_mmode_lx               { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_mmode_mml_lx           : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_mmode_mml_lw           : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lw           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_mmode_mml_lwx          : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lwx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_mmode_mml_lrx          : coverpoint match_status.val_access_allowed_reason.x_mmode_mml_lrx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_mmode_nomatch_nommwp_x : coverpoint match_status.val_access_allowed_reason.x_mmode_nomatch_nommwp_x { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        // User mode execute accesses
        cp_x_umode_x                : coverpoint match_status.val_access_allowed_reason.x_umode_x                { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_umode_mml_x            : coverpoint match_status.val_access_allowed_reason.x_umode_mml_x            { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_umode_mml_rx           : coverpoint match_status.val_access_allowed_reason.x_umode_mml_rx           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_umode_mml_rwx          : coverpoint match_status.val_access_allowed_reason.x_umode_mml_rwx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_umode_mml_lw           : coverpoint match_status.val_access_allowed_reason.x_umode_mml_lw           { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        cp_x_umode_mml_lwx          : coverpoint match_status.val_access_allowed_reason.x_umode_mml_lwx          { bins low  = {1'b0}; ignore_bins high = {1'b1}; }
        // Machine mode l/s accesses
        cp_r_mmode_nomatch_nommwp_r : coverpoint match_status.val_access_allowed_reason.r_mmode_nomatch_nommwp_r { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_mmode_nomatch_nommwp_w : coverpoint match_status.val_access_allowed_reason.w_mmode_nomatch_nommwp_w { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_mmode_mml_w            : coverpoint match_status.val_access_allowed_reason.w_mmode_mml_w            { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_mmode_mml_wx           : coverpoint match_status.val_access_allowed_reason.w_mmode_mml_wx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_mmode_mml_lrw          : coverpoint match_status.val_access_allowed_reason.w_mmode_mml_lrw          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_r                : coverpoint match_status.val_access_allowed_reason.r_mmode_r                { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_lr               : coverpoint match_status.val_access_allowed_reason.r_mmode_lr               { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_mmode_w                : coverpoint match_status.val_access_allowed_reason.w_mmode_w                { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_mmode_lw               : coverpoint match_status.val_access_allowed_reason.w_mmode_lw               { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_w            : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_w            { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_wx           : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_wx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_lwx          : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lwx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_lr           : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lr           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_lrx          : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lrx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_lrw          : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lrw          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_mmode_mml_lrwx         : coverpoint match_status.val_access_allowed_reason.r_mmode_mml_lrwx         { bins low  = {1'b0}; bins high = {1'b1}; }
        // User mode l/s accesses
        cp_w_umode_mml_wx           : coverpoint match_status.val_access_allowed_reason.w_umode_mml_wx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_umode_mml_rw           : coverpoint match_status.val_access_allowed_reason.w_umode_mml_rw           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_umode_mml_rwx          : coverpoint match_status.val_access_allowed_reason.w_umode_mml_rwx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_r                : coverpoint match_status.val_access_allowed_reason.r_umode_r                { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_w_umode_w                : coverpoint match_status.val_access_allowed_reason.w_umode_w                { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_w            : coverpoint match_status.val_access_allowed_reason.r_umode_mml_w            { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_wx           : coverpoint match_status.val_access_allowed_reason.r_umode_mml_wx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_r            : coverpoint match_status.val_access_allowed_reason.r_umode_mml_r            { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_rx           : coverpoint match_status.val_access_allowed_reason.r_umode_mml_rx           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_rw           : coverpoint match_status.val_access_allowed_reason.r_umode_mml_rw           { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_rwx          : coverpoint match_status.val_access_allowed_reason.r_umode_mml_rwx          { bins low  = {1'b0}; bins high = {1'b1}; }
        cp_r_umode_mml_lrwx         : coverpoint match_status.val_access_allowed_reason.r_umode_mml_lrwx         { bins low  = {1'b0}; bins high = {1'b1}; }
      endgroup : cg_internals_data_side
      cg_internals_data_side cg_data = new();
    end
  endgenerate

  generate
    if (PMP_NUM_REGIONS > 0) begin : gen_cg_common
      covergroup cg_internals_common @(posedge clk);
        option.per_instance = 1;

        cp_ismatch_tor:   coverpoint model_i.is_match_tor(match_status.val_index) iff (match_status.is_matched);

        cp_napot_min_8byte: coverpoint { pmp_req_addr_i[2], csr_pmp_i.addr[match_status.val_index][2] }
          iff (csr_pmp_i.cfg[match_status.val_index].mode == PMP_MODE_NAPOT &&
               match_status.is_matched         == 1'b1 &&
               match_status.is_access_allowed  == 1'b1
        );

        cp_napot_min_8byte_disallowed: coverpoint { pmp_req_addr_i[2], csr_pmp_i.addr[match_status.val_index][2] }
          iff (csr_pmp_i.cfg[match_status.val_index].mode == PMP_MODE_NAPOT &&
               match_status.is_matched         == 1'b1 &&
               match_status.is_access_allowed  == 1'b0
        );

        cp_napot_encoding: coverpoint ( pmp_req_addr_i[33:2+PMP_GRANULARITY] == csr_pmp_i.addr[match_status.val_index][33:2+PMP_GRANULARITY] )
          iff (csr_pmp_i.cfg[match_status.val_index].mode == PMP_MODE_NAPOT &&
               match_status.is_matched        == 1'b1 &&
               match_status.is_access_allowed == 1'b1
        );

        cp_napot_encoding_disallowed: coverpoint ( pmp_req_addr_i[33:2+PMP_GRANULARITY] == csr_pmp_i.addr[match_status.val_index][33:2+PMP_GRANULARITY] )
          iff (csr_pmp_i.cfg[match_status.val_index].mode == PMP_MODE_NAPOT &&
               match_status.is_matched        == 1'b1 &&
               match_status.is_access_allowed == 1'b0
        );

      endgroup
      cg_internals_common cg_int = new();
    end
  endgenerate

  // NA4 only available in G=0  (vplan:Na4Unselectable)
  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_na4onlyg0
    a_na4_only_g0: assert property (
      (csr_pmp_i.cfg[region].mode == PMP_MODE_NA4)
      |->
      (PMP_GRANULARITY === 1'b 0)
    ) else `uvm_error(info_tag, "G must be 0 if using NA4");


    if (PMP_GRANULARITY !== 1'b 0) begin: gen_na4onlyg0_reverse
      a_na4_not_when_g: assert property (
        // "Redundant" assert for coverage
        (csr_pmp_i.cfg[region].mode !== PMP_MODE_NA4)
      ) else `uvm_error(info_tag, "mode can't be NA4 if G=0");
    end
  end endgenerate

  // NA4 has 4-byte granularity  (vplan:NapotMatching)
  generate if (PMP_GRANULARITY == 0 && PMP_NUM_REGIONS > 0) begin: gen_na4is4byte
    a_na4_is_4byte: assert property (
        csr_pmp_i.cfg[match_status.val_index].mode == PMP_MODE_NA4 &&
        match_status.is_matched        == 1'b1 &&
        match_status.is_access_allowed == 1 |->
           pmp_req_addr_i[31:2] == csr_pmp_i.addr[match_status.val_index][31:2]
    ) else `uvm_error(info_tag, "NA4 matches must match word-aligned");
  end endgenerate

  // Spec: "The combination R=0 and W=1 is reserved for future use" - Exception: mml set
  // (vplan:RwReserved)
  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_rwfuture
    a_rw_futureuse: assert property  (
      csr_pmp_i.mseccfg.mml === 1'b0 |->
        !(csr_pmp_i.cfg[region].read == 0 && csr_pmp_i.cfg[region].write == 1)
    ) else `uvm_error(info_tag, "'RW' cannot be 01");
  end endgenerate

  // mseccfg.RLB = 1 LOCKED rules may be modified/removed, LOCKED entries may be modified -> test inverse
  // (vplan:IgnoreWrites)
  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_rlb_locked
    a_norlb_locked_rules_cannot_modify : assert property (
      csr_pmp_i.mseccfg.rlb === 1'b0 && csr_pmp_i.cfg[region].lock === 1'b1 |=>
        $stable(csr_pmp_i.cfg[region])
    ) else `uvm_error(info_tag, "locked unbypassed cfgs must be stable");
  end endgenerate

  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_rlb_locked_cov
    cov_rlb_locked_rules_can_modify_addr : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.addr[region])
    );

    cov_rlb_locked_rules_can_modify_lock : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].lock)
    );

    cov_rlb_locked_rules_can_modify_exec : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].exec)
    );

    cov_rlb_locked_rules_can_modify_mode : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].mode)
    );

    cov_rlb_locked_rules_can_modify_write : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].write)
    );

    cov_rlb_locked_rules_can_modify_read : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].read)
    );

    cov_rlb_locked_rules_can_remove : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 &&
      csr_pmp_i.cfg[region].lock == 1'b1 &&
      csr_pmp_i.cfg[region].mode != PMP_MODE_OFF ##1
        csr_pmp_i.cfg[region].mode === PMP_MODE_OFF
    );

    // Adding an M-mode-only or a locked Shared-Region rule with executable privileges is not possible and
    // such pmpcfg writes are ignored, leaving pmpcfg unchanged. This restriction can be temporarily lifted
    // e.g. during the boot process, by setting mseccfg.RLB.
    // (vplan:ExecIgnored)
    a_mmode_only_or_shared_executable_ignore: assert property (
      csr_pmp_i.mseccfg.mml === 1'b1 && csr_pmp_i.mseccfg.rlb === 1'b0 |=>
        $stable(csr_pmp_i.cfg[region])
      or
        not ($changed(csr_pmp_i.cfg[region]) ##0
        csr_pmp_i.cfg[region].lock === 1'b1 ##0
        csr_pmp_i.cfg[region].read === 1'b0 ##0
        csr_pmp_i.cfg[region].write || csr_pmp_i.cfg[region].exec)
    ) else `uvm_error(info_tag, "certain rules can't be added");

    cov_mmode_only_or_shared_executable: cover property (
      csr_pmp_i.mseccfg.mml === 1'b1 && csr_pmp_i.mseccfg.rlb === 1'b1
      ##1
        $changed(csr_pmp_i.cfg[region])     ##0
        csr_pmp_i.cfg[region].lock === 1'b1 ##0
        csr_pmp_i.cfg[region].read === 1'b0 ##0
        csr_pmp_i.cfg[region].write || csr_pmp_i.cfg[region].exec
    );
  end endgenerate

  // Validate PMP mode settings  (Not a vplan item)
  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_matchmode
    a_matchmode: assert property (
      csr_pmp_i.cfg[region].mode inside {
        PMP_MODE_OFF,
        PMP_MODE_TOR,
        PMP_MODE_NA4,
        PMP_MODE_NAPOT
      }
    ) else `uvm_error(info_tag, "pmp mode must be supported");
  end endgenerate

  generate if (PMP_NUM_REGIONS > 0) begin : gen_pmp_assert
    // Check output vs model  (Myriad vplan items)
    a_accept_only_legal : assert property (
      (pmp_req_err_o === 1'b0) |-> match_status.is_access_allowed
    ) else `uvm_error(info_tag, "mismatch, PMP allow must match model");
    a_deny_only_illegal : assert property (
      pmp_req_err_o |-> (match_status.is_access_allowed === 1'b0)
    ) else `uvm_error(info_tag, "mismatch, PMP deny must match model");

    // Assert that only one (or none) valid access reason can exist for any given access  (Not a vplan item)
    a_unique_access_allowed_reason: assert property (
      $countones(match_status.val_access_allowed_reason) <= 1
    ) else `uvm_error(info_tag, "there can only be 1 accept reason");

    // Validate privilege level  (Not a vplan item)
    a_privmode: assert property (
      priv_lvl_i inside {
        PRIV_LVL_M,
        PRIV_LVL_U
      }
    ) else `uvm_error(info_tag, "the privilege mode must be supported");


    // Validate access type  (TODO:silabs-robin make it a vplan item)

    if (IS_INSTR_SIDE) begin: gen_req_type_instr
      a_req_type_instr: assert property (
        pmp_req_type_i inside {
          PMP_ACC_EXEC
        }
      ) else `uvm_error(info_tag, "instr-side access must be execution");
    end : gen_req_type_instr

    if (!IS_INSTR_SIDE) begin: gen_req_type_data
      a_req_type_data: assert property (
        pmp_req_type_i inside {
          PMP_ACC_READ,
          PMP_ACC_WRITE
        }
      ) else `uvm_error(info_tag, "data-side access must be loadstore");
    end : gen_req_type_data


    // SMEPMP 2b: When mseccfg.RLB is 0 and pmpcfg.L is 1 in any rule or entry (including disabled entries), then
    // mseccfg.RLB remains 0 and any further modifications to mseccfg.RLB are ignored until a PMP reset.
    //
    // In other words: mseccfg.RLB = 0 and pmpcfg.L = 1 in any rule or entry (including disabled),
    // mseccfg.RLB remains 0 and does not change until PMP reset.
    // (vplan:RemainZero)
    a_rlb_never_fall_while_locked: assert property (
      csr_pmp_i.mseccfg.rlb === 1'b0 && match_status.is_any_locked |=>
        $stable(csr_pmp_i.mseccfg.rlb)
    ) else `uvm_error(info_tag, "RLB must remain off after it is locked");

    // SMEPMP 3: On mseccfg we introduce a field in bit 1 called Machine Mode Whitelist Policy (mseccfg.MMWP).
    // This is a sticky bit, meaning that once set it cannot be unset until a PMP reset.
    // (vplan:WhiteList:StickyUntilReset)
    a_mmwp_never_fall_until_reset: assert property (
      csr_pmp_i.mseccfg.mmwp === 1'b1 |=>
        $stable(csr_pmp_i.mseccfg.mmwp)
    ) else `uvm_error(info_tag, "MMWP is sticky high");

    // SMEPMP 4: On mseccfg we introduce a field in bit 0 called Machine Mode Lockdown (mseccfg.MML). This is a
    // sticky bit, meaning that once set it cannot be unset until a PMP reset.
    // (vplan:LockdownGeneral:StickyUntilReset)
    a_mml_never_fall_until_reset: assert property (
      csr_pmp_i.mseccfg.mml === 1'b1 |=>
        $stable(csr_pmp_i.mseccfg.mml)
    ) else `uvm_error(info_tag, "MML is sticky high");

    // U-mode fails if no match  (vplan:UmodeNomatch)
    a_nomatch_umode_fails: assert property (
      priv_lvl_i == PRIV_LVL_U && match_status.is_matched == 1'b0 |->
        pmp_req_err_o ^ match_status.is_dm_override
    ) else `uvm_error(info_tag, "non-matched umode access must fail");

    // M-mode fails if: no match, and "mseccfg.MMWP"  (vplan:WhiteList:Denied)
    a_nomatch_mmode_mmwp_fails: assert property (
      (priv_lvl_i == PRIV_LVL_M)  &&
      !match_status.is_matched  &&
      csr_pmp_i.mseccfg.mmwp
      |->
      pmp_req_err_o ^ match_status.is_dm_override
    ) else `uvm_error(info_tag, "non-matched mmode access must fail when MMWP");

    // U-mode or L=1 succeed only if RWX  (vplan:RwxUmode)
    a_uorl_onlyif_rwx: assert property (
      //TODO:silabs-robin  Why, 'L=1' in comment, but 'is_matched' in code?
      ( priv_lvl_i == PRIV_LVL_U || match_status.is_matched == 1'b1 ) && !pmp_req_err_o
      |->
        match_status.is_rwx_ok || match_status.is_dm_override
    ) else `uvm_error(info_tag, "RWX must agree for allowing umode and L");

    // After a match, LRWX determines access  (vplan:LrwxDetermines)
    a_lrwx_aftermatch: assert property (
      //TODO:silabs-robin  Why, "LRWX" in comment, but "rwx" in code?
      match_status.is_matched == 1'b1 && !pmp_req_err_o |->
        match_status.is_rwx_ok || match_status.is_dm_override
    ) else `uvm_error(info_tag, "LRWX must agree for allowing matched access");

    // SMEPMP 1: The reset value of mseccfg is implementation-specific, otherwise if backwards
    // compatibility is a requirement it should reset to zero on hard reset.
    // (vplan:MsecCfg:ResetValue)
    a_mseccfg_reset_val: assert property (
      $rose(rst_n) |-> csr_pmp_i.mseccfg === PMP_MSECCFG_RV
    ) else `uvm_error(info_tag, "mseccfg must be reset correctly");
  end endgenerate


  // Denied accesses don't reach the bus, or don't retire (instr-side)  (vplan:SuppressReq)

  if (IS_INSTR_SIDE) begin: gen_supress_req_instr
    property p_suppress_req_instr;
      logic [31:0]  addr = 0;

      (
        // Addr denied, but retires
        pmp_req_err_o  ##0
        (1, addr = pmp_req_addr_i[31:0])  ##0
        ((rvfi_valid && (rvfi_pc_rdata == addr)) [->1])
      )
      implies
      (
        (
          // Doesn't reach bus, until retirement
          (
            !(obi_req && (obi_addr == addr))  ||  // (Forbidden addr doesn't reach bus)
            $past(obi_req && !obi_gnt)            // (Excuse ongoing remnant)
          )
          throughout
          ((rvfi_valid && (rvfi_pc_rdata == addr)) [->1])
        )
        or
        (
          // ...or, re-attempt got permission
          (!pmp_req_err_o && (pmp_req_addr_i[31:2] == addr[31:2]))
          within
          ((rvfi_valid && (rvfi_pc_rdata == addr)) [->1])
        )
      )
      ;
    endproperty : p_suppress_req_instr

    a_suppress_req_instr: assert property (
      p_suppress_req_instr
    ) else `uvm_error(info_tag, "denied ifetch must refetch or not retire");
  end


  // Denied accesses don't reach the bus (data-side)  (vplan:SuppressReq)

  if (!IS_INSTR_SIDE) begin: gen_supress_req_data
    property p_suppress_req_data;
      logic [31:0]  addr;

      // When "addr" is denied
      pmp_req_err_o  ##0
      (1, addr = pmp_req_addr_i[31:0])

      |->

      (
        !obi_req                                            ^  // OBI is quelled
        ($past(obi_req && !obi_gnt) && (obi_addr == addr))  ^  // (...or has leftovers)
        (obi_req && (obi_addr != addr))                        // (...or does something completely different
      )
      until
      (
        // New attempt, got permission
        (pmp_req_addr_i == addr)  &&
        !pmp_req_err_o
        // Note: Can add timeout if proven to be resource-hungry
      )
      ;
    endproperty : p_suppress_req_data

    a_suppress_req_data: assert property (
      p_suppress_req_data
    ) else `uvm_error(info_tag, "denied data access doesn't reach bus");
    // TODO:silabs-robin  Add covers, or get reviews, and become convinced this is "bullet proof".
  end


endmodule : uvmt_cv32e40s_pmp_assert


`default_nettype wire
