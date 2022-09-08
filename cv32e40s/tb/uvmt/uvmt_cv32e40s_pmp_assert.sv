`default_nettype none

module uvmt_cv32e40s_pmp_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_pkg::*;
  #(
    parameter int       PMP_GRANULARITY   = 0,
    parameter int       PMP_NUM_REGIONS   = 0,
    parameter int       IS_INSTR_SIDE     = 0,
    parameter mseccfg_t MSECCFG_RESET_VAL = MSECCFG_DEFAULT
  )
  (
   // Clock and Reset
   input wire            clk,
   input wire            rst_n,

   // Interface to CSRs
   input wire pmp_csr_t  csr_pmp_i,

   // Privilege mode
   input wire privlvl_t  priv_lvl_i,

   // Access checking
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


  // Defaults

  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n);


  // Helper logic

  match_status_t  match_status;
  uvmt_cv32e40s_pmp_model #(
    .PMP_GRANULARITY  (PMP_GRANULARITY),
    .PMP_NUM_REGIONS  (PMP_NUM_REGIONS)
  ) model_i (
    .match_status_o (match_status),
    .*
  );


  // Extra covers and asserts to comprehensively match the spec

  // Cover the helper-RTL internals
  generate
    if (IS_INSTR_SIDE === 1'b1 && PMP_NUM_REGIONS > 0) begin : gen_cp_instr_side
      covergroup cg_internals_instr_side @(posedge clk);
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
      endgroup : cg_internals_instr_side
      cg_internals_instr_side cg_instr = new();
    end
    else if (IS_INSTR_SIDE === 1'b0 && PMP_NUM_REGIONS > 0) begin : gen_cp_data_side
      covergroup cg_internals_data_side @(posedge clk);
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
      cg_internals_data_side cg_instr = new();
    end
  endgenerate

  generate
    if (PMP_NUM_REGIONS > 0) begin : gen_cg_common
      covergroup cg_internals_common @(posedge clk);
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

  // NA4 only available in G=1
  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_na4onlyg0
    a_na4_only_g0: assert property (
      (csr_pmp_i.cfg[region].mode == PMP_MODE_NA4)
      |->
      (PMP_GRANULARITY === 1'b 0)
    );

    a_na4_not_when_g: assert property (
      // "Redundant" assert for (antecedent) coverage
      (PMP_GRANULARITY !== 1'b 0)
      |->
      (csr_pmp_i.cfg[region].mode !== PMP_MODE_NA4)
    );
  end endgenerate

  // NA4 has 4-byte granularity
  generate if (PMP_GRANULARITY == 0 && PMP_NUM_REGIONS > 0) begin: gen_na4is4byte
    a_na4_is_4byte: assert property (
        csr_pmp_i.cfg[match_status.val_index].mode == PMP_MODE_NA4 &&
        match_status.is_matched        == 1'b1 &&
        match_status.is_access_allowed == 1 |->
           pmp_req_addr_i[31:2] == csr_pmp_i.addr[match_status.val_index][31:2]
    );
  end endgenerate

  // Spec: "The combination R=0 and W=1 is reserved for future use" - Exception: mml set
  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_rwfuture
    a_rw_futureuse: assert property  (
      csr_pmp_i.mseccfg.mml === 1'b0 |->
        !(csr_pmp_i.cfg[region].read == 0 && csr_pmp_i.cfg[region].write == 1)
    );
  end endgenerate

  // mseccfg.RLB = 1 LOCKED rules may be modified/removed, LOCKED entries may be modified -> test inverse
  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_rlb_locked
    a_norlb_locked_rules_cannot_modify : assert property (
      csr_pmp_i.mseccfg.rlb === 1'b0 && csr_pmp_i.cfg[region].lock === 1'b1 |=>
        $stable(csr_pmp_i.cfg[region])
    );
  end endgenerate

  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_rlb_locked_cov
    c_rlb_locked_rules_can_modify_addr : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.addr[region])
    );

    c_rlb_locked_rules_can_modify_lock : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].lock)
    );

    c_rlb_locked_rules_can_modify_exec : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].exec)
    );

    c_rlb_locked_rules_can_modify_mode : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].mode)
    );

    c_rlb_locked_rules_can_modify_write : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].write)
    );

    c_rlb_locked_rules_can_modify_read : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 && csr_pmp_i.cfg[region].lock === 1'b1 ##1
        $changed(csr_pmp_i.cfg[region].read)
    );

    c_rlb_locked_rules_can_remove : cover property (
      csr_pmp_i.mseccfg.rlb === 1'b1 &&
      csr_pmp_i.cfg[region].lock == 1'b1 &&
      csr_pmp_i.cfg[region].mode != PMP_MODE_OFF ##1
        csr_pmp_i.cfg[region].mode === PMP_MODE_OFF
    );

    // Adding an M-mode-only or a locked Shared-Region rule with executable privileges is not possible and
    // such pmpcfg writes are ignored, leaving pmpcfg unchanged. This restriction can be temporarily lifted
    // e.g. during the boot process, by setting mseccfg.RLB.
    a_mmode_only_or_shared_executable_ignore: assert property (
      csr_pmp_i.mseccfg.mml === 1'b1 && csr_pmp_i.mseccfg.rlb === 1'b0 |=>
        $stable(csr_pmp_i.cfg[region])
      or
        not ($changed(csr_pmp_i.cfg[region]) ##0
        csr_pmp_i.cfg[region].lock === 1'b1 ##0
        csr_pmp_i.cfg[region].read === 1'b0 ##0
        csr_pmp_i.cfg[region].write || csr_pmp_i.cfg[region].exec)
    );

    c_mmode_only_or_shared_executable: cover property (
      csr_pmp_i.mseccfg.mml === 1'b1 && csr_pmp_i.mseccfg.rlb === 1'b1
      ##1
        $changed(csr_pmp_i.cfg[region])     ##0
        csr_pmp_i.cfg[region].lock === 1'b1 ##0
        csr_pmp_i.cfg[region].read === 1'b0 ##0
        csr_pmp_i.cfg[region].write || csr_pmp_i.cfg[region].exec
    );
  end endgenerate

  // Validate PMP mode settings
  generate for (genvar region = 0; region < PMP_NUM_REGIONS; region++) begin: gen_matchmode
    a_matchmode: assert property (
      csr_pmp_i.cfg[region].mode inside {
        PMP_MODE_OFF,
        PMP_MODE_TOR,
        PMP_MODE_NA4,
        PMP_MODE_NAPOT
      }
    );
  end endgenerate

  generate if (PMP_NUM_REGIONS > 0) begin : gen_pmp_assert
    // Check output vs model
    a_accept_only_legal : assert property (
      (pmp_req_err_o === 1'b0) |-> match_status.is_access_allowed
    );

    a_deny_only_illegal : assert property (
      pmp_req_err_o |-> (match_status.is_access_allowed === 1'b0)
    );

    // Assert that only one (or none) valid access reason can exist for any given access
    a_unique_access_allowed_reason: assert property (
      $countones(match_status.val_access_allowed_reason) <= 1
    );

    // Validate privilege level
    a_privmode: assert property (
      priv_lvl_i inside {
        PRIV_LVL_M,
        PRIV_LVL_U
      }
    );

    // Validate access type
    a_req_type: assert property (
      pmp_req_type_i inside {
        PMP_ACC_READ,
        PMP_ACC_WRITE,
        PMP_ACC_EXEC
      }
    );
    // SMEPMP 2b: When mseccfg.RLB is 0 and pmpcfg.L is 1 in any rule or entry (including disabled entries), then
    // mseccfg.RLB remains 0 and any further modifications to mseccfg.RLB are ignored until a PMP reset.
    //
    // In other words: mseccfg.RLB = 0 and pmpcfg.L = 1 in any rule or entry (including disabled),
    // mseccfg.RLB remains 0 and does not change until PMP reset
    a_rlb_never_fall_while_locked: assert property (
      csr_pmp_i.mseccfg.rlb === 1'b0 && match_status.is_any_locked |=>
        $stable(csr_pmp_i.mseccfg.rlb)
    );

    // SMEPMP 3: On mseccfg we introduce a field in bit 1 called Machine Mode Whitelist Policy (mseccfg.MMWP).
    // This is a sticky bit, meaning that once set it cannot be unset until a PMP reset.
    a_mmwp_never_fall_until_reset: assert property (
      csr_pmp_i.mseccfg.mmwp === 1'b1 |=>
        $stable(csr_pmp_i.mseccfg.mmwp)
    );

    // SMEPMP 4: On mseccfg we introduce a field in bit 0 called Machine Mode Lockdown (mseccfg.MML). This is a
    // sticky bit, meaning that once set it cannot be unset until a PMP reset.
    a_mml_never_fall_until_reset: assert property (
      csr_pmp_i.mseccfg.mml === 1'b1 |=>
        $stable(csr_pmp_i.mseccfg.mml)
    );

    // U-mode fails if no match
    a_nomatch_umode_fails: assert property (
      priv_lvl_i == PRIV_LVL_U && match_status.is_matched == 1'b0 |->
        pmp_req_err_o
    );

    // M-mode fails if: no match, and "mseccfg.MMWP"
    a_nomatch_mmode_mmwp_fails: assert property (
      (priv_lvl_i == PRIV_LVL_M)  &&
      !match_status.is_matched  &&
      csr_pmp_i.mseccfg.mmwp
      |->
      pmp_req_err_o
    );

    // U-mode or L=1 succeed only if RWX
    a_uorl_onlyif_rwx: assert property (
      ( priv_lvl_i == PRIV_LVL_U || match_status.is_matched == 1'b1 ) && !pmp_req_err_o |->
        match_status.is_rwx_ok
    );

    // After a match, LRWX determines access
    a_lrwx_aftermatch: assert property (
      match_status.is_matched == 1'b1 && !pmp_req_err_o |->
        match_status.is_rwx_ok
    );

    // SMEPMP 1: The reset value of mseccfg is implementation-specific, otherwise if backwards
    // compatibility is a requirement it should reset to zero on hard reset.
    a_mseccfg_reset_val: assert property (
      $rose(rst_n) |-> csr_pmp_i.mseccfg === MSECCFG_RESET_VAL
    );
  end endgenerate

  // Denied accesses don't reach the bus, or don't retire (instr-side)
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
    );
  end

  // Denied accesses don't reach the bus (data-side)
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
    );
    // TODO:silabs-robin  Add covers, or get reviews, and become convinced this is "bullet proof".
  end

endmodule : uvmt_cv32e40s_pmp_assert

`default_nettype wire
