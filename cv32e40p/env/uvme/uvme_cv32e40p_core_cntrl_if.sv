// Copyright 2022 Dolphin Design
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

/**
 * Quasi-static core control signals.
 */
interface uvme_cv32e40p_core_cntrl_if
    import uvm_pkg::*;
    import cv32e40p_pkg::*;
    ();

    logic        clk;
    logic        fetch_en;

    logic        scan_cg_en;
    logic [31:0] boot_addr;
    logic [31:0] mtvec_addr;
    logic [31:0] dm_halt_addr;
    logic [31:0] dm_exception_addr;
    logic [31:0] mhartid;

    logic [31:0] num_mhpmcounters;
    // pma_cfg_t pma_cfg[]; TODO
    // cv32e40p_pkg::b_ext_e b_ext; TODO

    // Testcase asserts this to load memory (not really a core control signal)
    logic        load_instr_mem;

  clocking drv_cb @(posedge clk);
    output fetch_en;
  endclocking : drv_cb

endinterface : uvme_cv32e40p_core_cntrl_if
