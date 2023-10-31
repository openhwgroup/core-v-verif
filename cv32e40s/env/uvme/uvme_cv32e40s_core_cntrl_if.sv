/**
 * Quasi-static core control signals.
 */
interface uvme_cv32e40s_core_cntrl_if_t
    import uvm_pkg::*;
    import cv32e40s_pkg::*;
    ();

    logic        clk;
    logic        fetch_en;
    logic        wu_wfe;

    logic        scan_cg_en;
    logic [31:0] boot_addr;
    logic [31:0] mtvec_addr;
    logic [31:0] dm_halt_addr;
    logic [31:0] dm_exception_addr;
    logic [31:0] nmi_addr;
    logic [31:0] mhartid;
    logic [3:0]  mimpid_patch;

    logic [31:0] num_mhpmcounters;
    `ifndef FORMAL
    pma_cfg_t pma_cfg[];
    `else
    pma_cfg_t pma_cfg[16];
    `endif
    cv32e40s_pkg::b_ext_e b_ext;

    // Testcase asserts this to load memory (not really a core control signal)
    logic        load_instr_mem;

  clocking drv_cb @(posedge clk);
    output fetch_en;
    output wu_wfe;
  endclocking : drv_cb

endinterface : uvme_cv32e40s_core_cntrl_if_t
