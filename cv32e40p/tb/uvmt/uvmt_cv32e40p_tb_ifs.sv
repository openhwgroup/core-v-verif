//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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

// -----------------------------------------------------------------------------
// REFACTOR SUMMARY (Issue #2386)
// - Replaced internal reg/wire with logic where appropriate; port lists unchanged.
// - Introduced localparams for timing (clk_gen_if) and default addresses/counts
//   (core_cntrl_if) to remove magic literals.
// - Parameterized covergroup address bins via localparams to reduce duplication
//   and keep coverage intent consistent.
// - Fixed $sformatf format strings in report_step_compare (0d%0d -> %0d).
// - Corrected comment typos (duarion->duration, occured->occurred, affect->effect).
// - Isolated LFSR logic in a named always block; added short doc headers per
//   interface; standardized indentation and comment style.
// - No port, connectivity, or behavioral changes.
// -----------------------------------------------------------------------------

// This file specifies all interfaces used by the CV32E40P test bench (uvmt_cv32e40p_tb).
// Most interfaces support tasks to allow control by the ENV or test cases.

`ifndef __UVMT_CV32E40P_TB_IFS_SV__
`define __UVMT_CV32E40P_TB_IFS_SV__

// -----------------------------------------------------------------------------
// Clock and reset generation. Drives core_clock and core_reset_n with
// configurable period and reset assertion/deassertion timing.
// -----------------------------------------------------------------------------
interface uvmt_cv32e40p_clk_gen_if (output logic core_clock, output logic core_reset_n);

  import uvm_pkg::*;

  // Default timing (ps). TODO: drive from uvme_cv32e40p_* ENV CFG.
  localparam real DEFAULT_CLOCK_PERIOD_PS     = 1500.0;
  localparam real DEFAULT_RESET_DURATION_PS   = 7400.0;

  bit      start_clk                = 0;
  realtime core_clock_period        = DEFAULT_CLOCK_PERIOD_PS * 1ps;
  realtime reset_deassert_duration  = DEFAULT_RESET_DURATION_PS * 1ps;
  realtime reset_assert_duration   = DEFAULT_RESET_DURATION_PS * 1ps;

  /**
   * Generates clock and reset signals.
   * If reset_n comes up de-asserted (1'b1), wait a bit, then assert, then de-assert.
   * Otherwise, leave reset asserted, wait a bit, then de-assert.
   */
  initial begin
    core_clock   = 0;
    core_reset_n = 0;
    wait (start_clk);
    fork
      forever begin
        #(core_clock_period/2) core_clock = ~core_clock;
      end
      begin
        if (core_reset_n == 1'b1) #(reset_deassert_duration);
        core_reset_n = 1'b0;
        #(reset_assert_duration);
        core_reset_n = 1'b1;
      end
    join_none
  end

  /** Sets clock period in ps. */
  function static void set_clk_period(real clk_period);
    core_clock_period = clk_period * 1ps;
  endfunction : set_clk_period

  /** Triggers the generation of clk. */
  function static void start();
    start_clk = 1;
    `uvm_info("CLK_GEN_IF", "uvmt_cv32e40p_clk_gen_if.start() called", UVM_NONE)
  endfunction : start

endinterface : uvmt_cv32e40p_clk_gen_if

// -----------------------------------------------------------------------------
// Virtual peripheral status: tests_passed, tests_failed, exit_valid, exit_value.
// Driven by DUT WRAPPER memory-mapped virtual peripherals.
// -----------------------------------------------------------------------------
interface uvmt_cv32e40p_vp_status_if (
  output reg        tests_passed,
  output reg        tests_failed,
  output reg        exit_valid,
  output reg [31:0] exit_value
);

  import uvm_pkg::*;

  // TODO: X/Z checks
  initial begin
  end

endinterface : uvmt_cv32e40p_vp_status_if

// -----------------------------------------------------------------------------
// Quasi-static core control: fetch enable, boot/debug addresses, and load_instr_mem.
// Fetch is enabled via go_fetch(); LFSR toggles fetch_en after that for coverage.
// -----------------------------------------------------------------------------
interface uvmt_cv32e40p_core_cntrl_if (
  input               clk,
  output logic        fetch_en,
  output logic        pulp_clock_en,
  output logic        scan_cg_en,
  output logic [31:0] boot_addr,
  output logic [31:0] mtvec_addr,
  output logic [31:0] dm_halt_addr,
  output logic [31:0] dm_exception_addr,
  output logic [31:0] hart_id,
  output logic        debug_req,
  output logic        load_instr_mem
);

  import uvm_pkg::*;

  // Default quasi-static values (used before plusarg overrides).
  localparam logic [31:0] DEFAULT_BOOT_ADDR         = 32'h0000_0080;
  localparam logic [31:0] DEFAULT_MTVEC_ADDR       = 32'h0000_0000;
  localparam logic [31:0] DEFAULT_DM_HALT_ADDR     = 32'h1A11_0800;
  localparam logic [31:0] DEFAULT_DM_EXCEPTION_ADDR = 32'h1A11_1000;
  localparam logic [31:0] DEFAULT_HART_ID           = 32'h0000_0000;
  localparam int         GO_FETCH_DELAY_CYCLES     = 10;

  // Address bin ranges for coverage (shared across coverpoints).
  localparam logic [31:0] ADDR_BIN_LOW_MIN  = 32'h0000_0000;
  localparam logic [31:0] ADDR_BIN_LOW_MAX  = 32'h0000_FFFF;
  localparam logic [31:0] ADDR_BIN_MED_MIN  = 32'h0001_0000;
  localparam logic [31:0] ADDR_BIN_MED_MAX  = 32'hEFFF_FFFF;
  localparam logic [31:0] ADDR_BIN_HIGH_MIN = 32'hF000_0000;
  localparam logic [31:0] ADDR_BIN_HIGH_MAX = 32'hFFFF_FFFF;

  string       qsc_stat_str;  // Quasi-static control status string
  logic        fb;
  logic        lfsr_reset;
  logic [15:0] lfsr;

  covergroup core_cntrl_cg;
    // For CV32E40P, pulp_clock_en / scan_cg_en are tied to 0; bins left for future use.
    // pulp_clock_enable: coverpoint pulp_clock_en { bins enabled = {1'b1}; bins disabled = {1'b0}; }
    // scan_enable:       coverpoint scan_cg_en    { bins enabled = {1'b1}; bins disabled = {1'b0}; }
    boot_address: coverpoint boot_addr {
      bins low  = {[ADDR_BIN_LOW_MIN  : ADDR_BIN_LOW_MAX]};
      bins med  = {[ADDR_BIN_MED_MIN  : ADDR_BIN_MED_MAX]};
      bins high = {[ADDR_BIN_HIGH_MIN : ADDR_BIN_HIGH_MAX]};
    }
    mtvec_address: coverpoint mtvec_addr {
      bins low  = {[ADDR_BIN_LOW_MIN  : ADDR_BIN_LOW_MAX]};
      bins med  = {[ADDR_BIN_MED_MIN  : ADDR_BIN_MED_MAX]};
      bins high = {[ADDR_BIN_HIGH_MIN : ADDR_BIN_HIGH_MAX]};
    }
    debug_module_halt_address: coverpoint dm_halt_addr {
      bins low  = {[ADDR_BIN_LOW_MIN  : ADDR_BIN_LOW_MAX]};
      bins med  = {[ADDR_BIN_MED_MIN  : ADDR_BIN_MED_MAX]};
      bins high = {[ADDR_BIN_HIGH_MIN : ADDR_BIN_HIGH_MAX]};
    }
    debug_module_exception_address: coverpoint dm_exception_addr {
      bins low  = {[ADDR_BIN_LOW_MIN  : ADDR_BIN_LOW_MAX]};
      bins med  = {[ADDR_BIN_MED_MIN  : ADDR_BIN_MED_MAX]};
      bins high = {[ADDR_BIN_HIGH_MIN : ADDR_BIN_HIGH_MAX]};
    }
    hart_id: coverpoint hart_id {
      bins low  = {[ADDR_BIN_LOW_MIN  : ADDR_BIN_LOW_MAX]};
      bins med  = {[ADDR_BIN_MED_MIN  : ADDR_BIN_MED_MAX]};
      bins high = {[ADDR_BIN_HIGH_MIN : ADDR_BIN_HIGH_MAX]};
    }
  endgroup : core_cntrl_cg

  core_cntrl_cg core_cntrl_cg_inst = new();

  // TODO: randomize hart_id (should have no effect); randomize boot_addr/mtvec_addr
  //       in sync with test program start address.
  initial begin : quasi_static_controls
    lfsr_reset        = 1'b1;
    fetch_en          = 1'b0;
    debug_req         = 1'b0;
    pulp_clock_en     = 1'b0;
    scan_cg_en        = 1'b0;
    boot_addr         = DEFAULT_BOOT_ADDR;
    mtvec_addr        = DEFAULT_MTVEC_ADDR;
    dm_halt_addr      = DEFAULT_DM_HALT_ADDR;
    dm_exception_addr = DEFAULT_DM_EXCEPTION_ADDR;
    hart_id           = DEFAULT_HART_ID;

    if ($value$plusargs("mtvec_addr=0x%x", mtvec_addr)) begin
      string override;
      int    fh;
      override = $sformatf("--override root/cpu/mtvec=0x%08x", {mtvec_addr[31:8], 8'h01});
      fh       = $fopen("ovpsim.ic", "a");
      $fwrite(fh, " %s\n", override);
      $fclose(fh);
    end

    qsc_stat_str  =                $sformatf("\tpulp_clock_en     = %0d\n", pulp_clock_en);
    qsc_stat_str  = {qsc_stat_str, $sformatf("\tscan_cg_en        = %0d\n", scan_cg_en)};
    qsc_stat_str  = {qsc_stat_str, $sformatf("\tboot_addr         = %8h\n", boot_addr)};
    qsc_stat_str  = {qsc_stat_str, $sformatf("\tmtvec_addr        = %8h\n", mtvec_addr)};
    qsc_stat_str  = {qsc_stat_str, $sformatf("\tdm_halt_addr      = %8h\n", dm_halt_addr)};
    qsc_stat_str  = {qsc_stat_str, $sformatf("\tdm_exception_addr = %8h\n", dm_exception_addr)};
    qsc_stat_str  = {qsc_stat_str, $sformatf("\thart_id           = %8h\n", hart_id)};

    `uvm_info("CORE_CNTRL_IF", $sformatf("Quasi-static CORE control inputs:\n%s", qsc_stat_str), UVM_NONE)
  end

  clocking drv_cb @(posedge clk);
    output fetch_en;
  endclocking : drv_cb

  /** Drives fetch_en high; samples coverage and releases LFSR after delay. */
  task static go_fetch();
    drv_cb.fetch_en <= 1'b1;
    `uvm_info("CORE_CNTRL_IF", "uvmt_cv32e40p_core_cntrl_if.go_fetch() called", UVM_DEBUG)
    core_cntrl_cg_inst.sample();
    repeat (GO_FETCH_DELAY_CYCLES) @(posedge clk);
    lfsr_reset <= 1'b0;
  endtask : go_fetch

  /** Drives fetch_en low and resets LFSR. */
  function void stop_fetch();
    drv_cb.fetch_en <= 1'b0;
    lfsr_reset      <= 1'b1;
    `uvm_info("CORE_CNTRL_IF", "uvmt_cv32e40p_core_cntrl_if.stop_fetch() called", UVM_DEBUG)
  endfunction : stop_fetch

  // LFSR feedback and update: toggles fetch_en after initial assertion to show
  // core ignores fetch_en once running. TODO: make constrainable; remove DVT waiver.
  assign fb = !(lfsr[15] ^ lfsr[13] ^ lfsr[12] ^ lfsr[10]);

  always @(posedge clk) begin : lfsr_update
    if (lfsr_reset) begin
      lfsr <= $urandom(); //@DVT_LINTER_WAIVER "MT20210811_2" disable SVTB.29.1.3.1
    end else begin
      lfsr            <= {lfsr[14:0], fb};
      drv_cb.fetch_en <= lfsr[15];
    end
  end

endinterface : uvmt_cv32e40p_core_cntrl_if

// -----------------------------------------------------------------------------
// Core status inputs: core_busy and security level (sec_lvl).
// -----------------------------------------------------------------------------
interface uvmt_cv32e40p_core_status_if (
  input  wire        core_busy,
  input  logic       sec_lvl
);

  import uvm_pkg::*;

endinterface : uvmt_cv32e40p_core_status_if

// -----------------------------------------------------------------------------
// ISA coverage: ISS wrapper drives ins and fires ins_valid for coverage collection.
// -----------------------------------------------------------------------------
interface uvmt_cv32e40p_isa_covg_if;

  import uvm_pkg::*;
  import uvme_cv32e40p_pkg::*;

  event ins_valid;
  ins_t ins;

endinterface : uvmt_cv32e40p_isa_covg_if

// -----------------------------------------------------------------------------
// Step-and-compare: events and state for ISS vs RTL comparison.
// Xcelium does not support event types in the module port list.
// -----------------------------------------------------------------------------
interface uvmt_cv32e40p_step_compare_if;

  import uvm_pkg::*;

  // From RTL riscv_tracer.sv
  typedef struct {
    logic [ 5:0] addr;
    logic [31:0] value;
  } reg_t;

  event        ovp_cpu_valid;       // Instruction successfully retired (ISS)
  event        ovp_cpu_trap;        // Exception occurred (ISS)
  event        ovp_cpu_halt;        // Halt occurred (ISS)
  bit   [31:0] ovp_cpu_PCr;
  logic [31:0] ovp_cpu_GPR[32];
  bit          ovp_cpu_state_idle;
  bit          ovp_cpu_state_stepi;
  bit          ovp_cpu_state_stop;
  bit          ovp_cpu_state_cont;

  event        riscv_retire;         // RTL retire
  event        riscv_trap;          // RTL took a trap
  event        riscv_halt;          // RTL took a halt

  logic [31:0]        insn_pc;
  logic [31:0][31:0]  riscy_GPR;
  logic               deferint_prime;
  logic               deferint_prime_ack;

  int num_pc_checks;
  int num_gpr_checks;
  int num_csr_checks;

  /** Report step-and-compare checker counts at end of simulation. */
  function void report_step_compare();
    if (num_pc_checks > 0) begin
      `uvm_info("step_compare", $sformatf("Checked PC %0d times", num_pc_checks), UVM_LOW)
    end else begin
      `uvm_error("step_compare", "PC was checked 0 times!")
    end
    if (num_gpr_checks > 0) begin
      `uvm_info("step_compare", $sformatf("Checked GPR %0d times", num_gpr_checks), UVM_LOW)
    end else begin
      `uvm_error("step_compare", "GPR was checked 0 times!")
    end
    if (num_csr_checks > 0) begin
      `uvm_info("step_compare", $sformatf("Checked CSR %0d times", num_csr_checks), UVM_LOW)
    end else begin
      `uvm_error("step_compare", "CSR was checked 0 times!")
    end
  endfunction : report_step_compare

endinterface : uvmt_cv32e40p_step_compare_if

// -----------------------------------------------------------------------------
// Debug and coverage assertions: internal core signals for SVA and covergroups.
// -----------------------------------------------------------------------------
interface uvmt_cv32e40p_debug_cov_assert_if
  import cv32e40p_pkg::*;
(
  input  clk_i,
  input  rst_ni,

  input         fetch_enable_i,

  input  [31:0] irq_i,
  input         irq_ack_o,
  input  [4:0]  irq_id_o,
  input  [31:0] mie_q,

  input         if_stage_instr_rvalid_i,
  input  [31:0] if_stage_instr_rdata_i,

  input         id_stage_instr_valid_i,
  input  [31:0] id_stage_instr_rdata_i,
  input         id_stage_is_compressed,
  input  [31:0] id_stage_pc,
  input  [31:0] if_stage_pc,
  input         is_decoding,
  input         id_valid,
  input  wire   ctrl_state_e ctrl_fsm_cs,
  input         illegal_insn_i,
  input         illegal_insn_q,
  input         ecall_insn_i,

  input  [31:0] boot_addr_i,

  input         debug_req_i,
  input         debug_mode_q,
  input  [31:0] dcsr_q,
  input  [31:0] depc_q,
  input  [31:0] depc_n,
  input  [31:0] dm_halt_addr_i,
  input  [31:0] dm_exception_addr_i,

  input  [5:0]  mcause_q,
  input  [31:0] mtvec,
  input  [31:0] mepc_q,
  input  [31:0] tdata1,
  input  [31:0] tdata2,
  input         trigger_match_i,

  input  [31:0] mcountinhibit_q,
  input  [63:0] mcycle,
  input  [63:0] minstret,
  input         inst_ret,

  input         core_sleep_o,

  input         fence_i,

  input         csr_access,
  input  [1:0]  csr_op,
  input  [1:0] csr_op_dec,
  input  [11:0] csr_addr,
  input         csr_we_int,

  output logic        is_wfi,
  output logic        in_wfi,
  output logic        dpc_will_hit,
  output logic        addr_match,
  output logic        is_ebreak,
  output logic        is_cebreak,
  output logic        is_dret,
  output logic        is_mulhsu,
  output logic [31:0] pending_enabled_irq,
  input              pc_set,
  input              branch_in_decode
);

  clocking mon_cb @(posedge clk_i);
    input #1step
      fetch_enable_i,
      irq_i,
      irq_ack_o,
      irq_id_o,
      mie_q,
      if_stage_instr_rvalid_i,
      if_stage_instr_rdata_i,
      id_stage_instr_valid_i,
      id_stage_instr_rdata_i,
      id_stage_is_compressed,
      id_stage_pc,
      if_stage_pc,
      ctrl_fsm_cs,
      illegal_insn_i,
      illegal_insn_q,
      ecall_insn_i,
      boot_addr_i,
      debug_req_i,
      debug_mode_q,
      dcsr_q,
      depc_q,
      depc_n,
      dm_halt_addr_i,
      dm_exception_addr_i,
      mcause_q,
      mtvec,
      mepc_q,
      tdata1,
      tdata2,
      trigger_match_i,
      fence_i,
      mcountinhibit_q,
      mcycle,
      minstret,
      inst_ret,
      core_sleep_o,
      csr_access,
      csr_op,
      csr_op_dec,
      csr_addr,
      is_wfi,
      in_wfi,
      dpc_will_hit,
      addr_match,
      is_ebreak,
      is_cebreak,
      is_dret,
      is_mulhsu,
      pending_enabled_irq,
      pc_set,
      branch_in_decode;
  endclocking : mon_cb

endinterface : uvmt_cv32e40p_debug_cov_assert_if

`endif // __UVMT_CV32E40P_TB_IFS_SV__
