`default_nettype none


module  uvmt_cv32e40s_umode_cov
  import cv32e40s_rvfi_pkg::*;
(
  input wire  clk_i,
  input wire  rst_ni,

  input wire         rvfi_valid,
  input rvfi_trap_t  rvfi_trap,
  input wire [31:0]  rvfi_insn,
  input wire [31:0]  rvfi_rs1_rdata,
  input wire [31:0]  rvfi_pc_rdata,
  input wire [ 1:0]  rvfi_mode,
  input wire [ 4:0]  rvfi_rd_addr,

  input wire         obi_iside_req,
  input wire         obi_iside_gnt,
  input wire [31:0]  obi_iside_addr,
  input wire [ 2:0]  obi_iside_prot
);
//TODO:silabs-robin  Only include any of this if "coverage_enabled"


  // Helper Definitions

  localparam int  MODE_U = 2'b 00;
  localparam int  MODE_M = 2'b 11;

  localparam int  EXC_ACCESFAULT =  1;
  localparam int  EXC_BUSFAULT   = 24;

  localparam int  CSRADDR_MISA     = 12'h 301;
  localparam int  CSRADDR_MSCRATCH = 12'h 340;
  localparam int  CSRADDR_MSTATUS  = 12'h 300;
  localparam int  CSRADDR_MEDELEG  = 12'h 302;
  localparam int  CSRADDR_MIDELEG  = 12'h 303;

  typedef struct packed {
    logic [31:13]  dontcare1;
    logic [12:11]  mpp;
    logic [10: 0]  dontcare0;
  } mstatus_t;


  // Helper Signals

  wire  is_rvfi_instrrevoked =
    rvfi_trap.exception  &&
    (rvfi_trap.exception_cause inside {EXC_ACCESFAULT, EXC_BUSFAULT});

  wire  is_rvfi_valid_norevoke =
    rvfi_valid  &&
    !is_rvfi_instrrevoked;

  wire  is_rvfi_csr_instr =
    is_rvfi_valid_norevoke                        &&
    (rvfi_insn[ 6: 0] == 7'b 1110011)             &&
    (rvfi_insn[14:12] inside {1, 2, 3, 5, 6, 7})  ;

  wire  is_rvfi_csr_instr_read =
    is_rvfi_csr_instr  &&
    (
      rvfi_rd_addr  ||                   // "rd != x0"
      !(rvfi_insn[14:12] inside {1, 5})  // ...or not "csrrw[i]"
    );

  wire  is_rvfi_csr_instr_write =
    is_rvfi_csr_instr  &&
    (
      rvfi_insn[19:15]  ||              // "rs1 != x0/0"
      (rvfi_insn[14:12] inside {1, 5})  // ...or "csrrw[i]"
    );

  wire  is_rvfi_notrap_csrrw_mstatus =
    rvfi_valid                         &&
    !rvfi_trap                         &&
    (rvfi_insn[ 6: 0] == 7'b 1110011)  &&  // op
    (rvfi_insn[14:12] == 1'd 1)        &&  // funct3
    (rvfi_insn[31:20] == 12'h 300)     ;   // csr

  wire mstatus_t  have_rvfi_csrrw_attempted_wdata =
    rvfi_rs1_rdata;

  wire  is_rvfi_notrap_mret =
    rvfi_valid  &&
    !rvfi_trap  &&
    (rvfi_insn == 32'b 0011000_00010_00000_000_00000_1110011);

  wire  is_obi_iside_aphase =
    obi_iside_req  &&
    obi_iside_gnt  ;


  // Helper Sequences

  sequence  seq_next_rvfi_valid;
    1  ##1
    (rvfi_valid [->1])
    ;
  endsequence : seq_next_rvfi_valid

  sequence  seq_write_mpp (mode);
    is_rvfi_notrap_csrrw_mstatus  &&
    (have_rvfi_csrrw_attempted_wdata.mpp == mode)
    ;
  endsequence : seq_write_mpp


  // Cover: "SupportedLevels" & "MppValues"

  for (genvar mode = 0; mode <= 3; mode++) begin : gen_try_goto_mode
    cov_try_goto_mode: cover property (
      seq_write_mpp (mode)  ##0
      // TODO can have non-mpp-changing retires in-between
      seq_next_rvfi_valid   ##0
      is_rvfi_notrap_mret
    );

    // Plus some helper covers to be sure
    cov_write_mpp: cover property (
      seq_write_mpp (mode)
    );
    cov_notrap_mret: cover property (
      is_rvfi_notrap_mret
    );
  end : gen_try_goto_mode


  // Cover: "Refetch"

  sequence  seq_refetch_as (logic [1:0]  mode);
    logic [31:0]  addr;

    is_obi_iside_aphase            ##0
    (obi_iside_prot[2:1] != mode)  ##0
    (1, addr = obi_iside_addr)

    // TODO:silabs-robin  Will be resource-hungry in sim?
    // TODO:silabs-robin  Cover with 0/1/2 other fetches between?
    // TODO:silabs-robin  No rvfi_valid on same addr before final one?

    ##1
    (is_obi_iside_aphase [->1])    ##0
    (obi_iside_prot[2:1] == mode)  ##0
    (obi_iside_addr == addr)
    // TODO?  ((is_obi_iside_aphase && (obi_iside_addr == addr)) [->1])  ##0

    ##5  // (Traverse pipeline)
    (rvfi_valid [->1])  ##0
    (rvfi_pc_rdata == addr)
    // TODO?  ((rvfi_valid && (rvfi_pc_rdata == addr)) [->1])
    ;
  endsequence : seq_refetch_as

  cov_refetch_as_umode: cover property (seq_refetch_as(MODE_U));
  cov_refetch_as_mmode: cover property (seq_refetch_as(MODE_M));
  // TODO:silabs-robin  Cover with/without trap


  // Covergroup, mixed features

  covergroup  cg @(posedge clk_i);
    // TODO:silabs-robin  "InstrProt" and "DataProt"?

    cp_mode: coverpoint  rvfi_mode  iff (rvfi_valid) {
      bins  mmode = {MODE_M};
      bins  umode = {MODE_U};
    }

    /* TODO:silabs-robin  Conditionally include if "cov_enable_pedantic"
    cp_csraddr: coverpoint  rvfi_insn[31:20]  iff (is_rvfi_csr_instr) {
      bins  addr[4096] = {[0:$]};
    }
    */

    cp_csrreadwrite: coverpoint
      {is_rvfi_csr_instr_read, is_rvfi_csr_instr_write}
      iff (is_rvfi_csr_instr)
    {
      bins  r  = {2'b 10};
      bins  w  = {2'b 01};
      // bins  rw = {2'b 11};  // Enable for thoroughness
    }

    cp_umodecsrs: coverpoint  rvfi_insn[31:20]  iff (is_rvfi_csr_instr) {
      bins  misa     = {CSRADDR_MISA};
      bins  mscratch = {CSRADDR_MSCRATCH};
      bins  mstatus  = {CSRADDR_MSTATUS};
      bins  medeleg  = {CSRADDR_MEDELEG};
      bins  mideleg  = {CSRADDR_MIDELEG};
    }

    /* TODO:silabs-robin  Conditionally include if "cov_enable_pedantic"
    x_mode_csraddr: cross cp_mode, cp_csraddr;
    */

    // "MisaU" & "MisaN", "MscratchReliable"
    x_csrreadwrite_mode_umodecsrs:
      cross cp_csrreadwrite, cp_mode, cp_umodecsrs;
  endgroup

  cg  cg_inst = new;


endmodule : uvmt_cv32e40s_umode_cov


`default_nettype wire
