`default_nettype none


module  uvmt_cv32e40s_umode_cov
  import cv32e40s_rvfi_pkg::*;
(
  input wire  clk_i,
  input wire  rst_ni,

  input wire         rvfi_valid,
  input rvfi_trap_t  rvfi_trap,
  input wire [31:0]  rvfi_insn,
  input wire [31:0]  rvfi_rs1_rdata
);


  // Helper Typedefs

  typedef struct packed {
    logic [31:13]  dontcare1;
    logic [12:11]  mpp;
    logic [10: 0]  dontcare0;
  } mstatus_t;


  // Helper Signals

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


  // Cover: SupportedLevels & MppValues

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


endmodule : uvmt_cv32e40s_umode_cov


`default_nettype wire
