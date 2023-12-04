// Copyright 2022 Silicon Labs, Inc.
// Copyright 2022 OpenHW Group
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
// See the License for the specific language governing permissions and
// limitations under the License.


`default_nettype none


module  uvmt_cv32e40s_umode_cov
  import uvma_rvfi_pkg::*;
#(
  int ILEN = DEFAULT_ILEN,
  int XLEN = DEFAULT_XLEN
)(
  input wire  clk_i,
  input wire  rst_ni,

  input wire              rvfi_valid,
  input wire rvfi_trap_t  rvfi_trap,
  input wire rvfi_intr_t  rvfi_intr,
  input wire [31:0]       rvfi_insn,
  input wire [31:0]       rvfi_rs1_rdata,
  input wire [31:0]       rvfi_pc_rdata,
  input wire [ 1:0]       rvfi_mode,
  input wire [ 4:0]       rvfi_rd_addr,
  input wire              rvfi_dbg_mode,
  input wire [63:0]       rvfi_order,
  input wire [(NMEM*XLEN/8)-1:0] rvfi_mem_rmask,
  input wire [(NMEM*XLEN/8)-1:0] rvfi_mem_wmask,

  input wire [31:0]  rvfi_csr_mstatus_rdata,
  input wire [31:0]  rvfi_csr_mstatus_rmask,
  input wire [31:0]  rvfi_csr_dcsr_rdata,
  input wire [31:0]  rvfi_csr_dcsr_rmask,

  input wire         obi_iside_req,
  input wire         obi_iside_gnt,
  input wire [31:0]  obi_iside_addr,
  input wire [ 2:0]  obi_iside_prot
);


  // Clock & Reset

  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;


  // Helper Definitions

  localparam bit [1:0]  MODE_U = 2'b 00;
  localparam bit [1:0]  MODE_M = 2'b 11;

  localparam bit [11:0]  CSRADDR_MISA       = 12'h 301;
  localparam bit [11:0]  CSRADDR_MSCRATCH   = 12'h 340;
  localparam bit [11:0]  CSRADDR_MSTATUS    = 12'h 300;
  localparam bit [11:0]  CSRADDR_MEDELEG    = 12'h 302;
  localparam bit [11:0]  CSRADDR_MIDELEG    = 12'h 303;
  localparam bit [11:0]  CSRADDR_MCOUNTEREN = 12'h 306;

  localparam int  EXC_ACCESFAULT =  1;
  localparam int  EXC_BUSFAULT   = 24;

  typedef struct packed {
    logic [31:18]  dontcare2;
    logic [17:17]  mprv;
    logic [16:13]  dontcare1;
    logic [12:11]  mpp;
    logic [10: 0]  dontcare0;
  } mstatus_t;

  typedef struct packed {
    logic [31:2]  dontcare;
    logic [ 1:0]  prv;
  } dcsr_t;


  // Helper Signals

  logic  is_rvfi_instrrevoked;
  assign is_rvfi_instrrevoked =
    rvfi_trap.exception  &&
    (rvfi_trap.exception_cause inside {EXC_ACCESFAULT, EXC_BUSFAULT});

  logic  is_rvfi_valid_norevoke;
  assign is_rvfi_valid_norevoke =
    rvfi_valid  &&
    !is_rvfi_instrrevoked;

  logic  is_rvfi_csr_instr;
  assign is_rvfi_csr_instr =
    is_rvfi_valid_norevoke                        &&
    (rvfi_insn[ 6: 0] == 7'b 1110011)             &&
    (rvfi_insn[14:12] inside {1, 2, 3, 5, 6, 7})  ;

  logic  is_rvfi_csr_instr_read;
  assign is_rvfi_csr_instr_read =
    is_rvfi_csr_instr  &&
    (
      rvfi_rd_addr  ||                   // "rd != x0"
      !(rvfi_insn[14:12] inside {1, 5})  // ...or not "csrrw[i]"
    );

  logic  is_rvfi_csr_instr_write;
  assign is_rvfi_csr_instr_write =
    is_rvfi_csr_instr  &&
    (
      rvfi_insn[19:15]  ||              // "rs1 != x0/0"
      (rvfi_insn[14:12] inside {1, 5})  // ...or "csrrw[i]"
    );

  logic  is_rvfi_notrap_csrrw;
  assign is_rvfi_notrap_csrrw =
    rvfi_valid                         &&
    !rvfi_trap                         &&
    (rvfi_insn[ 6: 0] == 7'b 1110011)  &&  // op
    (rvfi_insn[14:12] == 1'd 1)        ;   // funct3

  logic  is_rvfi_notrap_csrrw_mstatus;
  assign is_rvfi_notrap_csrrw_mstatus =
    is_rvfi_notrap_csrrw           &&
    (rvfi_insn[31:20] == 12'h 300) ;   // csr

  logic  is_rvfi_notrap_csrrw_dcsr;
  assign is_rvfi_notrap_csrrw_dcsr =
    is_rvfi_notrap_csrrw           &&
    (rvfi_insn[31:20] == 12'h 7B0) ;   // csr

  mstatus_t  have_rvfi_csrrw_wdata_mstatus;
  assign     have_rvfi_csrrw_wdata_mstatus =
    rvfi_rs1_rdata;

  dcsr_t  have_rvfi_csrrw_wdata_dcsr;
  assign  have_rvfi_csrrw_wdata_dcsr =
    rvfi_rs1_rdata;

  mstatus_t  have_rvfi_mstatus_rdata;
  assign     have_rvfi_mstatus_rdata =
    (rvfi_csr_mstatus_rdata & rvfi_csr_mstatus_rmask);

  dcsr_t  have_rvfi_dcsr_rdata;
  assign  have_rvfi_dcsr_rdata =
    (rvfi_csr_dcsr_rdata & rvfi_csr_dcsr_rmask);

  logic  is_rvfi_notrap_mret;
  assign is_rvfi_notrap_mret =
    rvfi_valid  &&
    !rvfi_trap  &&
    (rvfi_insn == 32'b 0011000_00010_00000_000_00000_1110011);

  logic  is_rvfi_notrap_dret;
  assign is_rvfi_notrap_dret =
    rvfi_valid  &&
    !rvfi_trap  &&
    (rvfi_insn == 32'h 7b20_0073);

  logic  is_obi_iside_aphase;
  assign is_obi_iside_aphase =
    obi_iside_req  &&
    obi_iside_gnt  ;

  var [1:0]  was_rvfi_mode;
  always @(posedge clk_i) begin
    if (rvfi_valid) begin
      was_rvfi_mode <= rvfi_mode;
    end
  end

  var [63:0]  clk_cnt;
  always @(posedge clk_i, negedge rst_ni) begin
    if (rst_ni == 0) begin
      clk_cnt <= 64'd 1;
    end else if (clk_cnt != '1) begin
      clk_cnt <= clk_cnt + 64'd 1;
    end
  end


  // Helper Sequences

  sequence  seq_next_rvfi_valid;
    1  ##1
    (rvfi_valid [->1])
    ;
  endsequence : seq_next_rvfi_valid

  sequence  seq_write_mstatus_mpp (mode);
    is_rvfi_notrap_csrrw_mstatus  &&
    (have_rvfi_csrrw_wdata_mstatus.mpp == mode)
    ;
  endsequence : seq_write_mstatus_mpp

  sequence  seq_write_dcsr_prv (mode);
    is_rvfi_notrap_csrrw_dcsr  &&
    (have_rvfi_csrrw_wdata_dcsr.prv == mode)
    ;
  endsequence : seq_write_dcsr_prv


  // Cover - vplan:SupportedLevels & vplan:MppValues

  for (genvar mode = 0; mode <= 3; mode++) begin : gen_try_goto_mode
    cov_try_goto_mode: cover property (
      seq_write_mstatus_mpp (mode)  ##0
      seq_next_rvfi_valid           ##0
      is_rvfi_notrap_mret
    );

    // Plus some helper covers to be sure
    cov_write_mpp: cover property (
      seq_write_mstatus_mpp (mode)
    );
    cov_notrap_mret: cover property (
      is_rvfi_notrap_mret
    );
  end : gen_try_goto_mode


  // Cover - vplan:PrvSupported

  for (genvar mode = 0; mode <= 3; mode++) begin : gen_try_set_prv
    cov_try_set_prv: cover property (
      seq_write_dcsr_prv (mode)
    );
  end : gen_try_set_prv


  // Cover - vplan:Refetch

  sequence  seq_refetch_as (logic [1:0]  mode);
    logic [31:0]  addr;

    is_obi_iside_aphase            ##0
    (obi_iside_prot[2:1] != mode)  ##0
    (1, addr = obi_iside_addr)

    ##1
    (is_obi_iside_aphase [->1])    ##0
    (obi_iside_prot[2:1] == mode)  ##0
    (obi_iside_addr == addr)

    ##5  // (Traverse pipeline)
    (rvfi_valid [->1])       ##0
    (rvfi_pc_rdata == addr)  ##0
    (rvfi_mode == mode)
    ;
  endsequence : seq_refetch_as

  cov_refetch_as_umode_notrap: cover property (
    seq_refetch_as(MODE_U) ##0 !rvfi_trap
  );
  cov_refetch_as_mmode_notrap: cover property (
    seq_refetch_as(MODE_M) ##0 !rvfi_trap
  );
  cov_refetch_as_umode_trap: cover property (
    seq_refetch_as(MODE_U) ##0  rvfi_trap.exception
  );
  cov_refetch_as_mmode_trap: cover property (
    seq_refetch_as(MODE_M) ##0  rvfi_trap.exception
  );


  // Cover - vplan:TrapsMmode  (Helper Covers)

  cov_umode_intr: cover property (
    rvfi_valid                 &&
    (was_rvfi_mode == MODE_U)  &&
    rvfi_intr.interrupt        &&
    (rvfi_order > 64'd 1)
  );

  `ifdef FORMAL  // (Don't need this specificity in sim)
    cov_umode_intr_32: cover property (
      rvfi_valid                 &&
      (was_rvfi_mode == MODE_U)  &&
      rvfi_intr.interrupt        &&
      (rvfi_order > 64'd 1)      &&
      (clk_cnt == 32)
    );
  `endif

  cov_umode_notrap: cover property (
    rvfi_valid             &&
    (rvfi_mode == MODE_U)  &&
    !rvfi_trap
  );

  `ifdef FORMAL  // (Don't need this specificity in sim)
    cov_umode_notrap_25: cover property (
      rvfi_valid             &&
      (rvfi_mode == MODE_U)  &&
      !rvfi_trap             &&
      (clk_cnt == 25)
    );
  `endif


  // Cover - vplan:ResumeMprv  (Helper Covers)

  cov_umode_mprv: cover property (
    rvfi_valid                            &&
    have_rvfi_mstatus_rdata.mprv          &&
    (have_rvfi_dcsr_rdata.prv == MODE_U)  &&
    is_rvfi_notrap_dret
    ##1
    (rvfi_valid [->1])
  );


  // Covergroup, mixed features

  covergroup  cg  @(posedge clk_i);
    option.per_instance = 1;

    // Coverpoints

    cp_mode: coverpoint  rvfi_mode  iff (rvfi_valid) {
      bins  mmode = {MODE_M};
      bins  umode = {MODE_U};
    }

    `ifndef FORMAL
    cp_csraddr: coverpoint  rvfi_insn[31:20]  iff (is_rvfi_csr_instr) {
      bins  addr[4096] = {[0:$]};
    }
    `endif

    cp_csrreadwrite: coverpoint
      {is_rvfi_csr_instr_read, is_rvfi_csr_instr_write}
      iff (is_rvfi_csr_instr)
    {
      bins  r  = {2'b 10};
      bins  w  = {2'b 01};
      // bins  rw = {2'b 11};  // Enable for thoroughness
    }

    cp_umodecsrs: coverpoint  rvfi_insn[31:20]  iff (is_rvfi_csr_instr) {
      bins  misa       = {CSRADDR_MISA};
      bins  mscratch   = {CSRADDR_MSCRATCH};
      bins  mstatus    = {CSRADDR_MSTATUS};
      bins  medeleg    = {CSRADDR_MEDELEG};
      bins  mideleg    = {CSRADDR_MIDELEG};
      bins  mcounteren = {CSRADDR_MCOUNTEREN};
    }

    cp_mpp: coverpoint  have_rvfi_mstatus_rdata.mpp  iff (rvfi_valid) {
      bins  mmode = {MODE_M};
      bins  umode = {MODE_U};
    }

    cp_excint: coverpoint
      {rvfi_intr.exception, rvfi_intr.interrupt}  iff (rvfi_valid)
    {
      bins  exc  = {2'b 10};
      bins  intr = {2'b 01};
    }

    cp_prevmode: coverpoint
      was_rvfi_mode  iff (rvfi_valid && (rvfi_order > 1))
    {
      bins  mmode = {MODE_M};
      bins  umode = {MODE_U};
    }

    cp_dmode: coverpoint  rvfi_dbg_mode  iff (rvfi_valid) {
      bins  dmode  = {1'b 1};
      bins  normal = {1'b 0};
    }

    cp_loadstore: coverpoint
      {|rvfi_mem_rmask, |rvfi_mem_wmask}  iff (rvfi_valid)
    {
      bins  load  = {2'b 10};
      bins  store = {2'b 01};
      bins  none  = {2'b 00};
    }

    cp_mprv: coverpoint  have_rvfi_mstatus_rdata.mprv  iff (rvfi_valid) {
      bins  on  = {1'b 1};
      bins  off = {1'b 0};
    }

    cp_dret: coverpoint  is_rvfi_notrap_dret  iff (rvfi_valid) {
      bins  dret = {1'b 1};
    }

    cp_prv: coverpoint  have_rvfi_dcsr_rdata.prv  iff (rvfi_valid) {
      bins  mmode = {MODE_M};
      bins  umode = {MODE_U};
    }

    // Crosses

    // vplan:AccessLevel & vplan:IllegalAccess
    `ifndef FORMAL
    x_mode_csraddr: cross cp_mode, cp_csraddr;
    `endif

    // vlpan:MisaU & vplan:MisaN & vplan:MscratchReliable & vplan:MedelegMideleg
    x_csrreadwrite_mode_umodecsrs:
      cross cp_csrreadwrite, cp_mode, cp_umodecsrs;

    // vplan:TrapMpp
    x_mpp_excint: cross cp_mpp, cp_excint  iff (!rvfi_dbg_mode);

    // vplan:TrapsMmode
    x_prevmode_excint: cross cp_prevmode, cp_excint;

    // vplan:ExcecuteMmode  (in dmode)
    x_dmode_csrreadwrite: cross cp_dmode, cp_csrreadwrite;

    // vplan:ExcecuteMmode & vplan:ExcecuteMprven
    x_dmode_loadstore: cross cp_dmode, cp_loadstore;
    x_dmode_mprv:      cross cp_dmode, cp_mprv;
    x_dmode_mpp:       cross cp_dmode, cp_mpp;
    x_dmode_loadstore_mprv_mpp:
      cross cp_dmode, cp_loadstore, cp_mprv, cp_mpp
      iff (!rvfi_trap);

    // vplan:ResumeMprv
    x_dret_mprv_prv: cross cp_dret, cp_mprv, cp_prv;
  endgroup

  cg  cg_inst = new;


endmodule : uvmt_cv32e40s_umode_cov


`default_nettype wire
