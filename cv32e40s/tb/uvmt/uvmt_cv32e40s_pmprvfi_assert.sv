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


module uvmt_cv32e40s_pmprvfi_assert
  import cv32e40s_pkg::*;
  import support_pkg::*;
  import uvm_pkg::*;
  import uvma_rvfi_pkg::*;
  import uvma_rvfi_pkg::EXC_CAUSE_INSTR_BUS_FAULT;
  import uvma_rvfi_pkg::EXC_CAUSE_INSTR_INTEGRITY_FAULT;
  import uvmt_cv32e40s_base_test_pkg::*;
#(
  parameter int  PMP_GRANULARITY = 0,
  parameter int  PMP_NUM_REGIONS = 0
)(
  // Clock and Reset
  input wire  clk_i,
  input wire  rst_ni,

  //RVFI INSTR IF
  uvma_rvfi_instr_if_t    rvfi_if,
  // RVFI
  input wire              rvfi_valid,
  input wire [31:0]       rvfi_insn,
  input wire [ 1:0]       rvfi_mode,
  input wire rvfi_trap_t  rvfi_trap,
  input wire [ 4:0]       rvfi_rd_addr,
  input wire [31:0]       rvfi_rd_wdata,
  input wire [ 4:0]       rvfi_rs1_addr,
  input wire [31:0]       rvfi_rs1_rdata,
  input wire [31:0]       rvfi_pc_rdata,
  input wire [31:0]       rvfi_mem_addr,
  input wire [ 3:0]       rvfi_mem_wmask,
  input wire [ 3:0]       rvfi_mem_rmask,

  // RVFI CSR
  //(pmpcfg)
  input wire [PMP_MAX_REGIONS/4-1:0][31:0]  rvfi_csr_pmpcfg_rdata,
  input wire [PMP_MAX_REGIONS/4-1:0][31:0]  rvfi_csr_pmpcfg_wdata,
  input wire [PMP_MAX_REGIONS/4-1:0][31:0]  rvfi_csr_pmpcfg_wmask,
  //(pmpaddr)
  input wire [PMP_MAX_REGIONS-1:0]  [31:0]  rvfi_csr_pmpaddr_rdata,
  input wire [PMP_MAX_REGIONS-1:0]  [31:0]  rvfi_csr_pmpaddr_wdata,
  input wire [PMP_MAX_REGIONS-1:0]  [31:0]  rvfi_csr_pmpaddr_wmask,
  //(mseccfg[h])
  input wire [31:0]  rvfi_csr_mseccfg_rdata,
  input wire [31:0]  rvfi_csr_mseccfg_wdata,
  input wire [31:0]  rvfi_csr_mseccfg_wmask,
  input wire [31:0]  rvfi_csr_mseccfgh_rdata,
  input wire [31:0]  rvfi_csr_mseccfgh_wdata,
  input wire [31:0]  rvfi_csr_mseccfgh_wmask,
  //(mstatus)
  input wire [31:0]  rvfi_csr_mstatus_rdata,
  //(jvt)
  input wire [31:0]  rvfi_csr_jvt_rdata,

  // Debug
  input wire  rvfi_dbg_mode
);


  // Defines

  `define  max(a,b)  ((a) > (b) ? (a) : (b))

  string info_tag = "CV32E40S_PMPRVFI_ASSERT";

  localparam logic [1:0] MODE_U                = 2'b 00;
  localparam logic [1:0] MODE_M                = 2'b 11;
  localparam logic [2:0] DBG_TRIGGER           = 3'd 2;
  localparam int         NUM_CFG_REGS          = 16;
  localparam int         NUM_ADDR_REGS         = 64;
  localparam int         CSRADDR_FIRST_PMPCFG  = 12'h 3A0;
  localparam int         CSRADDR_FIRST_PMPADDR = 12'h 3B0;
  localparam int         CSRADDR_MSECCFG       = 12'h 747;

  typedef struct packed {
    logic  pc_lower;
    logic  pc_upper;
    logic  tablejump;
    logic  mret_pointer;
  } denial_reasons_t;


  // Defaults

  default clocking @(posedge clk_i); endclocking
  default disable iff !(rst_ni);


  // Helper signals

  wire  is_rvfi_csr_instr =
    rvfi_valid  &&
    (rvfi_insn[6:0] == 7'b 1110011)  &&
    (rvfi_insn[14:12] inside {1, 2, 3, 5, 6, 7});

  wire  is_rvfi_exception =
    rvfi_valid  &&
    rvfi_trap.trap  &&
    rvfi_trap.exception;

  wire  is_rvfi_exc_ill_instr =
    is_rvfi_exception  &&
    (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSTR);

  wire  is_rvfi_exc_instr_acc_fault =
    is_rvfi_exception  &&
    (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_ACC_FAULT);

  wire  is_rvfi_exc_instr_bus_fault=
    is_rvfi_exception  &&
    (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_BUS_FAULT);

  wire  is_rvfi_exc_instr_chksum_fault=
    is_rvfi_exception  &&
    (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_INTEGRITY_FAULT);

  wire  is_rvfi_dbg_trigger =
    rvfi_valid  &&
    rvfi_trap.debug  &&
    (rvfi_trap.debug_cause == DBG_TRIGGER);

  wire  is_rvfi_csr_read_instr =
    is_rvfi_csr_instr  &&
    rvfi_rd_addr;

  wire  is_rvfi_csr_write_instr =
    is_rvfi_csr_instr  &&
    !((rvfi_insn[13:12] inside {2'b 10, 2'b 11}) && !rvfi_rs1_addr);  // CSRRS/C[I] w/ rs1=x0/0

  wire [1:0]  rvfi_effective_mode =
    rvfi_csr_mstatus_rdata[17]      ?  // "mstatus.MPRV", modify privilege?
      rvfi_csr_mstatus_rdata[12:11] :  // "mstatus.MPP", loadstores act as if "mode==MPP"
      rvfi_mode;                       // Else, act as actual mode

  wire [31:0]  rvfi_mem_upperaddr =
    (rvfi_mem_rmask[3] || rvfi_mem_wmask[3]) ? (
      rvfi_mem_addr + 3
    ) : (
      (rvfi_mem_rmask[2] || rvfi_mem_wmask[2]) ? (
        rvfi_mem_addr + 2
      ) : (
        (rvfi_mem_rmask[1] || rvfi_mem_wmask[1]) ? (
          rvfi_mem_addr + 1
        ) : (
          rvfi_mem_addr
        )
      )
    );

  denial_reasons_t  denial_reasons;
  always_comb begin
    // WARNING: Some of these are approximations. Useful in some scenarios.

    denial_reasons.pc_lower = !match_status_instr.is_access_allowed;

    denial_reasons.pc_upper = (
      rvfi_if.is_split_instrtrans  &&
      !match_status_upperinstr.is_access_allowed
      //TODO:WARNING:silabs-robin Assert, low word match obi if no lower fault.
    );

    denial_reasons.tablejump = (
      rvfi_if.is_tablejump_raw  &&
      !match_status_jvt.is_access_allowed
    );

    denial_reasons.mret_pointer =
      rvfi_if.match_instr_raw(rvfi_if.INSTR_OPCODE_MRET, rvfi_if.INSTR_MASK_FULL);
  end

  logic  is_access_allowed;
  always_comb begin
    is_access_allowed =
      !denial_reasons.pc_lower  &&
      !denial_reasons.pc_upper;
      // Note: This is incomplete but useful. Lacks cm.jt, mret ptr, etc.
  end

  logic [31:0]  jvt_addr;
  always_comb begin
    jvt_addr = get_jvt_addr_f(rvfi_if.rvfi_insn, rvfi_csr_jvt_rdata);
  end

  pmp_csr_t  pmp_csr_rvfi_rdata;
  pmp_csr_t  pmp_csr_rvfi_wdata;
  pmp_csr_t  pmp_csr_rvfi_wmask;
  for (genvar i = 0; i < PMP_MAX_REGIONS; i++) begin: gen_pmp_csr_readout
    localparam  pmpcfg_reg_i    = i / 4;
    localparam  pmpcfg_field_hi = (8 * (i % 4)) + 7;
    localparam  pmpcfg_field_lo = (8 * (i % 4));

    assign  pmp_csr_rvfi_rdata.cfg[i]  = rvfi_csr_pmpcfg_rdata[pmpcfg_reg_i][pmpcfg_field_hi : pmpcfg_field_lo];
    assign  pmp_csr_rvfi_wdata.cfg[i]  = rvfi_csr_pmpcfg_wdata[pmpcfg_reg_i][pmpcfg_field_hi : pmpcfg_field_lo];
    assign  pmp_csr_rvfi_wmask.cfg[i]  = rvfi_csr_pmpcfg_wmask[pmpcfg_reg_i][pmpcfg_field_hi : pmpcfg_field_lo];

    assign  pmp_csr_rvfi_rdata.addr[i] = {rvfi_csr_pmpaddr_rdata[i], 2'b 00};
    assign  pmp_csr_rvfi_wdata.addr[i] = {rvfi_csr_pmpaddr_wdata[i], 2'b 00};
    assign  pmp_csr_rvfi_wmask.addr[i] = {rvfi_csr_pmpaddr_wmask[i], 2'b 00};
  end
  assign  pmp_csr_rvfi_rdata.mseccfg = rvfi_csr_mseccfg_rdata;
  assign  pmp_csr_rvfi_wdata.mseccfg = rvfi_csr_mseccfg_wdata;
  assign  pmp_csr_rvfi_wmask.mseccfg = rvfi_csr_mseccfg_wmask;


  // Helper models

  match_status_t  match_status_instr;
  match_status_t  match_status_data;
  match_status_t  match_status_upperinstr;
  match_status_t  match_status_upperdata;
  match_status_t  match_status_jvt;

  uvmt_cv32e40s_pmp_model #(
    .PMP_GRANULARITY  (PMP_GRANULARITY),
    .PMP_NUM_REGIONS  (PMP_NUM_REGIONS),
    .DM_REGION_START  (CORE_PARAM_DM_REGION_START),
    .DM_REGION_END    (CORE_PARAM_DM_REGION_END)
  ) model_instr_i (
    .clk   (clk_i),
    .rst_n (rst_ni),

    .csr_pmp_i      (pmp_csr_rvfi_rdata),
    .debug_mode     (rvfi_dbg_mode),
    .pmp_req_addr_i ({2'b 00, rvfi_pc_rdata}),
    .pmp_req_err_o  ('Z),
    .pmp_req_type_i (PMP_ACC_EXEC),
    .priv_lvl_i     (privlvl_t'(rvfi_mode)),

    .match_status_o (match_status_instr),

    .*
  );

  uvmt_cv32e40s_pmp_model #(
    .PMP_GRANULARITY  (PMP_GRANULARITY),
    .PMP_NUM_REGIONS  (PMP_NUM_REGIONS),
    .DM_REGION_START  (CORE_PARAM_DM_REGION_START),
    .DM_REGION_END    (CORE_PARAM_DM_REGION_END)
  ) model_data_i (
    .clk   (clk_i),
    .rst_n (rst_ni),

    .csr_pmp_i      (pmp_csr_rvfi_rdata),
    .debug_mode     (rvfi_dbg_mode),
    .pmp_req_addr_i ({2'b 00, rvfi_mem_addr}),  // TODO:WARNING:silabs-robin  Multi-op instructions
    .pmp_req_err_o  ('Z),
    .pmp_req_type_i (rvfi_if.is_store_instr ? PMP_ACC_WRITE : PMP_ACC_READ),
    .priv_lvl_i     (privlvl_t'(rvfi_effective_mode)),

    .match_status_o (match_status_data),

    .*
  );

  uvmt_cv32e40s_pmp_model #(
    .PMP_GRANULARITY  (PMP_GRANULARITY),
    .PMP_NUM_REGIONS  (PMP_NUM_REGIONS),
    .DM_REGION_START  (CORE_PARAM_DM_REGION_START),
    .DM_REGION_END    (CORE_PARAM_DM_REGION_END)
  ) model_upperinstr_i (
    .clk   (clk_i),
    .rst_n (rst_ni),

    .csr_pmp_i      (pmp_csr_rvfi_rdata),
    .debug_mode     (rvfi_dbg_mode),
    .pmp_req_addr_i ({2'b 00, rvfi_if.rvfi_pc_upperrdata}),
    .pmp_req_err_o  ('Z),
    .pmp_req_type_i (PMP_ACC_EXEC),
    .priv_lvl_i     (privlvl_t'(rvfi_mode)),

    .match_status_o (match_status_upperinstr),

    .*
  );

  uvmt_cv32e40s_pmp_model #(
    .PMP_GRANULARITY  (PMP_GRANULARITY),
    .PMP_NUM_REGIONS  (PMP_NUM_REGIONS),
    .DM_REGION_START  (CORE_PARAM_DM_REGION_START),
    .DM_REGION_END    (CORE_PARAM_DM_REGION_END)
  ) model_upperdata_i (
    .clk   (clk_i),
    .rst_n (rst_ni),

    .csr_pmp_i      (pmp_csr_rvfi_rdata),
    .debug_mode     (rvfi_dbg_mode),
    .pmp_req_addr_i ({2'b 00, rvfi_mem_upperaddr}),  // TODO:WARNING:silabs-robin  Multi-op instructions
    .pmp_req_err_o  ('Z),
    .pmp_req_type_i (rvfi_if.is_store_instr ? PMP_ACC_WRITE : PMP_ACC_READ),
    .priv_lvl_i     (privlvl_t'(rvfi_effective_mode)),

    .match_status_o (match_status_upperdata),

    .*
  );

  uvmt_cv32e40s_pmp_model #(
    .PMP_GRANULARITY (PMP_GRANULARITY),
    .PMP_NUM_REGIONS (PMP_NUM_REGIONS),
    .DM_REGION_START (CORE_PARAM_DM_REGION_START),
    .DM_REGION_END   (CORE_PARAM_DM_REGION_END)
  ) model_jvt_i (
    .clk   (clk_i),
    .rst_n (rst_ni),

    .csr_pmp_i      (pmp_csr_rvfi_rdata),
    .debug_mode     (rvfi_dbg_mode),
    .pmp_req_addr_i ({2'b 00, jvt_addr}),
    .pmp_req_err_o  ('Z),
    .pmp_req_type_i (PMP_ACC_EXEC),
    .priv_lvl_i     (privlvl_t'(rvfi_mode)),

    .match_status_o (match_status_jvt),

    .*
  );

  var [31:0]  clk_cnt;
  always @(posedge clk_i, negedge rst_ni) begin
    if (rst_ni == 0) begin
      clk_cnt <= 32'd 1;
    end else if (clk_cnt != '1) begin
      clk_cnt <= clk_cnt + 32'd 1;
    end
  end


  // Assertions:


  // PMP CSRs only accessible from M-mode  (vplan:Csrs:MmodeOnly)

  sequence seq_csrs_mmode_only_ante;
    is_rvfi_csr_instr      &&
    (rvfi_mode == MODE_U)  &&
    (rvfi_insn[31:20] inside {['h3A0 : 'h3EF], 'h747, 'h757})  //PMP regs
    ;
  endsequence : seq_csrs_mmode_only_ante

  a_csrs_mmode_only: assert property (
    seq_csrs_mmode_only_ante
    |->
    is_rvfi_exc_ill_instr          ||
    is_rvfi_exc_instr_bus_fault    ||
    is_rvfi_exc_instr_chksum_fault ||
    is_rvfi_exc_instr_acc_fault    ||
    is_rvfi_dbg_trigger
  ) else `uvm_error(info_tag, "PMP CSRs are illegal to access from umode");

  cov_csrs_mmode_only: cover property (
    // Want to see "the real cause" (ill exc) finishing this property
    seq_csrs_mmode_only_ante  ##0  is_rvfi_exc_ill_instr
  );


  // NAPOT, some bits read as ones, depending on G  (vplan:NapotOnes)

  if (PMP_GRANULARITY >= 2) begin: gen_napot_ones_g2
    //TODO:INFO:silabs-robin no magic numbers
    for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_napot_ones_i
      a_napot_ones: assert property (
        rvfi_valid  &&
        pmp_csr_rvfi_rdata.cfg[i].mode[1]
        |->
        (pmp_csr_rvfi_rdata.addr[i][PMP_GRANULARITY:2] == '1)
      ) else `uvm_error(info_tag, "NAPOT LSBs should read as all 1s");

      cov_napot_ones: cover property (
        // The ones doesn't have to extend past the required part
        rvfi_valid  &&
        pmp_csr_rvfi_rdata.cfg[i].mode[1]  &&
        (pmp_csr_rvfi_rdata.addr[i][PMP_GRANULARITY+1] != 1'b 1)
        // Note, this cover only checks part of what an assert could
      );
    end
  end


  // OFF/TOR, some bits read as zeros, depending on G  (vplan:AllZeros)

  if (PMP_GRANULARITY >= 1) begin: gen_all_zeros_g1
    for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_all_zeros_i
      a_all_zeros: assert property (
        rvfi_valid  &&
        (pmp_csr_rvfi_rdata.cfg[i].mode[1] === 1'b 0)
        |->
        (pmp_csr_rvfi_rdata.addr[i][PMP_GRANULARITY-1:0] == '0)
      ) else `uvm_error(info_tag, "TOR/OFF LSBs should read as all 0s");
    end
  end


  // Software-view on PMP CSRs matches RVFI-view  (Not a vplan item)

  for (genvar i = 0; i < NUM_CFG_REGS; i++) begin: gen_swview_cfg
    a_pmpcfg_swview: assert property (
      is_rvfi_csr_read_instr  &&
      (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPCFG + i))
      |->
      (rvfi_rd_wdata == rvfi_csr_pmpcfg_rdata[i])
    ) else `uvm_error(info_tag, "RVFI data should be 'observable via the ISA'");
  end

  for (genvar i = 0; i < NUM_ADDR_REGS; i++) begin: gen_swview_addr
    a_pmpaddr_swview: assert property (
      is_rvfi_csr_read_instr  &&
      (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPADDR + i))
      |->
      (rvfi_rd_wdata == rvfi_csr_pmpaddr_rdata[i])
    ) else `uvm_error(info_tag, "RVFI data should be 'observable via the ISA'");
  end


  // Software views do not change underlying register value  (vplan:StorageUnaffected)

  property p_storage_unaffected(i);
    logic [33:0] pmpaddr;
    accept_on (
      // (A new write resets this behavior)
      is_rvfi_csr_write_instr  &&
      (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPADDR + i))
    )
      rvfi_valid                                ##0
      pmp_csr_rvfi_rdata.cfg[i].mode[1]         ##0  // NAPOT/NA4
      (1, pmpaddr = pmp_csr_rvfi_rdata.addr[i])      // (Save pmpaddr)
      ##1
      (rvfi_valid [->1])  ##0
      (pmp_csr_rvfi_rdata.cfg[i].mode[1] == 1'b 0)  // TOR/OFF
      // (Could cover rdata being different than pmpaddr)
      ##1
      (rvfi_valid [->1])  ##0
      pmp_csr_rvfi_rdata.cfg[i].mode[1]  // NAPOT/NA4
    |->
    (pmp_csr_rvfi_rdata.addr[i] == pmpaddr);  // (Unchanged pmpaddr?)
    // Note, this _can_ be generalized more, but at a complexity/readability cost
  endproperty : p_storage_unaffected

  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_storage_unaffected
    a_storage_unaffected: assert property (
      p_storage_unaffected(i)
    ) else `uvm_error(info_tag, "PMP mode change shouldn't change addresses");
  end


  // Software-view can read the granularity level  (vplan:GranularityDetermination)

  if (PMP_NUM_REGIONS) begin: gen_granularity_determination
    a_granularity_determination: assert property (
      (is_rvfi_csr_instr && (rvfi_insn[14:12] == 3'b 001)) &&  // CSRRW instr,
      (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPADDR + 0))    &&  // to a "pmpaddr" CSR,
      ((rvfi_rs1_rdata == '1) && rvfi_rs1_addr)            &&  // writing all ones.
      (pmp_csr_rvfi_rdata.cfg[0] == '0)                    &&  // Related cfg is 0,
      (pmp_csr_rvfi_rdata.cfg[0+1] == '0)                  &&  // above cfg is 0.
      !rvfi_trap                                               // (Trap doesn't meddle.)
      ##1 (rvfi_valid [->1])
      |->
      (rvfi_csr_pmpaddr_rdata[0][31:PMP_GRANULARITY] == '1)  &&
      (
        (rvfi_csr_pmpaddr_rdata[0][`max(PMP_GRANULARITY-1, 0) : 0] == '0)  ^
        (PMP_GRANULARITY == 0)
      )
      // Note: _Can_ be generalized for all i
    ) else `uvm_error(info_tag, "SW-visible granularity must match G");
  end


  // Locking is forever  (vplan:LockingAndPrivmode:UntilReset)

  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_until_reset
    a_until_reset: assert property (
      pmp_csr_rvfi_rdata.cfg[i].lock  &&
      !pmp_csr_rvfi_rdata.mseccfg.rlb
      |->
      always pmp_csr_rvfi_rdata.cfg[i].lock
    ) else `uvm_error(info_tag, "locked configs must remain locked");
  end


  // Stickiness isn't effectuated before triggered  (vplan:LockingBypass:UntilReset)

  property  p_until_reset_notbefore(logic rlb);
    $rose(rst_ni)                                               ##0
    (rvfi_valid [->1])                                          ##0  // First retire
    (is_rvfi_csr_write_instr && (rvfi_insn[14:12] == 3'b 001))  ##0  // ..."csrrw"
    (rvfi_insn[31:20] == CSRADDR_MSECCFG)                       ##0  // ...to mseccfg
    !rvfi_trap                                                  ##0
    (rvfi_rs1_rdata[2] == rlb)                                       // (Write-attempt's data)
    |->
    pmp_csr_rvfi_wmask.mseccfg.rlb          &&  // Must attempt
    (pmp_csr_rvfi_wdata.mseccfg.rlb == rlb)     // Must succeed
    ;
  endproperty : p_until_reset_notbefore

  a_until_reset_notbefore_0: assert property (
    p_until_reset_notbefore(1'b 0)
  ) else `uvm_error(info_tag, "RLB must be changeable after reset");

  a_until_reset_notbefore_1: assert property (
    p_until_reset_notbefore(1'b 1)
  ) else `uvm_error(info_tag, "RLB must be changeable after reset");


  // Locked entries  (vplan:IgnoreWrites, vplan:IgnoreTor)

  // Locked entries, ignore pmpicfg/pmpaddri writes
  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_ignore_writes_notrap
    // "Ignored writes" don't trap:
    a_ignore_writes_notrap: assert property (
      is_rvfi_csr_write_instr  &&
      (rvfi_insn[31:20] inside {(CSRADDR_FIRST_PMPADDR + i), (CSRADDR_FIRST_PMPCFG + i)})  &&
      (pmp_csr_rvfi_rdata.cfg[i].lock && !pmp_csr_rvfi_rdata.mseccfg.rlb)  &&
      (rvfi_mode == MODE_M)
      |->
      (rvfi_trap.exception_cause != EXC_CAUSE_ILLEGAL_INSTR)
    ) else `uvm_error(info_tag, "writing to locked entries shouldn't except");
  end

  // Locked entries, ignore pmpicfg/pmpaddri writes
  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_ignore_writes_nochange
    // Ignored writes means stable data
    a_ignore_writes_nochange: assert property (
      rvfi_valid &&
      (pmp_csr_rvfi_rdata.cfg[i].lock && !pmp_csr_rvfi_rdata.mseccfg.rlb)
      |=>
      always (
        $stable(pmp_csr_rvfi_rdata.cfg[i])  &&
        $stable(pmp_csr_rvfi_rdata.addr[i])
      )
    ) else `uvm_error(info_tag, "locked entries must never change");
  end

  // Locked entries, ignore pmpicfg/pmpaddri writes
  for (genvar i = 0; i < PMP_NUM_REGIONS - 1; i++) begin: gen_not_ignore_writes_torcfg
    // We can see change even if "above config" is locked TOR
    property p_not_ignore_writes_torcfg;
      logic [7:0] cfg;

      rvfi_valid  &&
      pmp_csr_rvfi_rdata.cfg[i+1].lock  &&
      (pmp_csr_rvfi_rdata.cfg[i+1].mode == PMP_MODE_TOR)  ##0
      (1, cfg = pmp_csr_rvfi_rdata.cfg[i])

      ##1

      (rvfi_valid [->1])  ##0
      (pmp_csr_rvfi_rdata.cfg[i] != cfg)
      ;
    endproperty : p_not_ignore_writes_torcfg

    cov_not_ignore_writes_torcfg: cover property (
      p_not_ignore_writes_torcfg
    );
  end


  // Written cfgs are legal
  // (vplan:LegalRwx, vplan:Na4Unselectable, vplan:IgnoreWrites, vplan:ExecIgnored, vplan:ExecRlb, vplan:Warl)

  // Written cfg is written as expected
  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_cfg_expected
    wire pmpncfg_t  cfg_expected = rectify_cfg_write(pmp_csr_rvfi_rdata.cfg[i], rvfi_rs1_rdata[8*(i%4) +: 8]);

    sequence seq_cfg_expected_ante;
      (is_rvfi_csr_write_instr && (rvfi_insn[14:12] == 3'b 001))  &&  // "csrrw"
      (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPCFG + i/4))          &&  // ...to cfg's csr
      (!rvfi_trap)
      // Note, this doesn't check csrr(s/c)[i]
      ;
    endsequence : seq_cfg_expected_ante

    a_cfg_expected: assert property (
      seq_cfg_expected_ante
      |->
      (pmp_csr_rvfi_wmask.cfg[i] == 8'h FF)  &&  // Must write cfg
      (pmp_csr_rvfi_wdata.cfg[i] == cfg_expected)
    ) else `uvm_error(info_tag, "updating cfgs must use legal values");

    cov_not_ignore_writes_cfg_unlocked: cover property (
      !pmp_csr_rvfi_rdata.cfg[i].lock  ##0
      seq_cfg_expected_ante
    );

    cov_cfg_expected_updates: cover property (
      (pmp_csr_rvfi_wdata.cfg[i] != pmp_csr_rvfi_rdata.cfg[i])  ##0
      seq_cfg_expected_ante
    );

    cov_cfg_expected_ones: cover property (
      seq_cfg_expected_ante  ##0
      (rvfi_rs1_rdata[8*(i%4) +: 8] == '1)
    );
  end


  // Written cfg is legal  (vplan "ExecIgnored", ...)

  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_cfgwdata_legal
    wire [7:0] rectified_cfg = rectify_cfg_write(pmp_csr_rvfi_rdata.cfg[i], pmp_csr_rvfi_wdata.cfg[i]);

    a_cfgwdata_legal: assert property (
      rvfi_valid  &&
      pmp_csr_rvfi_wmask.cfg[i]
      |->
      (pmp_csr_rvfi_wdata.cfg[i] == rectified_cfg)
    ) else `uvm_error(info_tag, "updating cfgs must use legal values");
  end


  // Read cfg is as expected

  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_cfgrdata_expected
    property p_cfgrdata_expected;
      pmpncfg_t  cfg_prev;
      rvfi_valid  ##0
      (1, cfg_prev = pmp_csr_rvfi_rdata.cfg[i])
      ##1
      (rvfi_valid [->1])
      |->
      (pmp_csr_rvfi_rdata.cfg[i] == rectify_cfg_write(cfg_prev, pmp_csr_rvfi_rdata.cfg[i]))
      ;
    endproperty : p_cfgrdata_expected

    a_cfgrdata_expected: assert property (
      p_cfgrdata_expected
    ) else `uvm_error(info_tag, "read cfgs have legal values");
  end


  // addr/addr-1  unlocked->unstable  (vplan:NotIgnore)

  sequence  seq_csrrw_pmpaddri (i);
    (is_rvfi_csr_write_instr && (rvfi_insn[14:12] == 3'b 001))  &&  // "csrrw"
    (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPADDR + i))           &&  // ...to addr csr
    (!rvfi_trap)
    ;
  endsequence : seq_csrrw_pmpaddri

  function automatic logic  is_beneath_locktor (int cfg_idx);
    if (cfg_idx < (PMP_NUM_REGIONS - 1)) begin
      return (
        (pmp_csr_rvfi_rdata.cfg[cfg_idx + 1].mode == PMP_MODE_TOR)  &&
        (pmp_csr_rvfi_rdata.cfg[cfg_idx + 1].lock)
      );
    end else begin
      return 0;
    end
  endfunction : is_beneath_locktor

  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_addr_writes
    a_addr_writeattempt: assert property (
      seq_csrrw_pmpaddri(i)
      |->
      (pmp_csr_rvfi_wmask.addr[i][33:2] == 32'h FFFF_FFFF)
    ) else `uvm_error(info_tag, "writing addr must attempt word write");

    a_addr_nonlocked: assert property (
      seq_csrrw_pmpaddri(i)            and
      !pmp_csr_rvfi_rdata.cfg[i].lock  and
      !is_beneath_locktor(i)
      |->
      (pmp_csr_rvfi_wdata.addr[i][33:2+PMP_GRANULARITY]
        == rvfi_rs1_rdata[31:PMP_GRANULARITY])
    ) else `uvm_error(info_tag, "unlocked write must update as attempted");
  end

  for (genvar i = 1; i < PMP_NUM_REGIONS; i++) begin: gen_addr_tor
    // (Special case of "a_addr_nonlocked")
    a_addr_nonlocked_tor: assert property (
      seq_csrrw_pmpaddri(i - 1)                         and
      (pmp_csr_rvfi_rdata.cfg[i].mode == PMP_MODE_TOR)  and
      !pmp_csr_rvfi_rdata.cfg[i  ].lock                 and
      !pmp_csr_rvfi_rdata.cfg[i-1].lock
      |->
      (pmp_csr_rvfi_wdata.addr[i-1][33:2+PMP_GRANULARITY]
        == rvfi_rs1_rdata[31:PMP_GRANULARITY])
    ) else `uvm_error(info_tag, "unlocked write must update beneath tor too");
  end


  // RVFI: Reported CSR writes take effect  (vplan:AffectSuccessors)

  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_rvfi_csr_writes
    // cfg:
    property  p_rvfi_cfg_writes;
      logic [7:0]  cfg, cfg_r, cfg_w;
      rvfi_valid  ##0
      (1, cfg_w = (pmp_csr_rvfi_wdata.cfg[i] &  pmp_csr_rvfi_wmask.cfg[i]))  ##0
      (1, cfg_r = (pmp_csr_rvfi_rdata.cfg[i] & ~pmp_csr_rvfi_wmask.cfg[i]))  ##0
      (1, cfg = (cfg_r | cfg_w))
      ##1 (rvfi_valid [->1])
      |->
      (pmp_csr_rvfi_rdata.cfg[i] == cfg)
      ;
    endproperty : p_rvfi_cfg_writes
    a_rvfi_cfg_writes: assert property (
      p_rvfi_cfg_writes
    ) else `uvm_error(info_tag, "cfg updates must be present on next retire");

    // addr:
    property  p_rvfi_addr_writes;
      logic [31:0]  addr, addr_r, addr_w;
      rvfi_valid                                                                ##0
      (1, addr_w = (pmp_csr_rvfi_wdata.addr[i][33:2] &  pmp_csr_rvfi_wmask.addr[i][33:2]))  ##0
      (1, addr_r = (pmp_csr_rvfi_rdata.addr[i][33:2] & ~pmp_csr_rvfi_wmask.addr[i][33:2]))  ##0
      (1, addr = (addr_r | addr_w))
      ##1 (rvfi_valid [->1])
      |->
      (pmp_csr_rvfi_rdata.addr[i][31+2:PMP_GRANULARITY+2] == addr[31:PMP_GRANULARITY])
      ;
    endproperty : p_rvfi_addr_writes;
    a_rvfi_addr_writes: assert property (
      p_rvfi_addr_writes
    ) else `uvm_error(info_tag, "addr updates must be present on next retire");
  end


  // Locked TOR, ignore i-1 addr writes  (vplan:IgnoreTor)

  for (genvar i = 1; i < PMP_NUM_REGIONS; i++) begin: gen_ignore_tor
    a_ignore_tor_stable: assert property (
      rvfi_valid &&
      (pmp_csr_rvfi_rdata.cfg[i].lock && !pmp_csr_rvfi_rdata.mseccfg.rlb)  &&
      (pmp_csr_rvfi_rdata.cfg[i].mode == PMP_MODE_TOR)
      |=>
      always $stable(pmp_csr_rvfi_rdata.addr[i-1][31+2:PMP_GRANULARITY+2])
    ) else `uvm_error(info_tag, "TOR-locking must lock the subordinate addr");

    a_ignore_tor_wdata: assert property (
      rvfi_valid &&
      (pmp_csr_rvfi_rdata.cfg[i].lock && !pmp_csr_rvfi_rdata.mseccfg.rlb)  &&
      (pmp_csr_rvfi_rdata.cfg[i].mode == PMP_MODE_TOR)
      |->
      (pmp_csr_rvfi_wmask.addr[i-1] == 0)  ||
      (pmp_csr_rvfi_wdata.addr[i-1] == pmp_csr_rvfi_rdata.addr[i-1])
    ) else `uvm_error(info_tag, "TOR-locking forbids writing subordinate addr");
  end


  // Expected response on missing execute permission (vplan:WaitUpdate, vplan:AffectSuccessors, myriad vplan items)

  a_noexec_musttrap: assert property (
    rvfi_valid  &&
    !match_status_instr.is_access_allowed
    |->
    rvfi_trap
    // TODO:INFO:silabs-robin  Can assert the opposite too?
  ) else `uvm_error(info_tag, "on access denied we must trap");

  a_noexec_cause: assert property (
    rvfi_valid  &&
    !match_status_instr.is_access_allowed  &&
    rvfi_trap.exception
    |->
    (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_ACC_FAULT)
    // Note, if we implement etrigger etc then priority will change
  ) else `uvm_error(info_tag, "on access denied the cause must match");

  a_noexec_splittrap: assert property (
    rvfi_valid  &&
    rvfi_if.is_split_instrtrans  &&
    !match_status_upperinstr.is_access_allowed
    |->
    rvfi_trap
  ) else `uvm_error(info_tag, "on split-access denied we must trap");


  // Expected response on missing loadstore permission (vplan:WaitUpdate, vplan:AffectSuccessors)

  a_noloadstore_musttrap: assert property (
    rvfi_if.is_loadstore_instr  &&
    !match_status_data.is_access_allowed
    |->
    rvfi_trap
  ) else `uvm_error(info_tag, "on access denied we must trap");

  a_noloadstore_cause_load: assert property (
    rvfi_if.is_load_instr  &&
    !match_status_data.is_access_allowed  &&
    rvfi_trap.exception
    |->
    (rvfi_trap.exception_cause == EXC_CAUSE_LOAD_ACC_FAULT)  ^
    rvfi_if.is_deprioritized_load_acc_fault
  ) else `uvm_error(info_tag, "on load denied the cause must match");

  a_noloadstore_cause_store: assert property (
    rvfi_if.is_store_instr  &&
    !match_status_data.is_access_allowed  &&
    rvfi_trap.exception
    |->
    (rvfi_trap.exception_cause == EXC_CAUSE_STORE_ACC_FAULT)  ^
    rvfi_if.is_deprioritized_store_acc_fault
  ) else `uvm_error(info_tag, "on store denied the cause must match");

  a_noloadstore_splittrap: assert property (
    rvfi_valid  &&
    rvfi_if.is_split_datatrans_intended  &&
    !match_status_upperdata.is_access_allowed
    |->
    rvfi_trap
  ) else `uvm_error(info_tag, "on split-access denied we must trap");

  //TODO:INFO:silabs-robin Could model "is_blocked |-> pma_deny || pmp_deny" etc


  // RVFI must report what was allowed on the data bus  (Not a vplan item)

  a_rvfi_mem_allowed_data: assert property (
    rvfi_if.is_mem_act_actual
    |->
    match_status_data.is_access_allowed
  ) else `uvm_error(info_tag, "Data trans first word access must be allowed");

  a_rvfi_mem_allowed_upperdata: assert property (
    rvfi_if.is_split_datatrans_actual
    |->
    match_status_upperdata.is_access_allowed
  ) else `uvm_error(info_tag, "Data trans second word access must be allowed");


  // RVFI must report what was allowed on the instr bus  (Not a vplan item)

  a_instr_prediction: assert property (
    rvfi_if.rvfi_valid
    |->
    (rvfi_if.is_instr_acc_fault_pmp != is_access_allowed)  ||
    (rvfi_if.is_instr_acc_fault_pmp && denial_reasons)  ||
    rvfi_if.is_dbg_trg
    //Would like "fault!=allowed". Alas, impractical.
  ) else `uvm_error(info_tag, "RVFI PMP faults must match prediction");

  a_instr_nofault_nopclower: assert property (
    rvfi_if.rvfi_valid  &&
    !rvfi_if.is_instr_acc_fault_pmp
    |->
    !denial_reasons.pc_lower  ||
    rvfi_if.is_dbg_trg
  ) else `uvm_error(info_tag, "RVFI no fault, instr first word not denied");

  a_instr_nofault_nopcupper: assert property (
    rvfi_if.rvfi_valid  &&
    !rvfi_if.is_instr_acc_fault_pmp
    |->
    !denial_reasons.pc_upper  ||
    rvfi_if.is_dbg_trg
  ) else `uvm_error(info_tag, "RVFI no fault, instr second word not denied");

  a_instr_yesfault_yesdenial: assert property (
    rvfi_if.is_instr_acc_fault_pmp
    |->
    denial_reasons
  ) else `uvm_error(info_tag, "RVFI fault must be predicted");

  a_instr_nodenial_nofault: assert property (
    !denial_reasons
    |->
    !rvfi_if.is_instr_acc_fault_pmp
  ) else `uvm_error(info_tag, "no prediction, no RVFI fault");


  // RWX has reservations  (vplan:RwReserved)

  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_rwx_mml
    a_rwx_mml: assert property (
      !pmp_csr_rvfi_rdata.mseccfg.mml
      |->
      (pmp_csr_rvfi_rdata.cfg[i][1:0] != 2'b 10)
    ) else `uvm_error(info_tag, "'RW' cannot be 01");
  end


  // RLB lifts restrictions  (vplan:ExecRlb)

  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_rlblifts_lockedexec
    logic [31:0] csr_intended_wdata;
    always_comb begin
      csr_intended_wdata <=
        rvfi_if.csr_intended_wdata(
          ({24'd 0, pmp_csr_rvfi_rdata.cfg[i]} << 8*(i%4)),
          (CSRADDR_FIRST_PMPCFG + (i / 3'd4))
        );
    end
    wire pmpncfg_t  cfg_attempt = csr_intended_wdata[32'd 8 * (i%4) +: 8];

    sequence seq_rlblifts_lockedexec_ante;
      pmp_csr_rvfi_rdata.mseccfg.rlb  &&
      pmp_csr_rvfi_rdata.mseccfg.mml
      ##0
      rvfi_if.is_csr_write(CSRADDR_FIRST_PMPCFG + (i / 3'd4))  &&
      !rvfi_trap  &&
      !(PMP_GRANULARITY > 0 && cfg_attempt.mode == PMP_MODE_NA4)
      ;
    endsequence : seq_rlblifts_lockedexec_ante

    a_rlblifts_lockedexec: assert property (
      seq_rlblifts_lockedexec_ante
      |->
      (pmp_csr_rvfi_wdata.cfg[i] == (cfg_attempt & 8'h 9F))
    ) else `uvm_error(info_tag, "with rlb, some illegal cfgs must be writable");
    // Note, "lockedexec" is just one case of a restriction that RLB lifts.

  end

  cov_rlb_mml: cover property (
    rvfi_valid  &&
    pmp_csr_rvfi_rdata.mseccfg.rlb  &&
    pmp_csr_rvfi_rdata.mseccfg.mml
  );


  // Translate write-attempts to legal values

  function automatic pmpncfg_t  rectify_cfg_write (pmpncfg_t cfg_pre, pmpncfg_t cfg_attempt);
    pmpncfg_t  cfg_rfied;

    // Initial assumption: Attempt is ok
    cfg_rfied = cfg_attempt;

    // Pick "pre-state" where required
    begin
      // RWX collective WARL  (vplan:LegalRwx)
      if ((cfg_attempt[2:0] inside {2, 6}) && !pmp_csr_rvfi_rdata.mseccfg.mml) begin
        cfg_rfied[2:0] = cfg_pre[2:0];
      end

      // NA4, G=0  (vplan:Na4Unselectable)
      if ((PMP_GRANULARITY >= 1) && (cfg_attempt.mode == PMP_MODE_NA4)) begin
        cfg_rfied.mode = cfg_pre.mode;
      end

      // Locked config can't change  (vplan:IgnoreWrites)
      if (cfg_pre.lock && !pmp_csr_rvfi_rdata.mseccfg.rlb) begin
        cfg_rfied = cfg_pre;
      end

      // MML, no locked-executable  (vplan:ExecIgnored, vplan:ExecRlb)
      if (
        (pmp_csr_rvfi_rdata.mseccfg.mml && !pmp_csr_rvfi_rdata.mseccfg.rlb)  &&
        ({cfg_attempt.lock, cfg_attempt.read, cfg_attempt.write, cfg_attempt.exec}
          inside {4'b 1001, 4'b 1010, 4'b 1011, 4'b 1101})
      )
      begin
        cfg_rfied = cfg_pre;
        // TODO:WARNING:silabs-robin  Test "a_cfg_expected" without this clause.
      end
    end

    // Tied zero  (vplan:Warl)
    cfg_rfied.zero0 = '0;

    return  cfg_rfied;
  endfunction : rectify_cfg_write


endmodule : uvmt_cv32e40s_pmprvfi_assert


`default_nettype wire
