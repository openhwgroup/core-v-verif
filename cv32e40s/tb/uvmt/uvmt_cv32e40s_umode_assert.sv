// Copyright 2022 OpenHW Group
// Copyright 2022 Silicon Labs, Inc.
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


module  uvmt_cv32e40s_umode_assert
  import cv32e40s_pkg::*;
  import cv32e40s_rvfi_pkg::*;
  import uvm_pkg::*;
(
  input wire  clk_i,
  input wire  rst_ni,

  input wire         rvfi_valid,
  input wire [ 2:0]  rvfi_mode,
  input wire [63:0]  rvfi_order,
  input rvfi_trap_t  rvfi_trap,
  input rvfi_intr_t  rvfi_intr,
  input wire [31:0]  rvfi_insn,
  input wire         rvfi_dbg_mode,

  input wire [31:0]  rvfi_csr_misa_rdata,
  input wire [31:0]  rvfi_csr_mscratch_rdata,
  input wire [31:0]  rvfi_csr_mscratch_rmask,
  input wire [31:0]  rvfi_csr_mscratch_wdata,
  input wire [31:0]  rvfi_csr_mscratch_wmask,
  input wire [31:0]  rvfi_csr_mstatus_rdata,
  input wire [31:0]  rvfi_csr_mstatus_wdata,
  input wire [31:0]  rvfi_csr_mstatus_wmask,
  input wire [31:0]  rvfi_csr_mcause_rdata,
  input wire [31:0]  rvfi_csr_dcsr_rdata
);

  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;

  string info_tag = "CV32E40S_UMODE_ASSERT";

  localparam int MISA_U_POS = 20;
  localparam int MISA_S_POS = 18;
  localparam int MISA_N_POS = 13;

  localparam int MPP_POS     = 11;
  localparam int MPP_LEN     =  2;
  localparam int SPP_POS     =  8;
  localparam int SPP_LEN     =  1;
  localparam int MPRV_POS    = 17;
  localparam int MPRV_LEN    =  1;
  localparam int TW_POS      = 21;
  localparam int TW_LEN      =  1;
  localparam int EBREAKU_POS = 12;
  localparam int EBREAKU_LEN =  1;
  localparam int PRV_POS     =  0;
  localparam int PRV_LEN     =  2;
  // TODO:ropeders would be nice if these came from a trusted place instead of being defined here

  localparam int MODE_U = 2'b 00;
  localparam int MODE_M = 2'b 11;

  localparam int MRET_IDATA    = 32'b 0011000_00010_00000_000_00000_1110011;
  localparam int WFI_IDATA     = 32'b 0001000_00101_00000_000_00000_1110011;
  localparam int CUSTOM0_IDATA = 32'b 100011_00000000000_000_00000_1110011;
  localparam int CUSTOM0_IMASK = 32'b 111111_00000000000_111_00000_1111111;
  localparam int CUSTOM1_IDATA = 32'b 110011_00000000000_000_00000_1110011;
  localparam int CUSTOM1_IMASK = 32'b 111111_00000000000_111_00000_1111111;
  localparam int URET_IDATA    = 32'b 0000000_00010_00000_000_00000_1110011;
  localparam int EBREAK_IDATA  = 32'b 000000000001_00000_000_00000_1110011;

  wire [31:0]  mstatus_writestate  = (rvfi_csr_mstatus_wdata &  rvfi_csr_mstatus_wmask);
  wire [31:0]  mstatus_legacystate = (rvfi_csr_mstatus_rdata & ~rvfi_csr_mstatus_wmask);
  wire [31:0]  mstatus_poststate   = (mstatus_writestate | mstatus_legacystate);
  wire  is_rvfi_instrrevoked = (
    rvfi_trap.exception  &&
    (rvfi_trap.exception_cause inside {EXC_CAUSE_INSTR_FAULT, EXC_CAUSE_INSTR_BUS_FAULT})
  );
  wire  is_rvfi_mret = (
    rvfi_valid             &&
    !is_rvfi_instrrevoked  &&
    (rvfi_insn == MRET_IDATA)
  );
  wire  is_rvfi_wfi = (
    rvfi_valid             &&
    !is_rvfi_instrrevoked  &&
    (rvfi_insn == WFI_IDATA)
  );
  wire  is_rvfi_custominstr = (
    rvfi_valid             &&
    !is_rvfi_instrrevoked  &&
    (
      ((rvfi_insn & CUSTOM0_IMASK) == CUSTOM0_IDATA)  ||
      ((rvfi_insn & CUSTOM1_IMASK) == CUSTOM1_IDATA)
    )
  );
  wire  is_rvfi_uret = (
    rvfi_valid             &&
    !is_rvfi_instrrevoked  &&
    (rvfi_insn == URET_IDATA)
    // TODO:ropeders can condense these "is_..." signals?
  );
  wire  is_rvfi_ebreak = (
    rvfi_valid             &&
    !is_rvfi_instrrevoked  &&
    (rvfi_insn == EBREAK_IDATA)
  );


  a_misa_bits: assert property (
    rvfi_valid
    |->
     rvfi_csr_misa_rdata[MISA_U_POS] &&
    !rvfi_csr_misa_rdata[MISA_S_POS] &&
    !rvfi_csr_misa_rdata[MISA_N_POS]
  ) else `uvm_error(info_tag, "misa has wrong extension bits");

  a_no_unsupported_modes: assert property (
    rvfi_valid
    |->
    (rvfi_mode inside {MODE_U, MODE_M})
  ) else `uvm_error(info_tag, "non-supported privilege level executed");
  cov_umode: cover property (
    rvfi_valid && (rvfi_mode == MODE_U)
  );
  cov_mmode: cover property (
    rvfi_valid && (rvfi_mode == MODE_M)
  );

  a_initial_mode: assert property (
    rvfi_valid && (rvfi_order inside {0, 1})  // TODO:ropeders use "rst_ni" instead of "rvfi_order"?
    |->
    (rvfi_mode == MODE_M)
  ) else `uvm_error(info_tag, "priv mode out of reset should be machine-mode");

  a_mscratch_reliable: assert property (
    rvfi_valid && (rvfi_mode == MODE_U)
    |->
    (rvfi_csr_mscratch_wmask == 'd 0)
    // TODO:ropeders what about "mscratchcsw" and "mscratchcswl" too?
  ) else `uvm_error(info_tag, "mscratch should not change in user-mode");
  cov_mscratch_changing: cover property (
    rvfi_valid  &&
    (rvfi_csr_mscratch_wmask != 'd 0)
  );

  a_mpp_mode: assert property (
    rvfi_valid
    |->
    rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] inside {MODE_M, MODE_U}
    // TODO:ropeders sufficient with just "rdata" or need "wdata & wmask" too?
    // TODO:ropeders cover with "mret" instr
  ) else `uvm_error(info_tag, "mpp can only hold user- and machine-mode");
  cov_mpp_mmode: cover property (
    rvfi_valid  &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] == MODE_M)
  );
  cov_mpp_umode: cover property (
    rvfi_valid  &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] == MODE_U)
  );

  a_spp_zero: assert property (
    rvfi_valid
    |->
    (rvfi_csr_mstatus_rdata[SPP_POS+:SPP_LEN] == 'd 0)
  ) else `uvm_error(info_tag, "spp must be zero because supervisor-mode is not implemented");

/* TODO:ropeders finish writing
  a_trap_mpp: assert property (
    rvfi_valid             &&
    (rvfi_mode == MODE_U)  &&
    rvfi_trap
    |=>
    (rvfi_valid [->1])
    ##0
    (rvfi_mode == MODE_M)  &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] == MODE_U)
    // TODO:ropeders cross U/X and Exc/Int
  ) else `uvm_error(info_tag, "when umode exceptions are handled, mpp must be umode");
*/

  a_traps_mmode: assert property (
    rvfi_valid  &&
    rvfi_trap
    |=>
    (rvfi_valid [->1])
    ##0 (rvfi_mode == MODE_M)
    // TODO:ropeders cross Exc/Int etc
    // TODO:ropeders assert "rvfi_intr |-> mmode"?
    // TODO:ropeders assert "if_id.valid |-> has_seen_iobi_req"?
    // TODO:ropeders assert "!(rvfi_dbg_mode && (rvfi_mode != MODE_M))"?
  ) else `uvm_error(info_tag, "all trapsTODO shall be handled in mmode");

  a_interrupt_mmode: assert property (
    rvfi_valid    &&
    rvfi_intr[0]  &&
    (rvfi_intr.interrupt || rvfi_csr_mcause_rdata[31])
    // TODO:ropeders ((rvfi_intr[0] && rvfi_intr.interrupt) || rvfi_csr_mcause_rdata[31])?
    |->
    (rvfi_mode == MODE_M)
  ) else `uvm_error(info_tag, "all interrupts shall be handled in mmode");

  a_mret_umode: assert property (
    // TODO:ropeders use "is_rvfi_mret"
    rvfi_valid                &&
    (rvfi_insn == MRET_IDATA) &&
    !(
      rvfi_trap.exception  &&
      rvfi_trap.exception_cause inside {EXC_CAUSE_INSTR_FAULT, EXC_CAUSE_INSTR_BUS_FAULT}
    )
    |->
    //(rvfi_csr_mstatus_wdata[MPP_POS+:MPP_LEN] == MODE_U)  &&
    //(rvfi_csr_mstatus_wmask[MPP_POS+:MPP_LEN] == 2'b 11)
    mstatus_poststate[MPP_POS+:MPP_LEN] == MODE_U
    // TODO:ropeders don't allow for "rdata" to "save the day"? Demand "wdata" correctness?
    // TODO:ropeders refine property w/ clauses until realistic
  ) else `uvm_error(info_tag, "mret should set mpp to umode");

  a_mret_mprv: assert property (
    is_rvfi_mret  &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] != MODE_M)
    |->
    (mstatus_poststate[MPRV_POS+:MPRV_LEN] == 1'b 0)
    // TODO:ropeders don't allow for "rdata" to "save the day"? Demand "wdata" correctness?
  ) else `uvm_error(info_tag, "TODO");

  cov_mret_in_umode: cover property (
    is_rvfi_mret  &&
    (rvfi_mode == MODE_U)
  );

  a_wfi_illegal: assert property (
    is_rvfi_wfi            &&
    (rvfi_mode == MODE_U)  &&
    (rvfi_csr_mstatus_rdata[TW_POS+:TW_LEN] == 1)
    |->
    rvfi_trap[0]  &&
    (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
  ) else `uvm_error(info_tag, "TODO");

  a_custom_instr: assert property (
    is_rvfi_custominstr
    |->
    rvfi_trap[0]  &&
    (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
    // TODO:ropeders assert "!(rvfi_trap.exception && !rvfi_trap.exception_cause)"?
    // TODO:ropeders assert "pipe.illegal ##0 ... rvfi_valid |-> trap"?
    // TODO:ropeders cover "rvfi_dbg_mode && rvfi_trap"?
    // TODO:ropeders debug why this CEXes
  ) else `uvm_error(info_tag, "TODO");

  a_uret: assert property (
    is_rvfi_uret
    |->
    rvfi_trap[0]  &&
    (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
    // TODO:ropeders can condence these illegal_insn asserts w/ sequence?
  ) else `uvm_error(info_tag, "TODO");

  a_ebreaku_on: assert property (
    is_rvfi_ebreak         &&
    (rvfi_mode == MODE_U)  &&
    rvfi_csr_dcsr_rdata[EBREAKU_POS+:EBREAKU_LEN]
    |=>
    (rvfi_valid [->1])
    ##0 rvfi_dbg_mode
    // TODO:ropeders check rvfi_debug cause too?
    // TODO:ropeders is EBREAKU not supported?
  ) else `uvm_error(info_tag, "TODO");
  cov_ebreaku_bit: cover property (
    rvfi_csr_dcsr_rdata[EBREAKU_POS+:EBREAKU_LEN]
  );

  a_dmode_mmode: assert property (
    rvfi_valid  &&
    rvfi_dbg_mode
    |->
    (rvfi_mode == MODE_M)
  ) else `uvm_error(info_tag, "TODO");

  property p_dret_prv;
    int prv;
    (rvfi_valid && rvfi_dbg_mode)  ##0
    (1, prv = rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN]) ##1
    (rvfi_valid [->1])  ##0
    !rvfi_dbg_mode
    |->
    (rvfi_mode == prv);
  endproperty : p_dret_prv
  a_dret_prv: assert property (
    p_dret_prv
  ) else `uvm_error(info_tag, "resuming from dmode should be in dcsr.prv mode");
  cov_dret_prv_u: cover property (
    reject_on
      (rvfi_valid && !rvfi_dbg_mode && (rvfi_mode != MODE_U))
      p_dret_prv
    // TODO:ropeders double check that these covers work as intended
  );
  cov_dret_prv_m: cover property (
    reject_on
      (rvfi_valid && !rvfi_dbg_mode && (rvfi_mode != MODE_M))
      p_dret_prv
  );

  a_dret_mprv: assert property (
    ( rvfi_valid &&          rvfi_dbg_mode)  ##1
    ((rvfi_valid [->1]) ##0 !rvfi_dbg_mode)  ##0
    (rvfi_mode == MODE_U)
    |->
    (rvfi_csr_mstatus_rdata[MPRV_POS+:MPRV_LEN] == 0)
    // TODO:ropeders cover mprv 0->0 and 1->0
  ) else `uvm_error(info_tag, "exiting dmode to umode should clear mprv");

endmodule : uvmt_cv32e40s_umode_assert
