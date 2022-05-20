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
  input wire [31:0]  rvfi_pc_rdata,

  input wire [31:0]  rvfi_csr_dcsr_rdata,
  input wire [31:0]  rvfi_csr_mcause_rdata,
  input wire [31:0]  rvfi_csr_mcause_wdata,
  input wire [31:0]  rvfi_csr_mcause_wmask,
  input wire [31:0]  rvfi_csr_mcounteren_rdata,
  input wire [31:0]  rvfi_csr_misa_rdata,
  input wire [31:0]  rvfi_csr_mscratch_rdata,
  input wire [31:0]  rvfi_csr_mscratch_rmask,
  input wire [31:0]  rvfi_csr_mscratch_wdata,
  input wire [31:0]  rvfi_csr_mscratch_wmask,
  input wire [31:0]  rvfi_csr_mstatus_rdata,
  input wire [31:0]  rvfi_csr_mstatus_wdata,
  input wire [31:0]  rvfi_csr_mstatus_wmask,

  input wire         impu_valid,
  input wire [31:0]  impu_addr
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
  localparam int XS_POS      = 15;
  localparam int XS_LEN      =  2;
  localparam int FS_POS      = 13;
  localparam int FS_LEN      =  2;
  localparam int SD_POS      = 31;
  localparam int SD_LEN      =  1;
  localparam int CY_POS      =  0;
  localparam int CY_LEN      =  1;
  localparam int MPRVEN_POS  =  4;
  localparam int MPRVEN_LEN  =  1;
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
  localparam int ECALL_IDATA   = 32'b 000000000000_00000_000_00000_1110011;

  localparam int CSRADDR_USTATUS    = 12'h 000;
  localparam int CSRADDR_UIE        = 12'h 004;
  localparam int CSRADDR_UTVEC      = 12'h 005;
  localparam int CSRADDR_JVT        = 12'h 017;
  localparam int CSRADDR_USCRATCH   = 12'h 040;
  localparam int CSRADDR_UEPC       = 12'h 041;
  localparam int CSRADDR_UCAUSE     = 12'h 042;
  localparam int CSRADDR_UTVAL      = 12'h 043;
  localparam int CSRADDR_UIP        = 12'h 044;
  localparam int CSRADDR_CYCLE      = 12'h C00;
  localparam int CSRADDR_MEDELEG    = 12'h 302;
  localparam int CSRADDR_MIDELEG    = 12'h 303;
  localparam int CSRADDR_MCOUNTEREN = 12'h 306;

  wire [31:0]  mstatus_writestate  = (rvfi_csr_mstatus_wdata &  rvfi_csr_mstatus_wmask);
  wire [31:0]  mstatus_legacystate = (rvfi_csr_mstatus_rdata & ~rvfi_csr_mstatus_wmask);
  wire [31:0]  mstatus_poststate   = (mstatus_writestate | mstatus_legacystate);
  wire  is_rvfi_instrrevoked = (
    rvfi_trap.exception  &&
    (rvfi_trap.exception_cause inside {EXC_CAUSE_INSTR_FAULT, EXC_CAUSE_INSTR_BUS_FAULT})
  );
  wire  is_rvfi_illegalinsn = (
    rvfi_trap[0]         &&
    rvfi_trap.exception  &&
    (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
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
  wire  is_rvfi_ecall = (
    rvfi_valid             &&
    !is_rvfi_instrrevoked  &&
    (rvfi_insn == ECALL_IDATA)
  );
  wire  is_rvfi_csrinstr = (
    rvfi_valid  &&
    !is_rvfi_instrrevoked  &&
    (rvfi_insn[ 6: 0] == 7'b 1110011) &&
    (rvfi_insn[14:12] inside {1, 2, 3, 5, 6, 7})
  );

  reg         rvficycle_hasfetched;
  reg [31:0]  rvficycle_firstfetchaddr;
  always @(posedge clk_i) begin
    if (rst_ni == 0) begin
      rvficycle_hasfetched <= 0;
      rvficycle_firstfetchaddr  <= 0;
    end else begin
      if (rvfi_valid) begin
        rvficycle_hasfetched <= 0;
        rvficycle_firstfetchaddr  <= 0;
      end

      if (impu_valid) begin
        rvficycle_hasfetched <= 1;

        if (rvfi_valid || !rvficycle_hasfetched) begin
          rvficycle_firstfetchaddr  <= impu_addr;
        end
      end
    end
  end


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

  a_mret_to_mpp: assert property (
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
    // TODO:ropeders assert mret in umode fails
  );

  a_wfi_illegal: assert property (
    is_rvfi_wfi            &&
    (rvfi_mode == MODE_U)  &&
    (rvfi_csr_mstatus_rdata[TW_POS+:TW_LEN] == 1)
    |->
    rvfi_trap[0]  &&
    (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
  ) else `uvm_error(info_tag, "TODO");

  a_wfi_normal: assert property (
    is_rvfi_wfi            &&
    (rvfi_mode == MODE_U)  &&
    (rvfi_csr_mstatus_rdata[TW_POS+:TW_LEN] == 0)
    |->
    !(
      rvfi_trap[0]  &&
      (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
    )
    // TODO:ropeders check more specifically that wfi operation works as normal?
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

  a_ecall_umode: assert property (
    is_rvfi_ecall  &&
    (rvfi_mode == MODE_U)
    |->
    (
      rvfi_trap[0]  &&
      rvfi_trap.exception  &&
      (rvfi_trap.exception_cause == EXC_CAUSE_ECALL_UMODE)  &&
      ((rvfi_csr_mcause_wdata & rvfi_csr_mcause_wmask) == EXC_CAUSE_ECALL_UMODE)
      // TODO:ropeders check mask is all ones?
    ) ^ (
      rvfi_trap[0]  &&
      rvfi_trap.debug  &&
      (rvfi_trap.debug_cause == DBG_CAUSE_TRIGGER)
      // TODO:ropeders should be in "revoked" clause?
    )
    // (might change when triggers are fully implemented)
    // TODO:ropeders don't trust the core pkg EXC_CAUSE defines?
    // TODO:ropeders will named sequences improve readability?
    // TODO:ropeders assert that exception_cause "always" matches mcause?
  ) else `uvm_error(info_tag, "TODO");

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

  property p_refetch;
    int mode0;
    ( rvfi_valid, mode0 = rvfi_mode)  ##1
    ((rvfi_valid [->1]) ##0 (rvfi_mode != mode0))
    // TODO:ropeders should compare against order=0 too  (helper-signal "rvfi_prev_mode"?)
    |->
    rvficycle_hasfetched  &&
    (rvficycle_firstfetchaddr == rvfi_pc_rdata);
    // TODO:ropeders  rtl updates will likely reveal need for tweaking this property
  endproperty : p_refetch
  a_refetch: assert property (
    p_refetch
    // TODO:ropeders how to also make sure the refetch uses the updated mode?
    // TODO:ropeders confirm that csr/mode update happens with the assumed timing relation to rvfi_valid
    // TODO:ropeders how to SVA "if change then was fetch" instead of "if no fetch then no change"?
    // TODO:ropeders write properties for all necessary cases (NoFetch, WrongFetch, ...)
  ) else `uvm_error(info_tag, "priv mode change must cause refetch");

  a_umode_extensions: assert property (
    rvfi_valid
    |->
    !rvfi_csr_mstatus_rdata[XS_POS+:XS_LEN]  &&
    !rvfi_csr_mstatus_rdata[FS_POS+:FS_LEN]  &&
    !rvfi_csr_mstatus_rdata[SD_POS+:SD_LEN]
  ) else `uvm_error(info_tag, "none of the mstatus umode extension bits shall be used");

  a_illegal_csr_access: assert property (
    is_rvfi_csrinstr       &&
    (rvfi_mode == MODE_U)  &&
    (rvfi_insn[29:28] != MODE_U)
    |->
    rvfi_trap[0]        &&
    rvfi_trap.exception &&
    (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
  ) else `uvm_error(info_tag, "access to higher lvl csrs is illegal");

  property p_mret_from_mpp (int mode);
    is_rvfi_mret  &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] == mode)  &&
    (rvfi_mode == MODE_M)  &&
    !rvfi_dbg_mode
    ##1
    (rvfi_valid [->1])
    ##0
    !(rvfi_intr[0] && rvfi_intr.interrupt && rvfi_csr_mcause_rdata[31])  &&
    !(rvfi_dbg_mode)
    |->
    (rvfi_mode == mode);
  endproperty : p_mret_from_mpp
  a_mret_from_mpp_umode: assert property (
    p_mret_from_mpp(MODE_U)
  ) else `uvm_error(info_tag, "TODO");
  a_mret_from_mpp_mmode: assert property (
    p_mret_from_mpp(MODE_M)
  ) else `uvm_error(info_tag, "TODO");
 /*
  cov_mret_from_mpp_umode: cover property (
    is_rvfi_mret  &&
    (rvfi_mode == MODE_M)  &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] == MODE_U)  &&
    !rvfi_dbg_mode
    ##1
    (rvfi_valid [->1])  ##0
  );
 */

  a_mret_in_umode: assert property (
    is_rvfi_mret  &&
    (rvfi_mode == MODE_U)
    |->
    (
      rvfi_trap[0]  &&
      rvfi_trap.exception  &&
      (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
    ) ^ (
      rvfi_trap[0]  &&
      rvfi_trap.debug  &&
      (rvfi_trap.debug_cause == DBG_CAUSE_TRIGGER)
      // TODO:ropeders refactor to helper-signal?
    )
  ) else `uvm_error(info_tag, "TODO");

  a_mcounteren_clear: assert property (
    is_rvfi_csrinstr  &&
    (rvfi_insn[31:20] == CSRADDR_CYCLE)  &&
    // TODO:ropeders CY/TM/IR/HPMn all of them
    (rvfi_mode == MODE_U)  &&
    !rvfi_csr_mcounteren_rdata[CY_POS+:CY_LEN]
    |->
    (
      rvfi_trap[0]         &&
      rvfi_trap.exception  &&
      (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
    ) ^ (
      rvfi_trap[0]     &&
      rvfi_trap.debug  &&
      (rvfi_trap.debug_cause == DBG_CAUSE_TRIGGER)
      // TODO:ropeders refactor to helper-signal?
    )
  ) else `uvm_error(info_tag, "TODO");

  a_mcounteren_access: assert property (
    is_rvfi_csrinstr       &&
    (rvfi_mode == MODE_M)  &&
    (rvfi_insn[31:20] == CSRADDR_MCOUNTEREN)
    |->
    !(
      rvfi_trap[0]         &&
      rvfi_trap.exception  &&
      (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
      // TODO:ropeders refactor to helper-signal
    )
  ) else `uvm_error(info_tag, "TODO");

  a_jvt_access: assert property (
    is_rvfi_csrinstr  &&
    (rvfi_insn[31:20] == CSRADDR_JVT)
    |->
    !is_rvfi_illegalinsn
    // TODO:ropeders "Smstateen"
    // TODO:ropeders "accessible" AND "effective"
  ) else `uvm_error(info_tag, "TODO");

  a_next_csrs: assert property (
    is_rvfi_csrinstr  &&
    (rvfi_insn[31:20] inside {
      CSRADDR_USTATUS, CSRADDR_UIE, CSRADDR_UTVEC, CSRADDR_USCRATCH,
      CSRADDR_UEPC, CSRADDR_UCAUSE, CSRADDR_UTVAL, CSRADDR_UIP
      }
    )
    |->
    rvfi_trap[0]         &&
    rvfi_trap.exception  &&
    (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
  ) else `uvm_error(info_tag, "none of the n ext csrs should be present");

  a_mprven_zero: assert property (
    rvfi_valid
    |->
    (rvfi_csr_dcsr_rdata[MPRVEN_POS+:MPRVEN_LEN] == 0)
  ) else `uvm_error(info_tag, "TODO");

  property  p_prv_entry;
    int mode;
    (rvfi_valid && !rvfi_dbg_mode)  ##0
    (1, mode = rvfi_mode)
    ##1
    (rvfi_valid [->1])  ##0
    rvfi_dbg_mode
    |->
    (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] == mode);
  endproperty : p_prv_entry
  a_prv_entry: assert property (
    p_prv_entry
  ) else `uvm_error(info_tag, "TODO");

  a_prv_supported: assert property (
    rvfi_valid
    |->
    (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] inside {MODE_U, MODE_M})
  ) else `uvm_error(info_tag, "TODO");
  cov_prv_supported_umode: cover property (
    rvfi_valid  &&
    (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] == MODE_U)
  );
  cov_prv_supported_mmode: cover property (
    rvfi_valid  &&
    (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] == MODE_M)
  );

  a_medeleg_mideleg: assert property (
    is_rvfi_csrinstr  &&
    (rvfi_insn[31:20] inside {CSRADDR_MEDELEG, CSRADDR_MIDELEG})
    |->
    rvfi_trap[0]         &&
    rvfi_trap.exception  &&
    (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
  ) else `uvm_error(info_tag, "medeleg and mideleg registers should not exist");

endmodule : uvmt_cv32e40s_umode_assert
