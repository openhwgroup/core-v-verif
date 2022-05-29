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
  input wire [ 1:0]  rvfi_mode,
  input wire [63:0]  rvfi_order,
  input rvfi_trap_t  rvfi_trap,
  input rvfi_intr_t  rvfi_intr,
  input wire [31:0]  rvfi_insn,
  input wire         rvfi_dbg_mode,
  input wire [ 2:0]  rvfi_dbg,
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
  localparam int IR_POS      =  2;
  localparam int MPRVEN_POS  =  4;
  localparam int MPRVEN_LEN  =  1;

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
  localparam int CSRADDR_HPM0       = 12'h C00;
  localparam int CSRADDR_MEDELEG    = 12'h 302;
  localparam int CSRADDR_MIDELEG    = 12'h 303;
  localparam int CSRADDR_MCOUNTEREN = 12'h 306;

  wire [31:0]  mstatus_writestate  = (rvfi_csr_mstatus_wdata &  rvfi_csr_mstatus_wmask);
  wire [31:0]  mstatus_legacystate = (rvfi_csr_mstatus_rdata & ~rvfi_csr_mstatus_wmask);
  wire [31:0]  mstatus_poststate   = (mstatus_writestate | mstatus_legacystate);
  wire [31:0]  mcause_writestate   = (rvfi_csr_mcause_wdata  &  rvfi_csr_mcause_wmask);
  wire [31:0]  mcause_legacystate  = (rvfi_csr_mcause_rdata  & ~rvfi_csr_mcause_wmask);
  wire [31:0]  mcause_poststate    = (mcause_writestate | mcause_legacystate);
  wire  is_rvfi_instrrevoked = (
    rvfi_trap.exception  &&
    (rvfi_trap.exception_cause inside {EXC_CAUSE_INSTR_FAULT, EXC_CAUSE_INSTR_BUS_FAULT})
  );
  wire  is_rvfi_instrtriggered = (
    rvfi_trap[0]     &&
    rvfi_trap.debug  &&
    (rvfi_trap.debug_cause == DBG_CAUSE_TRIGGER)
  );
  wire  is_rvfi_illegalinsn = (
    rvfi_trap[0]         &&
    rvfi_trap.exception  &&
    (rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)
  );
  wire  is_rvfi_mret = (
    rvfi_valid               &&
    !is_rvfi_instrrevoked    &&
    !rvfi_dbg_mode           &&
    !is_rvfi_instrtriggered  &&
    (rvfi_insn == MRET_IDATA)
  );
  wire  is_rvfi_wfi = (
    rvfi_valid               &&
    !is_rvfi_instrrevoked    &&
    !is_rvfi_instrtriggered  &&
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
    !is_rvfi_instrtriggered  &&
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

  reg [1:0]  effective_rvfi_privmode;
  always @(*) begin
    effective_rvfi_privmode = MODE_U;

    if (rvfi_dbg_mode) begin
      effective_rvfi_privmode = rvfi_mode;
    end else if (rvfi_csr_mstatus_rdata[MPRV_POS+:MPRV_LEN]) begin
      effective_rvfi_privmode = rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN];
    end else begin
      effective_rvfi_privmode = rvfi_mode;
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
    $past(rst_ni == 0)  ##0
    (rvfi_valid [->1])
    |->
    (rvfi_mode == MODE_M)  &&
    (rvfi_order inside {0, 1})
  ) else `uvm_error(info_tag, "priv mode out of reset should be machine-mode");

  a_mscratch_reliable: assert property (
    rvfi_valid && (rvfi_mode == MODE_U)
    |->
    (rvfi_csr_mscratch_wmask == 'd 0)
  ) else `uvm_error(info_tag, "mscratch should not change in user-mode");
  cov_mscratch_changing: cover property (
    rvfi_valid  &&
    (rvfi_csr_mscratch_wmask != 'd 0)
  );

  a_mpp_mode: assert property (
    rvfi_valid
    |->
    mstatus_poststate[MPP_POS+:MPP_LEN] inside {MODE_M, MODE_U}
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

  property p_trap_mpp;
    int mode;
    (rvfi_valid && rvfi_trap)  ##0
    (1, mode = rvfi_mode)
    |=>
    (rvfi_valid [->1])  ##0
    (rvfi_mode == MODE_M)  &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] == mode);
  endproperty : p_trap_mpp
  a_trap_mpp: assert property (
    p_trap_mpp
    // TODO:ropeders cov cross U/X and Exc/Int
  ) else `uvm_error(info_tag, "when exceptions from mode y are handled, mpp must become y");

  a_traps_mmode: assert property (
    rvfi_valid  &&
    rvfi_trap
    |=>
    (rvfi_valid [->1])  ##0
    (rvfi_mode == MODE_M)
    // TODO:ropeders cov cross Exc/Int etc
  ) else `uvm_error(info_tag, "all traps handling shall happen in mmode");

  a_interrupt_mmode: assert property (
    rvfi_valid  &&
    rvfi_intr
    |->
    (rvfi_mode == MODE_M)
  ) else `uvm_error(info_tag, "all traps shall be handled in mmode");

  a_mret_to_mpp: assert property (
    is_rvfi_mret
    |->
    (mstatus_poststate[MPP_POS+:MPP_LEN] == MODE_U)
  ) else `uvm_error(info_tag, "mret should set mpp to umode");

  a_mret_mprv: assert property (
    is_rvfi_mret  &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] != MODE_M)
    |->
    (mstatus_poststate[MPRV_POS+:MPRV_LEN] == 1'b 0)
  ) else `uvm_error(info_tag, "mret into umode must clear mstatus.mprv");

  a_wfi_illegal: assert property (
    is_rvfi_wfi            &&
    (rvfi_mode == MODE_U)  &&
    (rvfi_csr_mstatus_rdata[TW_POS+:TW_LEN] == 1)
    |->
    is_rvfi_illegalinsn
  ) else `uvm_error(info_tag, "wfi in umode w/ tw==1 is illegal");

  a_wfi_normal: assert property (
    is_rvfi_wfi            &&
    (rvfi_mode == MODE_U)  &&
    (rvfi_csr_mstatus_rdata[TW_POS+:TW_LEN] == 0)
    |->
    !(
      is_rvfi_illegalinsn
    )
  ) else `uvm_error(info_tag, "wfi in umode w/ tw==0 is not illegal");

  a_custom_instr: assert property (
    is_rvfi_custominstr
    |->
    is_rvfi_illegalinsn
  ) else `uvm_error(info_tag, "user-level custom instrs are not supported");

  a_uret: assert property (
    is_rvfi_uret
    |->
    is_rvfi_illegalinsn
  ) else `uvm_error(info_tag, "the uret instruction is not supported");

  a_ebreaku_on: assert property (
    is_rvfi_ebreak         &&
    (rvfi_mode == MODE_U)  &&
    rvfi_csr_dcsr_rdata[EBREAKU_POS+:EBREAKU_LEN]
    |=>
    (rvfi_valid [->1])  ##0
    rvfi_dbg_mode
  ) else `uvm_error(info_tag, "umode ebreak with ebreaku should cause dmode");
  cov_ebreaku_bit: cover property (
    rvfi_csr_dcsr_rdata[EBREAKU_POS+:EBREAKU_LEN]
  );

  a_ebreaku_off_except: assert property (
    is_rvfi_ebreak         &&
    (rvfi_mode == MODE_U)  &&
    !rvfi_csr_dcsr_rdata[EBREAKU_POS+:EBREAKU_LEN]
    |->
    (
      rvfi_trap[0]         &&
      rvfi_trap.exception  &&
      !rvfi_trap.debug     &&
      (rvfi_trap.exception_cause == EXC_CAUSE_BREAKPOINT)
    ) ^ (
      is_rvfi_instrtriggered
    )
  ) else `uvm_error(info_tag, "umode ebreak wo/ ebreaku should cause exception");

  a_ebreaku_off_nodebug: assert property (
    is_rvfi_ebreak         &&
    (rvfi_mode == MODE_U)  &&
    !rvfi_csr_dcsr_rdata[EBREAKU_POS+:EBREAKU_LEN]
    |=>
    (rvfi_valid [->1])  ##0
    (rvfi_dbg != DBG_CAUSE_EBREAK)
  ) else `uvm_error(info_tag, "umode ebreak wo/ ebreaku should not cause dmode");

  a_ecall_umode: assert property (
    is_rvfi_ecall  &&
    (rvfi_mode == MODE_U)
    |->
    (
      rvfi_trap[0]  &&
      rvfi_trap.exception  &&
      (rvfi_trap.exception_cause == EXC_CAUSE_ECALL_UMODE)  &&
      (mcause_poststate == EXC_CAUSE_ECALL_UMODE)
    ) ^ (
      is_rvfi_instrtriggered
    )
  ) else `uvm_error(info_tag, "umode ecall causes umode ecall exception");

  a_dmode_mmode: assert property (
    rvfi_valid  &&
    rvfi_dbg_mode
    |->
    (rvfi_mode == MODE_M)
  ) else `uvm_error(info_tag, "dmode must execute in mmode");

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
  );
  cov_dret_prv_m: cover property (
    reject_on
      (rvfi_valid && !rvfi_dbg_mode && (rvfi_mode != MODE_M))
      p_dret_prv
  );
  cov_prv_u: cover property (
    rvfi_valid  &&
    (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] == MODE_U)
  );
  cov_prv_m: cover property (
    rvfi_valid  &&
    (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] == MODE_M)
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
    |->
    rvficycle_hasfetched  &&
    (rvficycle_firstfetchaddr == rvfi_pc_rdata);
  endproperty : p_refetch
  a_refetch: assert property (
    p_refetch
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
    is_rvfi_illegalinsn
  ) else `uvm_error(info_tag, "access to higher lvl csrs is illegal");

  property p_mret_from_mpp (int mode);
    is_rvfi_mret  &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] == mode)  &&
    (rvfi_mode == MODE_M)  &&
    !rvfi_dbg_mode
    ##1
    (rvfi_valid [->1])  ##0
    !(rvfi_intr[0] && rvfi_intr.interrupt && rvfi_csr_mcause_rdata[31])  &&
    !(rvfi_dbg_mode)
    |->
    (rvfi_mode == mode);
  endproperty : p_mret_from_mpp
  a_mret_from_mpp_umode: assert property (
    p_mret_from_mpp(MODE_U)
  ) else `uvm_error(info_tag, "mret should result in privmode from mstatus.mpp (umode)");
  a_mret_from_mpp_mmode: assert property (
    p_mret_from_mpp(MODE_M)
  ) else `uvm_error(info_tag, "mret should result in privmode from mstatus.mpp (mmode)");

  a_mret_in_umode: assert property (
    is_rvfi_mret  &&
    (rvfi_mode == MODE_U)
    |->
    is_rvfi_illegalinsn ^ is_rvfi_instrtriggered
  ) else `uvm_error(info_tag, "mret in umode is illegal");

  for (genvar i = 0; i < 31; i++) begin : gen_mcounteren_clear
    a_check: assert property (
      is_rvfi_csrinstr                        &&
      (rvfi_mode == MODE_U)                   &&
      (rvfi_insn[31:20] == CSRADDR_HPM0 + i)  &&
      !rvfi_csr_mcounteren_rdata[i]
      |->
      is_rvfi_illegalinsn ^ is_rvfi_instrtriggered
    ) else `uvm_error(info_tag, "when mcounteren bit is off then umode access is illegal");
  end

  a_mcounteren_zeros: assert property (
    rvfi_valid
    |->
    (rvfi_csr_mcounteren_rdata == 0)
  ) else `uvm_error(info_tag, "not all bits in mcounteren can be non-zero");

  a_mcounteren_access: assert property (
    is_rvfi_csrinstr       &&
    (rvfi_mode == MODE_M)  &&
    (rvfi_insn[31:20] == CSRADDR_MCOUNTEREN)
    |->
    !is_rvfi_illegalinsn
  ) else `uvm_error(info_tag, "mcounteren must be implemented");

  a_jvt_access: assert property (
    is_rvfi_csrinstr  &&
    (rvfi_insn[31:20] == CSRADDR_JVT)
    |->
    !is_rvfi_illegalinsn
  ) else `uvm_error(info_tag, "jvt csr should be rw in both modes");

  a_next_csrs: assert property (
    is_rvfi_csrinstr  &&
    (rvfi_insn[31:20] inside {
      CSRADDR_USTATUS, CSRADDR_UIE, CSRADDR_UTVEC, CSRADDR_USCRATCH,
      CSRADDR_UEPC, CSRADDR_UCAUSE, CSRADDR_UTVAL, CSRADDR_UIP
      }
    )
    |->
    is_rvfi_illegalinsn
  ) else `uvm_error(info_tag, "none of the n ext csrs should be present");

  a_mprven_zero: assert property (
    rvfi_valid
    |->
    (rvfi_csr_dcsr_rdata[MPRVEN_POS+:MPRVEN_LEN] == 0)
  ) else `uvm_error(info_tag, "dcsr.mprven is not supported");

  property  p_prv_entry;
    int mode;
    (rvfi_valid && !rvfi_dbg_mode)  ##0
    (1, mode = rvfi_mode)
    ##1
    (rvfi_valid [->1])  ##0
    rvfi_dbg_mode
    |->
    if (!rvfi_intr[0]) (
      (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] == mode)
    ) else (
      (rvfi_intr.exception ^ rvfi_intr.interrupt)  &&
      (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] == MODE_M)
    );
  endproperty : p_prv_entry
  a_prv_entry: assert property (
    p_prv_entry
  ) else `uvm_error(info_tag, "on dbg entry, dcsr.prv should be previous privmode");
  cov_prv_entry_u: cover property (
    reject_on
      (rvfi_valid && rvfi_dbg_mode && (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] != MODE_U))
      p_prv_entry
  );
  cov_prv_entry_m: cover property (
    reject_on
      (rvfi_valid && rvfi_dbg_mode && (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] != MODE_M))
      p_prv_entry
  );

  a_prv_supported: assert property (
    rvfi_valid
    |->
    (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] inside {MODE_U, MODE_M})
  ) else `uvm_error(info_tag, "dcsr.prv must hold supported privmodes");
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
    is_rvfi_illegalinsn
  ) else `uvm_error(info_tag, "medeleg and mideleg registers should not exist");

/* TODO:ropeders enable (and tweak) when rvfi implementation has the new signals
  a_prot_fetch: assert property (
    rvfi_valid
    |->
    (rvfi_custom.instr_prot[2:1] == rvfi_mode)
  ) else `uvm_error(info_tag, "the prot on fetch must match the mode on retirement");

  a_prot_loadstore: assert property (
    rvfi_valid  &&
    is_rvfi_loadstore
    |->
    (rvfi_custom.loadstore_prot[2:1] == effective_rvfi_privmode)
  ) else `uvm_error(info_tag, "the prot on load/store must match the effective mode on retirement");
*/

  a_dbgpriv: assert property (
    rvfi_valid  &&
    rvfi_dbg_mode
    |->
    (rvfi_mode == MODE_M)
  );

endmodule : uvmt_cv32e40s_umode_assert
