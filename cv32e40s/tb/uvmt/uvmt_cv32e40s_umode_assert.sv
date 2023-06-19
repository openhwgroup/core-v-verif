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


`default_nettype  none


module  uvmt_cv32e40s_umode_assert
  import cv32e40s_pkg::*;
  import cv32e40s_rvfi_pkg::*;
  import uvm_pkg::*;
#(
  parameter bit  CLIC
)(
  input wire  clk_i,
  input wire  rst_ni,

  input wire               rvfi_valid,
  input wire [ 1:0]        rvfi_mode,
  input wire [63:0]        rvfi_order,
  input wire rvfi_trap_t   rvfi_trap,
  input wire rvfi_intr_t   rvfi_intr,
  input wire [31:0]        rvfi_insn,
  input wire               rvfi_dbg_mode,
  input wire [ 2:0]        rvfi_dbg,
  input wire [31:0]        rvfi_pc_rdata,
  uvma_rvfi_instr_if_t       rvfi_if,
  //TODO:INFO:silabs-robin Should only use the interface

  input wire [31:0]  rvfi_csr_dcsr_rdata,
  input wire [31:0]  rvfi_csr_mcause_rdata,
  input wire [31:0]  rvfi_csr_mcause_wdata,
  input wire [31:0]  rvfi_csr_mcause_wmask,
  input wire [31:0]  rvfi_csr_mcounteren_rdata,
  input wire [31:0]  rvfi_csr_mie_rdata,
  input wire [31:0]  rvfi_csr_mip_rdata,
  input wire [31:0]  rvfi_csr_misa_rdata,
  input wire [31:0]  rvfi_csr_mscratch_rdata,
  input wire [31:0]  rvfi_csr_mscratch_rmask,
  input wire [31:0]  rvfi_csr_mscratch_wdata,
  input wire [31:0]  rvfi_csr_mscratch_wmask,
  input wire [31:0]  rvfi_csr_mstateen0_rdata,
  input wire [31:0]  rvfi_csr_mstatus_rdata,
  input wire [31:0]  rvfi_csr_mstatus_wdata,
  input wire [31:0]  rvfi_csr_mstatus_wmask,

  input wire         mpu_iside_valid,
  input wire [31:0]  mpu_iside_addr,

  input wire [ 2:0]  obi_iside_prot,
  input wire [ 2:0]  obi_dside_prot
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
  localparam int DRET_IDATA    = 32'h 7b200073;
  localparam int WFI_IDATA     = 32'b 0001000_00101_00000_000_00000_1110011;
  localparam int WFE_IDATA     = 32'h 8C00_0073;
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
  wire  is_rvfi_valid_norevoke_notrigger = (
    rvfi_valid               &&
    !is_rvfi_instrrevoked    &&
    !is_rvfi_instrtriggered
  );
  wire  is_rvfi_mret = (
    is_rvfi_valid_norevoke_notrigger  &&
    (rvfi_insn == MRET_IDATA)
  );
  wire  is_rvfi_dret = (
    is_rvfi_valid_norevoke_notrigger  &&
    (rvfi_insn == DRET_IDATA)
  );
  wire  is_rvfi_wfi = (
    is_rvfi_valid_norevoke_notrigger  &&
    (rvfi_insn == WFI_IDATA)
  );
  wire  is_rvfi_customumodeinstr = (
    is_rvfi_valid_norevoke_notrigger  &&
    (
      ((rvfi_insn & CUSTOM0_IMASK) == CUSTOM0_IDATA)  ||
      ((rvfi_insn & CUSTOM1_IMASK) == CUSTOM1_IDATA)
    )
  );
  wire  is_rvfi_wfe = (
    is_rvfi_valid_norevoke_notrigger  &&
    (rvfi_insn == WFE_IDATA)
  );
  wire  is_rvfi_uret = (
    is_rvfi_valid_norevoke_notrigger  &&
    (rvfi_insn == URET_IDATA)
  );
  wire  is_rvfi_ebreak = (
    is_rvfi_valid_norevoke_notrigger  &&
    (rvfi_insn == EBREAK_IDATA)
  );
  wire  is_rvfi_ecall = (
    is_rvfi_valid_norevoke_notrigger  &&
    (rvfi_insn == ECALL_IDATA)
  );
  wire  is_rvfi_csrinstr = (
    is_rvfi_valid_norevoke_notrigger  &&
    (rvfi_insn[ 6: 0] == 7'b 1110011) &&
    (rvfi_insn[14:12] inside {1, 2, 3, 5, 6, 7})
  );

  reg   was_rvfi_valid;
  wire  clk_rvfi;
  always @(posedge clk_i) begin
    was_rvfi_valid <= rvfi_valid;
  end
  assign  clk_rvfi = clk_i & was_rvfi_valid;

  reg [1:0]  effective_rvfi_privmode;
  always @(*) begin
    if (rvfi_csr_mstatus_rdata[MPRV_POS+:MPRV_LEN]) begin
      effective_rvfi_privmode = rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN];
    end else begin
      effective_rvfi_privmode = rvfi_mode;
    end
  end

  reg [1:0]  was_rvfi_mode;
  reg [1:0]  was_rvfi_mode_wdata;  // Expected next mode (ignoring dmode)
  reg        was_rvfi_dbg_mode;
  always @(posedge clk_i) begin
    if (rvfi_valid) begin
      was_rvfi_mode     <= rvfi_mode;
      was_rvfi_dbg_mode <= rvfi_dbg_mode;

      was_rvfi_mode_wdata <=
        (is_rvfi_mret && !rvfi_trap.exception) ? (
          rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN]
        ) : (
          (is_rvfi_dret && !rvfi_trap.exception) ? (
            rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN]
          ) : (
            (rvfi_trap.exception) ? (
              MODE_M
            ) : (
              rvfi_mode
            )
          )
        );
        // TODO:INFO:silabs-robin  Check "(rvfi_mode == ...wdata) || rvfi_intr"
    end
  end

  wire logic [MPP_LEN-1:0]  mpp_rdata;
  wire logic [MPP_LEN-1:0]  mpp_rdata_past;
  assign  mpp_rdata      = rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN];
  assign  mpp_rdata_past = $past(mpp_rdata, , ,@(posedge clk_rvfi));


  // vplan:MisaU & vplan:MisaN

  a_misa_bits: assert property (
    rvfi_valid
    |->
     rvfi_csr_misa_rdata[MISA_U_POS] &&
    !rvfi_csr_misa_rdata[MISA_S_POS] &&
    !rvfi_csr_misa_rdata[MISA_N_POS]
  ) else `uvm_error(info_tag, "misa has wrong extension bits");


  // vplan:SupportedLevels

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


  // vplan:ResetMode

  a_initial_mode: assert property (
    $past(rst_ni == 0)  ##0
    (rvfi_valid [->1])
    |->
    (rvfi_mode == MODE_M)  &&
    (rvfi_order inside {0, 1})
  ) else `uvm_error(info_tag, "priv mode out of reset should be machine-mode");


  // vplan:MscratchReliable

  a_mscratch_reliable: assert property (
    rvfi_valid && (rvfi_mode == MODE_U)
    |->
    (rvfi_csr_mscratch_wmask == 'd 0)
  ) else `uvm_error(info_tag, "mscratch should not change in user-mode");

  cov_mscratch_changing: cover property (
    rvfi_valid  &&
    (rvfi_csr_mscratch_wmask != 'd 0)
  );


  // vplan:MppValues

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


  // vplan:SppValues

  a_spp_zero: assert property (
    rvfi_valid
    |->
    (rvfi_csr_mstatus_rdata[SPP_POS+:SPP_LEN] == 'd 0)
  ) else `uvm_error(info_tag, "spp must be zero because supervisor-mode is not implemented");


  // vplan:TrapMpp

  property p_trap_mpp_exception;
    int  was_mode;
    int  was_dbg;
    (rvfi_valid && rvfi_trap.exception) ##0
    (1, was_mode = rvfi_mode)           ##0
    (1, was_dbg  = rvfi_dbg_mode)
    ##1
    (rvfi_valid [->1])
    |->
    (rvfi_mode == MODE_M)  &&
    (
      (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] == was_mode)  ||
      rvfi_intr.interrupt  ||
      was_dbg
    )
    ;
  endproperty : p_trap_mpp_exception

  a_trap_mpp_exception: assert property (
    p_trap_mpp_exception
  ) else `uvm_error(info_tag, "when exceptions from mode y are handled, mpp must become y");

  a_trap_mpp_general: assert property (
    rvfi_valid  &&
    rvfi_intr  &&
    !(was_rvfi_dbg_mode && rvfi_dbg_mode)
    |->
    if (rvfi_intr.exception) (
      (mpp_rdata == was_rvfi_mode)
    ) else (
      (mpp_rdata == was_rvfi_mode_wdata)  ||
      (rvfi_intr.cause inside {[1024:1027]})  // NMI
      // TODO:INFO:silabs-robin  Preferably, exclude only "multi-lvl irq" specifically
    )
  ) else `uvm_error(info_tag, "when traps from mode y are handled, mpp must become y");

  a_trap_mpp_debug: assert property (
    @(posedge clk_rvfi)
    rvfi_valid         &&
    rvfi_intr          &&
    was_rvfi_dbg_mode  &&
    rvfi_dbg_mode
    |->
    (mpp_rdata == mpp_rdata_past)  ||
    (rvfi_dbg && rvfi_intr.interrupt)
  ) else `uvm_error(info_tag, "when trapping inside dmode mpp must be M-mode");


  // vplan:TrapsMmode & vplan:ToMmode

  a_traps_mmode: assert property (
    rvfi_valid  &&
    rvfi_trap
    ##1
    (rvfi_valid [->1])
    |->
    (rvfi_mode == MODE_M)
  ) else `uvm_error(info_tag, "all traps handling shall happen in mmode");

  a_interrupt_mmode: assert property (
    rvfi_valid  &&
    rvfi_intr
    |->
    (rvfi_mode == MODE_M)
  ) else `uvm_error(info_tag, "all traps shall be handled in mmode");

  a_umodetrap_zeromprv: assert property (
    (rvfi_valid && (rvfi_mode == MODE_U))
    ##1
    (rvfi_valid [->1])
    |->
    (rvfi_csr_mstatus_rdata[MPRV_POS+:MPRV_LEN] == 1'b 0)
  ) else `uvm_error(info_tag, "traps in umode keep mprv at zero");


  // vplan:MretLeastPrivileged

  a_mret_to_mpp: assert property (
    is_rvfi_mret  &&
    !rvfi_trap
    |->
    (mstatus_poststate[MPP_POS+:MPP_LEN] == MODE_U)
  ) else `uvm_error(info_tag, "mret should set mpp to umode");


  // vplan:MretMprv

  sequence  seq_mret_notrap_toumode;
    is_rvfi_mret  &&
    !rvfi_trap    &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] != MODE_M)
    ;
  endsequence : seq_mret_notrap_toumode

  a_mret_mprv_poststate: assert property (
    seq_mret_notrap_toumode
    |->
    (mstatus_poststate[MPRV_POS+:MPRV_LEN] == 1'b 0)
  ) else `uvm_error(info_tag, "mret into umode must clear mstatus.mprv");

  a_mret_mprv_writestate: assert property (
    seq_mret_notrap_toumode
    |->
    (mstatus_writestate[MPRV_POS+:MPRV_LEN] == 1'b 0)
  ) else `uvm_error(info_tag, "mret into umode must write mstatus.mprv to zero");

  a_mret_mprv_writempp: assert property (
    seq_mret_notrap_toumode
    |->
    rvfi_csr_mstatus_wmask[MPRV_POS+:MPRV_LEN]
  ) else `uvm_error(info_tag, "mret into umode must write mstatus.mprv");

  a_mret_mprv_writemstatus_simplified: assert property (
    seq_mret_notrap_toumode  ##0
    (!rvfi_dbg_mode && !rvfi_intr)
    |->
    rvfi_csr_mstatus_wmask
  ) else `uvm_error(info_tag, "mret into umode must write mstatus");

  a_mprv_poststate: assert property (
    rvfi_csr_mstatus_wmask[MPRV_POS+:MPRV_LEN]
    |->
    (mstatus_writestate[MPRV_POS+:MPRV_LEN] == mstatus_poststate[MPRV_POS+:MPRV_LEN])
  ) else `uvm_error(info_tag, "mstatus writes are reflected in the post state");


  // vplan:WfiExecute & vplan:WfiIllegal

  a_wfi_illegal: assert property (
    is_rvfi_wfi            &&
    (rvfi_mode == MODE_U)  &&
    (rvfi_csr_mstatus_rdata[TW_POS+:TW_LEN] == 1)
    |->
    is_rvfi_illegalinsn  ^
    (rvfi_trap.exception_cause inside {1, 24, 25})  // Higher priority exceptions
  ) else `uvm_error(info_tag, "wfi in umode w/ tw==1 is illegal");

  a_wfi_normal: assert property (
    is_rvfi_wfi            &&
    (rvfi_mode == MODE_U)  &&
    (rvfi_csr_mstatus_rdata[TW_POS+:TW_LEN] == 0)
    |->
    !is_rvfi_illegalinsn
  ) else `uvm_error(info_tag, "wfi in umode w/ tw==0 is not illegal");


  // vplan:CustomInstr & vplan:Uret

  a_custom_instr: assert property (
    is_rvfi_customumodeinstr  &&
    !is_rvfi_wfe
    |->
    is_rvfi_illegalinsn  ^
    (rvfi_trap.exception_cause inside {1, 24, 25})  // Higher priority exceptions
  ) else `uvm_error(info_tag, "user-level custom instrs are not supported");

  a_uret: assert property (
    is_rvfi_uret
    |->
    is_rvfi_illegalinsn  ^
    (rvfi_trap.exception_cause inside {1, 24, 25})  // Higher priority exceptions
  ) else `uvm_error(info_tag, "the uret instruction is not supported");


  // vplan:EbreakuOn

  a_ebreaku_on_rvfivalid: assert property (
    is_rvfi_ebreak         &&
    (rvfi_mode == MODE_U)  &&
    rvfi_csr_dcsr_rdata[EBREAKU_POS+:EBREAKU_LEN]
    ##1
    (rvfi_valid [->1])
    |->
    rvfi_dbg_mode
  ) else `uvm_error(info_tag, "umode ebreak with ebreaku should cause dmode");

  cov_ebreaku_bit: cover property (
    rvfi_csr_dcsr_rdata[EBREAKU_POS+:EBREAKU_LEN]
  );

  a_ebreaku_on_dbgtrap: assert property (
    is_rvfi_ebreak         &&
    (rvfi_mode == MODE_U)  &&
    rvfi_csr_dcsr_rdata[EBREAKU_POS+:EBREAKU_LEN]
    |->
    rvfi_if.rvfi_trap.trap  &&
    rvfi_if.rvfi_trap.debug
  ) else `uvm_error(info_tag, "ebreaku must give debug trap");

  a_ebreaku_on_noexception: assert property (
    is_rvfi_ebreak         &&
    (rvfi_mode == MODE_U)  &&
    rvfi_csr_dcsr_rdata[EBREAKU_POS+:EBREAKU_LEN]
    |->
    !(
      rvfi_if.rvfi_trap.exception  &&
      (rvfi_if.rvfi_trap.exception_cause == EXC_CAUSE_BREAKPOINT)
    )
  );


  // vplan:EbreakuOff

  sequence  seq_ebreak_umode_noebreaku;
    is_rvfi_ebreak         &&
    (rvfi_mode == MODE_U)  &&
    !rvfi_csr_dcsr_rdata[EBREAKU_POS+:EBREAKU_LEN]
    ;
  endsequence : seq_ebreak_umode_noebreaku

  a_ebreaku_off_trap: assert property (
    seq_ebreak_umode_noebreaku
    |->
    rvfi_trap.trap
  ) else `uvm_error(info_tag, "umode ebreak wo/ ebreaku should cause a trap");

  a_ebreaku_off_exception: assert property (
    seq_ebreak_umode_noebreaku
    |->
    rvfi_trap.exception
  ) else `uvm_error(info_tag, "umode ebreak wo/ ebreaku should cause an exception");

  a_ebreaku_off_cause: assert property (
    seq_ebreak_umode_noebreaku
    |->
    (rvfi_trap.exception_cause == EXC_CAUSE_BREAKPOINT)
  ) else `uvm_error(info_tag, "umode ebreak wo/ ebreaku should cause an exception");

  a_ebreaku_off_nodebug: assert property (
    seq_ebreak_umode_noebreaku
    |->
    !rvfi_trap.debug  ||
    (rvfi_trap.debug_cause inside {DBG_CAUSE_STEP})
  ) else `uvm_error(info_tag, "umode ebreak wo/ ebreaku should not cause debug entry");

  a_ebreaku_off_nodebugcause: assert property (
    seq_ebreak_umode_noebreaku
    ##1
    (rvfi_valid [->1])
    |->
    (rvfi_dbg != DBG_CAUSE_EBREAK)
  ) else `uvm_error(info_tag, "umode ebreak wo/ ebreaku should not cause dmode");


  // vplan:Ecall  (in umode)

  a_ecall_umode_trap: assert property (
    (is_rvfi_ecall && (rvfi_mode == MODE_U))
    |->
    rvfi_trap.trap
  ) else `uvm_error(info_tag, "umode ecall causes umode ecall exception");

  a_ecall_umode_exception: assert property (
    (is_rvfi_ecall && (rvfi_mode == MODE_U))
    |->
    rvfi_trap.exception
  ) else `uvm_error(info_tag, "umode ecall causes umode ecall exception");

  a_ecall_umode_cause: assert property (
    (is_rvfi_ecall && (rvfi_mode == MODE_U))
    |->
    (rvfi_trap.exception_cause inside {EXC_CAUSE_ECALL_UMODE, 1, 2, 24, 25})  // ("It" or higher)
  ) else `uvm_error(info_tag, "umode ecall causes umode ecall exception");

  a_ecall_umode_poststate: assert property (
    (is_rvfi_ecall && (rvfi_mode == MODE_U))
    |->
    (mcause_poststate[11:0] inside {EXC_CAUSE_ECALL_UMODE, 1, 2, 24, 25})  // ("It" or higher)
  ) else `uvm_error(info_tag, "umode ecall causes umode ecall exception");


  // vplan:ExecuteMmode (in debug)

  a_dmode_mmode: assert property (
    rvfi_valid  &&
    rvfi_dbg_mode
    |->
    (rvfi_mode == MODE_M)
  ) else `uvm_error(info_tag, "dmode must execute in mmode");


  // vplan:ResumePriv

  property p_dret_prv;
    int prv;
    (rvfi_valid && rvfi_dbg_mode)  ##0
    (1, prv = rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN])
    ##1
    (rvfi_valid [->1])  ##0
    !rvfi_dbg_mode
    |->
    (rvfi_mode == prv)  ||
    rvfi_intr.interrupt
    ;
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



  // vplan:ResumeMprv

  a_dret_mprv_umode: assert property (
    (rvfi_valid && rvfi_dbg_mode)
    ##1
    ((rvfi_valid [->1]) ##0 !rvfi_dbg_mode)  ##0
    (rvfi_mode == MODE_U)
    |->
    (rvfi_csr_mstatus_rdata[MPRV_POS+:MPRV_LEN] == 1'b 0)
  ) else `uvm_error(info_tag, "exiting dmode into umode should clear mprv");

  a_dret_mprv_prv: assert property (
    (rvfi_valid && rvfi_dbg_mode)  ##0
    (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] == MODE_U)
    ##1
    ((rvfi_valid [->1]) ##0 !rvfi_dbg_mode)
    |->
    (rvfi_csr_mstatus_rdata[MPRV_POS+:MPRV_LEN] == 1'b 0)
  ) else `uvm_error(info_tag, "exiting dmode towards umode should clear mprv");

  a_dret_mprv_csr: assert property (
    rvfi_if.is_dret  &&
    (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] == MODE_U)  &&
    rvfi_if.rvfi_dbg_mode
    |->
    (rvfi_csr_mstatus_wmask[MPRV_POS+:MPRV_LEN] == 1'b 1)  &&
    (rvfi_csr_mstatus_wdata[MPRV_POS+:MPRV_LEN] == 1'b 0)
  ) else `uvm_error(info_tag, "dret to umode clears mprv immediately");


  // vplan:UmodeUnmodified (wrt MPRV)

  a_umode_unmodified: assert property (
    rvfi_valid  &&
    (rvfi_mode == MODE_U)
    |->
    (rvfi_csr_mstatus_rdata[MPRV_POS+:MPRV_LEN] == 1'b 0)
  ) else `uvm_error(info_tag, "umode should have no way of running with modified privilege");


  // vplan:UserExtensions

  a_umode_extensions: assert property (
    rvfi_valid
    |->
    !rvfi_csr_mstatus_rdata[XS_POS+:XS_LEN]  &&
    !rvfi_csr_mstatus_rdata[FS_POS+:FS_LEN]  &&
    !rvfi_csr_mstatus_rdata[SD_POS+:SD_LEN]
  ) else `uvm_error(info_tag, "none of the mstatus umode extension bits shall be used");


  // vplan:IllegalAccess

  a_illegal_csr_access: assert property (
    is_rvfi_csrinstr       &&
    (rvfi_mode == MODE_U)  &&
    (rvfi_insn[29:28] != MODE_U)
    |->
    is_rvfi_illegalinsn  ^
    (rvfi_trap.exception_cause inside {1, 24, 25})  // Higher priority exceptions
  ) else `uvm_error(info_tag, "access to higher lvl csrs is illegal");


  // vplan:MretMpp

  property p_mret_from_mpp (int mode);
    is_rvfi_mret  &&
    (rvfi_mode == MODE_M)  &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] == mode)  &&
    !rvfi_trap  &&
    !rvfi_dbg_mode
    ##1
    (rvfi_valid [->1])  ##0
    !rvfi_intr.interrupt  &&
    !rvfi_dbg_mode
    |->
    (rvfi_mode == mode);
  endproperty : p_mret_from_mpp

  a_mret_from_mpp_umode: assert property (
    p_mret_from_mpp(MODE_U)
  ) else `uvm_error(info_tag, "mret should result in privmode from mstatus.mpp (umode)");

  a_mret_from_mpp_mmode: assert property (
    p_mret_from_mpp(MODE_M)
  ) else `uvm_error(info_tag, "mret should result in privmode from mstatus.mpp (mmode)");


  // vplan:Mret  (in umode)

  a_mret_umode_exception: assert property (
    (is_rvfi_mret && (rvfi_mode == MODE_U))
    |->
    is_rvfi_illegalinsn  ^
    (rvfi_trap.exception_cause inside {1, 24, 25})  // Higher priority exceptions
  ) else `uvm_error(info_tag, "mret in umode is illegal");

  a_mret_umode_nextmode: assert property (
    (is_rvfi_mret && (rvfi_mode == MODE_U))
    ##1
    (rvfi_valid [->1])
    |->
    (rvfi_mode == MODE_M)
  ) else `uvm_error(info_tag, "mret in umode traps to mmode");

  a_mret_umode_mpp: assert property (
    (is_rvfi_mret && (rvfi_mode == MODE_U))
    ##1
    (rvfi_valid [->1])
    |->
    (
      (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] == MODE_U)  ||
      rvfi_intr.interrupt
    )
  ) else `uvm_error(info_tag, "mret in umode sets mpp to umode, unless interrupted");

  // a_mret_umode_mprv - Handled by a_umodetrap_zeromprv.


  // vplan:McounterenClear & vplan:McounterenSet & vplan:Mcounteren

  for (genvar i = 0; i < 31; i++) begin : gen_mcounteren_clear
    a_check: assert property (
      is_rvfi_csrinstr                        &&
      (rvfi_mode == MODE_U)                   &&
      (rvfi_insn[31:20] == CSRADDR_HPM0 + i)  &&
      !rvfi_csr_mcounteren_rdata[i]
      |->
      is_rvfi_illegalinsn     ^
      is_rvfi_instrtriggered  ^
      (rvfi_trap.exception_cause inside {1, 24, 25})  // Higher priority exceptions
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


  // vplan:Jvt

  a_jvt_access: assert property (
    is_rvfi_csrinstr  &&
    (rvfi_insn[31:20] == CSRADDR_JVT)
    |->
    !is_rvfi_illegalinsn  ||
    (!rvfi_csr_mstateen0_rdata[2] && (rvfi_mode == MODE_U))
  ) else `uvm_error(info_tag, "jvt csr should be rw in both modes");


  // vplan:SoftwareInterrupts

  property p_softwareinterrupts_zeros(logic [31:0] csr);
    rvfi_valid
    |->
      //[31:16]
    !csr[15:12]  &&
      //[11:11]
    !csr[10: 8]  &&
      //[ 7: 7]
    !csr[ 6: 4]  &&
      //[ 3: 3]
    !csr[ 2: 0]
    ;
  endproperty : p_softwareinterrupts_zeros

  a_softwareinterrupts_zeromie: assert property (
    p_softwareinterrupts_zeros(rvfi_csr_mie_rdata)
  ) else `uvm_error(info_tag, "certain bits in 'mie' must be zero");

  a_softwareinterrupts_zeromip: assert property (
    p_softwareinterrupts_zeros(rvfi_csr_mip_rdata)
  ) else `uvm_error(info_tag, "certain bits in 'mip' must be zero");

  if (!CLIC) begin: gen_softwareinterrupts_mcausemode
    a_softwareinterrupts_mcausemode: assert property (
      rvfi_intr.interrupt
      |->
      !(rvfi_intr.cause inside {[0:2], [4:6], [8:10], [12:15]})
    ) else `uvm_error(info_tag, "unexpected interrupt cause");
  end : gen_softwareinterrupts_mcausemode


  // vplan:NExt

  a_next_csrs: assert property (
    is_rvfi_csrinstr  &&
    (rvfi_insn[31:20] inside {
      CSRADDR_USTATUS, CSRADDR_UIE, CSRADDR_UTVEC, CSRADDR_USCRATCH,
      CSRADDR_UEPC, CSRADDR_UCAUSE, CSRADDR_UTVAL, CSRADDR_UIP
      }
    )
    |->
    is_rvfi_illegalinsn  ^
    (rvfi_trap.exception_cause inside {1, 24, 25})  // Higher priority exceptions
  ) else `uvm_error(info_tag, "none of the n ext csrs should be present");


  // vplan:ExecuteMprven  (in debug)

  a_mprven_tied: assert property (
    rvfi_valid
    |->
    (rvfi_csr_dcsr_rdata[MPRVEN_POS+:MPRVEN_LEN] == 1'b 1)
  ) else `uvm_error(info_tag, "dcsr.mprven is not supported");


  // vplan:PrvEntry

  property  p_prv_entry;
    (rvfi_valid && !rvfi_dbg_mode)
    ##1
    (rvfi_valid [->1])  ##0
    rvfi_dbg_mode
    |->
    if (!rvfi_intr[0]) (
      (rvfi_csr_dcsr_rdata[PRV_POS+:PRV_LEN] == was_rvfi_mode_wdata)
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


  // vplan:PrvSupported

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


  // vplan:MedelegMideleg

  a_medeleg_mideleg: assert property (
    is_rvfi_csrinstr  &&
    (rvfi_insn[31:20] inside {CSRADDR_MEDELEG, CSRADDR_MIDELEG})
    |->
    is_rvfi_illegalinsn  ^
    (rvfi_trap.exception_cause inside {1, 24, 25})  // Higher priority exceptions
  ) else `uvm_error(info_tag, "medeleg and mideleg registers should not exist");


  // vplan:InstrProt

  a_instr_prot: assert property (
    rvfi_valid
    |->
    (rvfi_if.instr_prot[2:1] == rvfi_if.rvfi_mode)  ||
    (rvfi_if.rvfi_trap.exception_cause == cv32e40s_pkg::EXC_CAUSE_INSTR_FAULT)  ||
    (rvfi_trap.debug_cause == DBG_CAUSE_TRIGGER)
    //Note: Triggers can overshadow access faults
  ) else `uvm_error(info_tag, "the prot on fetch must match the mode on retirement");

  a_instr_prot_legal: assert property (
    rvfi_valid  &&
    (rvfi_if.rvfi_trap.exception_cause != cv32e40s_pkg::EXC_CAUSE_INSTR_FAULT)
    |->
    (rvfi_if.instr_prot[2:0] inside {3'b 000, 3'b 110})
  ) else `uvm_error(info_tag, "instr_prot illegal value");

  a_prot_iside_legal: assert property (
    obi_iside_prot  inside  {3'b 000, 3'b 110}
  ) else `uvm_error(info_tag, "the prot on fetch must be legal");


  // vplan:DataProt

  a_data_prot: assert property (
    rvfi_valid  &&
    (rvfi_if.rvfi_mem_rmask || rvfi_if.rvfi_mem_wmask)
    |->
    (rvfi_if.mem_prot[2:1] == effective_rvfi_privmode)
  ) else `uvm_error(info_tag, "the prot on load/store must match the effective mode on retirement");

  a_data_prot_legal: assert property (
    rvfi_valid  &&
    (rvfi_if.rvfi_trap.exception_cause != cv32e40s_pkg::EXC_CAUSE_INSTR_FAULT)
    |->
    (rvfi_if.mem_prot[2:0] inside {3'b 001, 3'b 111})
  ) else `uvm_error(info_tag, "data_prot illegal value");

  a_prot_dside_legal: assert property (
    obi_dside_prot  inside  {3'b 001, 3'b 111}
  ) else `uvm_error(info_tag, "the prot on loadstore must be legal");

  wire logic [NMEM-1:0]  data_prot_equals;
  wire logic [NMEM-1:0]  mem_act;
  for (genvar i = 0; i < NMEM; i++) begin: gen_data_prot_equals
    assign  data_prot_equals[i] = (rvfi_if.mem_prot[i*3+:3] == rvfi_if.mem_prot[2:0]);
    assign  mem_act[i]          = |rvfi_if.check_mem_act(i);
  end

  a_data_prot_equal: assert property (
    rvfi_valid  &&
    (|rvfi_if.rvfi_mem_rmask || |rvfi_if.rvfi_mem_wmask)
    |->
    ((data_prot_equals & mem_act) == mem_act)
  ) else `uvm_error(info_tag, "data prot should match accesses from same instr");

  cov_data_prot_equal_memact_load: cover property (
    rvfi_valid  &&
    ($countones(mem_act) > 1)  &&
    (|rvfi_if.rvfi_mem_rmask)
  );

  cov_data_prot_equal_memact_store: cover property (
    rvfi_valid  &&
    ($countones(mem_act) > 1)  &&
    (|rvfi_if.rvfi_mem_wmask)
  );


  // vplan:DbgProt

  a_dbg_prot_iside: assert property (
    rvfi_if.rvfi_valid  &&
    rvfi_if.rvfi_dbg_mode
    |->
    (rvfi_if.instr_prot[2:1] == MODE_M)  ||
    (rvfi_if.rvfi_trap.exception_cause == cv32e40s_pkg::EXC_CAUSE_INSTR_FAULT)
  ) else `uvm_error(info_tag, "dmode should fetch as mmode");

  a_dbg_prot_dside: assert property (
    rvfi_if.rvfi_dbg_mode  &&
    rvfi_valid  &&
    (|rvfi_if.rvfi_mem_rmask || |rvfi_if.rvfi_mem_wmask)
    |->
    (rvfi_if.mem_prot[2:1] == effective_rvfi_privmode)
  ) else `uvm_error(info_tag, "dmode should fetch as effective mode");


endmodule : uvmt_cv32e40s_umode_assert


`default_nettype  wire
