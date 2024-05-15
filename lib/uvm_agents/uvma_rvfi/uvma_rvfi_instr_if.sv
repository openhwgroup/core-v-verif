// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVMA_RVFI_INSTR_IF_SV__
`define __UVMA_RVFI_INSTR_IF_SV__

/**
 * Encapsulates all signals and clocking of RVFI Instruction interface. Used by
 * monitor,
 */
interface uvma_rvfi_instr_if_t
  import isa_decoder_pkg::*;
  import uvm_pkg::*;
  import uvma_rvfi_pkg::*;

  #(int ILEN=uvma_rvfi_pkg::DEFAULT_ILEN,
    int XLEN=uvma_rvfi_pkg::DEFAULT_XLEN)
  (
    input logic                      clk,
    input logic                      reset_n,

    input logic                      rvfi_valid,
    input logic [ORDER_WL-1:0]       rvfi_order,
    input logic [ILEN-1:0]           rvfi_insn,
    input rvfi_trap_t                rvfi_trap,
    input logic                      rvfi_halt,
    input logic [RVFI_DBG_WL-1:0]    rvfi_dbg,
    input logic                      rvfi_dbg_mode,
    input logic [RVFI_NMIP_WL-1:0]   rvfi_nmip,
    input rvfi_intr_t                rvfi_intr,
    input logic [MODE_WL-1:0]        rvfi_mode,
    input logic [IXL_WL-1:0]         rvfi_ixl,
    input logic [XLEN-1:0]           rvfi_pc_rdata,
    input logic [XLEN-1:0]           rvfi_pc_wdata,

    input logic [GPR_ADDR_WL-1:0]    rvfi_rs1_addr,
    input logic [XLEN-1:0]           rvfi_rs1_rdata,

    input logic [GPR_ADDR_WL-1:0]    rvfi_rs2_addr,
    input logic [XLEN-1:0]           rvfi_rs2_rdata,

    input logic [GPR_ADDR_WL-1:0]    rvfi_rs3_addr,
    input logic [XLEN-1:0]           rvfi_rs3_rdata,

    input logic [GPR_ADDR_WL-1:0]    rvfi_rd1_addr,
    input logic [XLEN-1:0]           rvfi_rd1_wdata,

    input logic [GPR_ADDR_WL-1:0]    rvfi_rd2_addr,
    input logic [XLEN-1:0]           rvfi_rd2_wdata,

    input logic [(32*XLEN)-1:0]      rvfi_gpr_rdata,
    input logic [(32)-1:0]           rvfi_gpr_rmask,
    input logic [(32*XLEN)-1:0]      rvfi_gpr_wdata,
    input logic [(32)-1:0]           rvfi_gpr_wmask,

    input logic [(NMEM*XLEN)-1:0]    rvfi_mem_addr,
    input logic [(NMEM*XLEN)-1:0]    rvfi_mem_rdata,
    input logic [(NMEM*XLEN/8)-1:0]  rvfi_mem_rmask,
    input logic [(NMEM*XLEN)-1:0]    rvfi_mem_wdata,
    input logic [(NMEM*XLEN/8)-1:0]  rvfi_mem_wmask,
    
    input logic [2:0]                rvfi_instr_prot,
    input logic [1:0]                rvfi_instr_memtype,
    input logic                      rvfi_instr_dbg,
    input logic [ NMEM*3-1:0]        rvfi_mem_prot,
    input logic [ 1*NMEM-1:0]        rvfi_mem_exokay,
    input logic [ 1*NMEM-1:0]        rvfi_mem_err,
    input logic [ 6*NMEM-1:0]        rvfi_mem_atop,
    input logic [ 2*NMEM-1:0]        rvfi_mem_memtype,
    input logic [ NMEM-1  :0]        rvfi_mem_dbg
  );

  typedef logic[4*NMEM-1:0] mem_mask_t;

  // -------------------------------------------------------------------
  // Local param
  // -------------------------------------------------------------------
  //instruction (rvfi_instr) masks

  localparam INSTR_MASK_DIV_REM     = 32'h FE00_607F;
  localparam INSTR_MASK_FULL          = 32'h FFFF_FFFF;
  localparam INSTR_MASK_R_TYPE        = 32'h FE00_707F;
  localparam INSTR_MASK_AMO_TYPE      = 32'h F800_707F;
  localparam INSTR_MASK_I_S_B_TYPE    = 32'h 0000_707F;
  localparam INSTR_MASK_U_J_TYPE      = 32'h 0000_007F;
  localparam INSTR_MASK_CSRADDR       = 32'h FFF0_0000;
  localparam INSTR_MASK_CSRUIMM       = 32'h 000F_8000;
  localparam INSTR_MASK_CMPR          = 32'h FFFF_E003;
  localparam INSTR_MASK_OPCODE        = 32'h 0000_007F;
  localparam INSTR_MASK_ZC_PUSHPOP    = 32'h FFFF_FF03;
  localparam INSTR_MASK_ZC_CLBU_CSB   = 32'h FFFF_FC03;
  localparam INSTR_MASK_CLH_CLHU_CSH  = 32'b 1111_1111_1111_1111_1111_1100_0100_0011;


  //instruction (rvfi_instr) comparison values
  localparam INSTR_OPCODE_DRET      = 32'h 7B20_0073;
  localparam INSTR_OPCODE_MRET      = 32'h 3020_0073;
  localparam INSTR_OPCODE_URET      = 32'h 0020_0073;
  localparam INSTR_OPCODE_WFI       = 32'h 1050_0073;
  localparam INSTR_OPCODE_WFE       = 32'h 8C00_0073;
  localparam INSTR_OPCODE_EBREAK    = 32'h 0010_0073;
  localparam INSTR_OPCODE_C_EBREAK  = 32'h 0000_9002;
  localparam INSTR_OPCODE_ECALL     = 32'h 0000_0073;
  localparam INSTR_OPCODE_CSLLI     = 32'h 0000_0002;

  localparam INSTR_OPCODE_DIV       = 32'h 0200_4033;
  localparam INSTR_OPCODE_REM       = 32'h 0200_6033;

  localparam INSTR_OPCODE_CSRRW     = 32'h 0000_1073;
  localparam INSTR_OPCODE_CSRRS     = 32'h 0000_2073;
  localparam INSTR_OPCODE_CSRRC     = 32'h 0000_3073;
  localparam INSTR_OPCODE_CSRRWI    = 32'h 0000_5073;
  localparam INSTR_OPCODE_CSRRSI    = 32'h 0000_6073;
  localparam INSTR_OPCODE_CSRRCI    = 32'h 0000_7073;

  localparam INSTR_OPCODE_BEQ       = 32'h0000_0063;
  localparam INSTR_OPCODE_BNE       = 32'h0000_1063;
  localparam INSTR_OPCODE_BLT       = 32'h0000_4063;
  localparam INSTR_OPCODE_BGE       = 32'h0000_5063;
  localparam INSTR_OPCODE_BLTU      = 32'h0000_6063;
  localparam INSTR_OPCODE_BGEU      = 32'h0000_7063;

  localparam INSTR_OPCODE_CBEQZ  = 32'h 0000_C001;
  localparam INSTR_OPCODE_CBNEZ  = 32'h 0000_E001;

  localparam INSTR_MASK_PUSHPOP   = 32'b 11111111_11111111_111_11111_0000_00_11;

  localparam INSTR_OPCODE_PUSH    = 32'b 00000000_00000000_101_11000_0000_00_10;
  localparam INSTR_OPCODE_POP     = 32'b 00000000_00000000_101_11010_0000_00_10;
  localparam INSTR_OPCODE_POPRET  = 32'b 00000000_00000000_101_11110_0000_00_10;
  localparam INSTR_OPCODE_POPRETZ = 32'b 00000000_00000000_101_11100_0000_00_10;

  localparam INSTR_MASK_TABLEJUMP   = 32'b 11111111_11111111_111_111_00000000_11;
  localparam INSTR_OPCODE_TABLEJUMP = 32'b 00000000_00000000_101_000_00000000_10;

  localparam INSTR_MASK_FENCE    = 32'b 00000000000000000_111_00000_1111111;
  localparam INSTR_OPCODE_FENCE  = 32'b 00000000000000000_000_00000_0001111;
  localparam INSTR_MASK_FENCEI   = 32'b 00000000000000000_111_00000_1111111;
  localparam INSTR_OPCODE_FENCEI = 32'b 00000000000000000_001_00000_0001111;

  localparam INSTR_OPCODE_LOAD    = 32'b 0000_0000_0000_0000_0000_0000_0000_0011;
  localparam INSTR_OPCODE_STORE  = 32'b 00000000_00000000_00000000_0_0100011;

  localparam INSTR_OPCODE_LH    = 32'b00000000000000000_001_00000_0000011;
  localparam INSTR_OPCODE_LHU   = 32'b00000000000000000_101_00000_0000011;
  localparam INSTR_OPCODE_LW    = 32'b00000000000000000_010_00000_0000011;
  localparam INSTR_OPCODE_SH    = 32'b00000000000000000_001_00000_0100011;
  localparam INSTR_OPCODE_SHU   = 32'b00000000000000000_001_00000_0100011;
  localparam INSTR_OPCODE_SW    = 32'b00000000000000000_010_00000_0100011;
  localparam INSTR_OPCODE_CLW   = 32'b0000000000000000_010_000000000_0000;
  localparam INSTR_OPCODE_CSW   = 32'b0000000000000000_110_000000000_0000;
  localparam INSTR_OPCODE_CLWSP = 32'b0000000000000000_010_000000000_0010;
  localparam INSTR_OPCODE_CSWSP = 32'b0000000000000000_110_000000000_0010;
  localparam INSTR_OPCODE_CSH   = 32'b0000000000000000_100_011_00000000_00;
  localparam INSTR_OPCODE_CSB   = 32'b0000000000000000_100_010_00000000_00;
  localparam INSTR_OPCODE_CLBU  = 32'b 00000000_00000000_100_000_000_00_000_00;
  localparam INSTR_OPCODE_CLHU  = 32'b 00000000_00000000_100_001_000_0_0_000_00;
  localparam INSTR_OPCODE_CLH   = 32'b 00000000_00000000_100_001_000_1_0_000_00;

  localparam INSTR_OPCODE_CMPOP      = 32'b 00000000_00000000_101_11010_0000_00_10;
  localparam INSTR_OPCODE_CMPOPRET   = 32'b 00000000_00000000_101_11110_0000_00_10;
  localparam INSTR_OPCODE_CMPOPRETZ  = 32'b 00000000_00000000_101_11100_0000_00_10;

  localparam INSTR_OPCODE_LRW       = 32'b 00010_0_0_00000_00000_010_00000_0101111;
  localparam INSTR_OPCODE_SCW       = 32'b 00011_0_0_00000_00000_010_00000_0101111;
  localparam INSTR_OPCODE_AMOSWAPW  = 32'b 00001_0_0_00000_00000_010_00000_0101111;
  localparam INSTR_OPCODE_AMOADDW   = 32'b 00000_0_0_00000_00000_010_00000_0101111;
  localparam INSTR_OPCODE_AMOXORW   = 32'b 00100_0_0_00000_00000_010_00000_0101111;
  localparam INSTR_OPCODE_AMOANDW   = 32'b 01100_0_0_00000_00000_010_00000_0101111;
  localparam INSTR_OPCODE_AMOORW    = 32'b 01000_0_0_00000_00000_010_00000_0101111;
  localparam INSTR_OPCODE_AMOMINW   = 32'b 10000_0_0_00000_00000_010_00000_0101111;
  localparam INSTR_OPCODE_AMOMAXW   = 32'b 10100_0_0_00000_00000_010_00000_0101111;
  localparam INSTR_OPCODE_AMOMINUW  = 32'b 11000_0_0_00000_00000_010_00000_0101111;
  localparam INSTR_OPCODE_AMOMAXUW  = 32'b 11100_0_0_00000_00000_010_00000_0101111;

  //positions
  localparam int INSTR_CSRADDR_POS  = 20;
  localparam int INSTR_CSRUIMM_POS  = 15;


  localparam INTR_CAUSE_NMI_MASK    = 11'h 400;



  // -------------------------------------------------------------------
  // Local variables
  // -------------------------------------------------------------------
  int unsigned                      irq_cnt;         // number of taken interrupts
  int unsigned                      nmi_instr_cnt;   // number of instructions after nmi
  int unsigned                      single_step_cnt; // number of instructions stepped
  logic [CYCLE_CNT_WL-1:0]          cycle_cnt;       // i'th number cycle since reset
  logic [CYCLE_CNT_WL-1:0]          cycle_cnt_q;

  string                            info_tag = "RVFI_INSTR_IF";

  logic [(32)-1:0][XLEN-1:0]        gpr_rdata_array;
  logic [(32)-1:0]                  gpr_rmask_array;
  logic [(32)-1:0][XLEN-1:0]        gpr_wdata_array;
  logic [(32)-1:0]                  gpr_wmask_array;
  logic [NMEM-1:0][XLEN-1:0]        mem_addr_array;
  logic [NMEM-1:0][XLEN-1:0]        mem_rdata_array;
  logic [NMEM-1:0][(XLEN/8)-1:0]    mem_rmask_array;
  logic [NMEM-1:0][XLEN-1:0]        mem_wdata_array;
  logic [NMEM-1:0][(XLEN/8)-1:0]    mem_wmask_array;

  logic [(5)-1:0]                   csri_uimm;
  logic [5:0]                       cslli_shamt;
  logic [11:0]                      csr_addr;

  logic                             is_dret;
  logic                             is_mret;
  logic                             is_uret;
  logic                             is_wfi;
  logic                             is_wfe;
  logic                             is_ebreak;
  logic                             is_ebreak_compr;
  logic                             is_ebreak_noncompr;
  logic                             is_ecall;
  logic                             is_branch;
  logic                             is_div;
  logic                             is_rem;
  logic                             is_cslli;
  logic                             is_nmi;
  logic                             is_compressed;
  logic                             is_dbg_trg;
  logic                             is_mmode;
  logic                             is_not_mmode;
  logic                             is_umode;
  logic                             is_not_umode;
  logic                             is_pma_instr_fault;
  logic                             is_instr_acc_fault_pmp;
  logic                             is_instr_bus_valid;
  logic                             is_pushpop;
  logic                             is_split_datatrans_actual;
  logic                             is_split_datatrans_intended;
  logic                             is_split_instrtrans;
  logic                             is_mem_act;
  logic                             is_mem_act_actual;
  logic                             is_mem_act_intended;
  logic                             is_tablejump_raw;
  logic                             is_pma_fault;
  logic                             is_fencefencei;
  logic                             is_nmi_triggered;
  logic                             is_load_instr;
  logic                             is_store_instr;
  logic                             is_amo_instr;
  logic                             is_atomic_instr;
  logic                             is_loadstore_instr;
  logic                             is_exception;
  logic                             is_load_acc_fault;
  logic                             is_store_acc_fault;
  logic                             is_deprioritized_load_acc_fault;
  logic                             is_deprioritized_store_acc_fault;
  logic [31:0]                      rvfi_mem_addr_word0highbyte;
  logic [31:0]                      rvfi_pc_upperrdata;
  logic [4*NMEM-1:0]                rvfi_mem_rmask_intended;
  logic [4*NMEM-1:0]                rvfi_mem_wmask_intended;

  asm_t instr_asm;

  // -------------------------------------------------------------------
  // Begin module code
  // -------------------------------------------------------------------

  // these signals are added to make it easier to use the signal arrays,
  // and to inspect them in the waveforms
  // gpr masks are redundant, but added for ease of use
  assign {>>{gpr_rdata_array}} = rvfi_gpr_rdata;
  assign gpr_rmask_array       = rvfi_gpr_rmask;
  assign {>>{gpr_wdata_array}} = rvfi_gpr_wdata;
  assign gpr_wmask_array       = rvfi_gpr_wmask;


  assign {>>{mem_addr_array}}  = rvfi_mem_addr;
  assign {>>{mem_rdata_array}} = rvfi_mem_rdata;
  assign {>>{mem_rmask_array}} = rvfi_mem_rmask;
  assign {>>{mem_wdata_array}} = rvfi_mem_wdata;
  assign {>>{mem_wmask_array}} = rvfi_mem_wmask;

  assign csri_uimm   = rvfi_insn[19:15];
  assign cslli_shamt = {rvfi_insn[12], rvfi_insn[6:2]};
  assign csr_addr    = rvfi_insn[31:20];

  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      irq_cnt          <= 0;
      is_nmi_triggered <= 0;
      nmi_instr_cnt    <= 0;
      single_step_cnt  <= 0;
    end else begin
      // Detect taken nmi or pending nmi and start counting
      is_nmi_triggered <= is_nmi_triggered ? 1'b1 : (is_nmi || (rvfi_nmip && rvfi_valid));
      if (is_nmi_triggered && rvfi_valid) begin
        nmi_instr_cnt <= nmi_instr_cnt + 1;
      end
      single_step_cnt <= (rvfi_dbg[2:0] == 3'h4 && rvfi_valid) ? single_step_cnt + 1 : single_step_cnt;
      irq_cnt <= ((rvfi_intr.intr == 1) && (rvfi_intr.interrupt == 1) && rvfi_valid) ? irq_cnt + 1 : irq_cnt;
    end
  end

  always_ff @(posedge clk) begin
    cycle_cnt_q <= cycle_cnt;
  end

  // assigning signal aliases to helper functions
  // These signals may be have dependencies on each other, thus to
  // avoid having to micromanage order of execution, they are split
  // into separate always_comb blocks. Assign will not work due to
  // sensitivity list issues with functions, and a single always_comb
  // block will cause issues due to clause b in section 9.2.2.2.1 of
  // ieee 1800-2017
  always_comb begin
    instr_asm                        = decode_instr(rvfi_insn);
  end

  always_comb begin
    is_dret                          = is_dret_f();
  end

  always_comb begin
    is_mret                          = is_mret_f();
  end

  always_comb begin
    is_uret                          = is_uret_f();
  end

  always_comb begin
    is_wfi                           = is_wfi_f();
  end

  always_comb begin
    is_wfe                           = is_wfe_f();
  end

  always_comb begin
    is_ebreak                        = is_ebreak_f();
  end

  always_comb begin
    is_ebreak_compr                  = is_ebreak_compr_f();
  end

  always_comb begin
    is_ebreak_noncompr               = is_ebreak_noncompr_f();
  end

  always_comb begin
    is_ecall                         = is_ecall_f();
  end

  always_comb begin
    is_branch                        = is_branch_f();
  end

  always_comb begin
    is_div                           = is_div_f();
  end

  always_comb begin
    is_rem                           = is_rem_f();
  end

  always_comb begin
    is_cslli                         = is_cslli_f();
  end

  always_comb begin
    is_nmi                           = is_nmi_f();
  end

  always_comb begin
    is_compressed                    = is_compressed_f();
  end

  always_comb begin
    is_dbg_trg                       = is_dbg_trg_f();
  end

  always_comb begin
    is_mmode                         = is_mmode_f();
  end

  always_comb begin
    is_not_mmode                     = is_not_mmode_f();
  end

  always_comb begin
    is_umode                         = is_umode_f();
  end

  always_comb begin
    is_not_umode                     = is_not_umode_f();
  end

  always_comb begin
    is_pma_instr_fault               = is_pma_instr_fault_f();
  end

  // TODO: always_comb does not work here with VSIM
`ifndef QUESTA_VSIM
  always_comb begin
`else
  always @(rvfi_trap.exception_cause) begin
`endif // QUESTA_VSIM
    is_instr_bus_valid               = is_instr_bus_valid_f();
  end

  always_comb begin
    is_pushpop                       = is_pushpop_f();
  end

  always_comb begin
    is_split_datatrans_actual        = is_split_datatrans_actual_f();
  end

  always_comb begin
    is_split_datatrans_intended      = is_split_datatrans_intended_f();
  end

  always_comb begin
    is_mem_act                       = is_mem_act_f();
  end

  always_comb begin
    is_tablejump_raw                 = is_tablejump_raw_f();
  end

  always_comb begin
    is_pma_fault                     = is_pma_fault_f();
  end

  always_comb begin
    is_fencefencei                   = is_fencefencei_f();
  end

  always_comb begin
    rvfi_mem_addr_word0highbyte      = rvfi_mem_addr_word0highbyte_f();
  end

  // TODO: always_comb does not work here with VSIM
`ifndef QUESTA_VSIM
  always_comb begin
`else
  always @(rvfi_insn) begin
`endif // QUESTA_VSIM
    rvfi_mem_rmask_intended          = rvfi_mem_rmask_intended_f();
  end

  // TODO: always_comb does not work here with VSIM
`ifndef QUESTA_VSIM
  always_comb begin
`else
  always @(rvfi_insn) begin
`endif // QUESTA_VSIM
    rvfi_mem_wmask_intended          = rvfi_mem_wmask_intended_f();
  end

  always_comb begin
    is_deprioritized_load_acc_fault  = is_deprioritized_exception_f({21'd 0, EXC_CAUSE_LOAD_ACC_FAULT});
  end

  always_comb begin
    is_deprioritized_store_acc_fault = is_deprioritized_exception_f({21'd 0, EXC_CAUSE_STORE_ACC_FAULT});
  end

  always_comb begin
    cycle_cnt = !reset_n ? 0 : (cycle_cnt_q + 1'b 1);
  end

  always_comb begin
    is_load_instr = rvfi_valid && |rvfi_mem_rmask_intended;
  end

  always_comb begin
    is_store_instr = rvfi_valid && |rvfi_mem_wmask_intended;
  end

  always_comb begin
    is_amo_instr = rvfi_valid && (
      rvfi_match_instr(INSTR_OPCODE_AMOSWAPW,  INSTR_MASK_AMO_TYPE)    ||
      rvfi_match_instr(INSTR_OPCODE_AMOADDW,   INSTR_MASK_AMO_TYPE)    ||
      rvfi_match_instr(INSTR_OPCODE_AMOXORW,   INSTR_MASK_AMO_TYPE)    ||
      rvfi_match_instr(INSTR_OPCODE_AMOANDW,   INSTR_MASK_AMO_TYPE)    ||
      rvfi_match_instr(INSTR_OPCODE_AMOORW,    INSTR_MASK_AMO_TYPE)    ||
      rvfi_match_instr(INSTR_OPCODE_AMOMINW,   INSTR_MASK_AMO_TYPE)    ||
      rvfi_match_instr(INSTR_OPCODE_AMOMAXW,   INSTR_MASK_AMO_TYPE)    ||
      rvfi_match_instr(INSTR_OPCODE_AMOMINUW,  INSTR_MASK_AMO_TYPE)    ||
      rvfi_match_instr(INSTR_OPCODE_AMOMAXUW,  INSTR_MASK_AMO_TYPE));
  end

  always_comb begin
    is_atomic_instr = rvfi_valid && (is_amo_instr ||
      rvfi_match_instr(INSTR_OPCODE_SCW,  INSTR_MASK_AMO_TYPE) ||
      rvfi_match_instr(INSTR_OPCODE_LRW,  INSTR_MASK_AMO_TYPE));
  end

  always_comb begin
    is_loadstore_instr = is_load_instr || is_store_instr;
  end

  always_comb begin
    is_mem_act_actual = is_mem_act;  // original signal is already "actual"
  end

  always_comb begin
    is_mem_act_intended = rvfi_valid  && (|rvfi_mem_rmask_intended || |rvfi_mem_wmask_intended);
  end

  always_comb begin
    rvfi_pc_upperrdata =
      (rvfi_insn[1:0] == 2'b 11) ? (
        rvfi_pc_rdata + 3
      ) : (
        rvfi_pc_rdata + 1
      );
      // WARNING: Can't trust rvfi_insn if scrambled data.
      // TODO:WARNING:silabs-robin  Can it be modelled exact?
  end

  always_comb begin
    is_split_instrtrans =
      rvfi_valid  &&
      (rvfi_pc_rdata[31:2] != rvfi_pc_upperrdata[31:2]);
  end

  always_comb begin
    is_exception =
      rvfi_valid  &&
      rvfi_trap.trap  &&
      rvfi_trap.exception;
  end

  always_comb begin
    is_instr_acc_fault_pmp =
      is_exception  &&
      (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_ACC_FAULT)  &&
      (rvfi_trap.cause_type == 'h 1);  // TODO:INFO:silabs-robin  Magic num
  end

  always_comb begin
    is_load_acc_fault =
      is_exception  &&
      (rvfi_trap.exception_cause == EXC_CAUSE_LOAD_ACC_FAULT);
  end

  always_comb begin
    is_store_acc_fault =
      is_exception  &&
      (rvfi_trap.exception_cause == EXC_CAUSE_STORE_ACC_FAULT);
  end

  /**
      * Used by target DUT.
  */
  clocking dut_cb @(posedge clk or reset_n);
  endclocking : dut_cb

  /**
      * Used by uvma_rvfi_instr_mon_c.
  */
  clocking mon_cb @(posedge clk or reset_n);
      input #1step
        cycle_cnt,
        nmi_instr_cnt,
        rvfi_valid,
        rvfi_order,
        rvfi_insn,
        rvfi_trap,
        rvfi_halt,
        rvfi_dbg,
        rvfi_dbg_mode,
        rvfi_nmip,
        rvfi_intr,
        rvfi_mode,
        rvfi_ixl,
        rvfi_pc_rdata,
        rvfi_pc_wdata,
        rvfi_rs1_addr,
        rvfi_rs1_rdata,
        rvfi_rs2_addr,
        rvfi_rs2_rdata,
        rvfi_rs3_addr,
        rvfi_rs3_rdata,
        rvfi_rd1_addr,
        rvfi_rd1_wdata,
        rvfi_rd2_addr,
        rvfi_rd2_wdata,
        rvfi_gpr_rdata,
        rvfi_gpr_rmask,
        rvfi_gpr_wdata,
        rvfi_gpr_wmask,
        rvfi_mem_addr,
        rvfi_mem_rdata,
        rvfi_mem_rmask,
        rvfi_mem_wdata,
        rvfi_mem_wmask;
  endclocking : mon_cb

  modport passive_mp    (clocking mon_cb);

  // -------------------------------------------------------------------
  // Functions
  // -------------------------------------------------------------------

  // NOTE: All of these functions are only valid when the RVFI bus holds
  //       valid values, indicated by rvfi_valid == 1

  // Check if instruction is of a certain type
  // Usage: instr_mask sets the parts of the instruction you want to compare,
  //        instr_ref is the reference to match
  function automatic logic rvfi_match_instr(
    logic [ XLEN-1:0] instr_ref,
    logic [ XLEN-1:0] instr_mask
  );

  return rvfi_valid && is_instr_bus_valid && ((rvfi_insn & instr_mask) == instr_ref);

  endfunction : rvfi_match_instr

  // Check if instruction is of a certain type, without verifying the instr word is valid
  // Usage: instr_mask sets the parts of the instruction you want to compare,
  //        instr_ref is the reference to match
  function automatic logic match_instr_raw(
    logic [ XLEN-1:0] instr_ref,
    logic [ XLEN-1:0] instr_mask
  );

  return rvfi_valid && ((rvfi_insn & instr_mask) == instr_ref);

  endfunction : match_instr_raw

// Match instr types
function automatic logic match_instr_r(logic [ XLEN-1:0] instr_ref);
  return rvfi_match_instr(instr_ref, INSTR_MASK_R_TYPE);
endfunction : match_instr_r

function automatic logic match_instr_r_var(
  logic [6:0] funct7,
  logic [2:0] funct3,
  logic [6:0] opcode
);
  return match_instr_r({funct7, 10'b0, funct3, 5'b0, opcode});
endfunction : match_instr_r_var

function automatic logic match_instr_isb(logic [ XLEN-1:0] instr_ref);
  return rvfi_match_instr(instr_ref, INSTR_MASK_I_S_B_TYPE);
endfunction : match_instr_isb

function automatic logic match_instr_isb_var (
  logic [2:0] funct3,
  logic [6:0] opcode
);
  return match_instr_isb({17'b0, funct3, 5'b0, opcode});
endfunction : match_instr_isb_var

function automatic logic match_instr_uj(logic [ XLEN-1:0] instr_ref);
  return  rvfi_match_instr(instr_ref, INSTR_MASK_U_J_TYPE);
endfunction : match_instr_uj

function automatic logic match_instr_uj_var(logic [6:0] opcode);
  return  match_instr_uj({25'b0, opcode});
endfunction : match_instr_uj_var

// Match CSR functions
// These instruction are used to check for csr activity.
// All instructions has the input csr_addr. Setting this limits the query to
// that single address, leaving the input as 0 returns any csr activity.
function automatic logic is_csr_instr(logic [11:0] csr_addr = 0);
  if (csr_addr == 0) begin //not specified
    return  match_instr_isb(INSTR_OPCODE_CSRRW)  ||
            match_instr_isb(INSTR_OPCODE_CSRRS)  ||
            match_instr_isb(INSTR_OPCODE_CSRRC)  ||
            match_instr_isb(INSTR_OPCODE_CSRRWI) ||
            match_instr_isb(INSTR_OPCODE_CSRRSI) ||
            match_instr_isb(INSTR_OPCODE_CSRRCI);
  end else begin
    return  rvfi_match_instr(32'h0 | (csr_addr << INSTR_CSRADDR_POS), INSTR_MASK_CSRADDR) &&
            ( match_instr_isb(INSTR_OPCODE_CSRRW)  ||
              match_instr_isb(INSTR_OPCODE_CSRRS)  ||
              match_instr_isb(INSTR_OPCODE_CSRRC)  ||
              match_instr_isb(INSTR_OPCODE_CSRRWI) ||
              match_instr_isb(INSTR_OPCODE_CSRRSI) ||
              match_instr_isb(INSTR_OPCODE_CSRRCI));
  end
endfunction : is_csr_instr

// This function follows the spec definition of a csr read
function automatic logic is_csr_read(logic [11:0] csr_addr = 0);
  if (  (rvfi_rd1_addr == 0) &&
        (   match_instr_isb(INSTR_OPCODE_CSRRW) ||
            match_instr_isb(INSTR_OPCODE_CSRRWI))) begin
    return 0;
  end else begin
    return is_csr_instr(csr_addr);
  end
endfunction

// This function follows the spec definition of a csr write
function automatic logic is_csr_write(logic [11:0] csr_addr = 0);
  if (  ( (rvfi_rs1_addr == 0) &&
          (   match_instr_isb(INSTR_OPCODE_CSRRS) ||
              match_instr_isb(INSTR_OPCODE_CSRRC))
        ) || (
          ((rvfi_insn & INSTR_MASK_CSRUIMM) == 0) &&
          (   match_instr_isb(INSTR_OPCODE_CSRRSI) ||
              match_instr_isb(INSTR_OPCODE_CSRRCI))
        )) begin
    return 0;
  end else begin
    return is_csr_instr(csr_addr);
  end
endfunction

// returns intended write data for any CSR write instruction,
// without regard for what the legal values are in the CSR
// input current value of the csr, and the csr address
// NOTE: that this will work for CSRRW with unspecified csr address,
// but CSRRS/CSRRC will give incorrect return values
function automatic logic [XLEN-1:0] csr_intended_wdata( logic [XLEN-1:0] csr_rdata,
                                                                logic [11:0] csr_addr = 0);
  if (!is_csr_write(csr_addr)) begin
    return 0;
  end else begin
    if (match_instr_isb(INSTR_OPCODE_CSRRW)) begin
      return rvfi_rs1_rdata;
    end else if (match_instr_isb(INSTR_OPCODE_CSRRWI)) begin
      return (rvfi_insn & INSTR_MASK_CSRUIMM) >> INSTR_CSRUIMM_POS;
    end else if (match_instr_isb(INSTR_OPCODE_CSRRS)) begin
      return csr_rdata | rvfi_rs1_rdata;
    end else if (match_instr_isb(INSTR_OPCODE_CSRRSI)) begin
      return csr_rdata | ((rvfi_insn & INSTR_MASK_CSRUIMM) >> INSTR_CSRUIMM_POS);
     end else if (match_instr_isb(INSTR_OPCODE_CSRRC)) begin
      return csr_rdata & ~rvfi_rs1_rdata;
    end else if (match_instr_isb(INSTR_OPCODE_CSRRCI)) begin
      return csr_rdata & ~((rvfi_insn & INSTR_MASK_CSRUIMM) >> INSTR_CSRUIMM_POS);
    end
  end
endfunction

// Return wdata of register "gpr"
function automatic logic [ XLEN-1:0] get_gpr_wdata( int gpr);
  return rvfi_gpr_wdata[gpr* XLEN +: XLEN];
endfunction : get_gpr_wdata

// Return rdata of register "gpr"
function automatic logic [ XLEN-1:0] get_gpr_rdata( int gpr);
  return rvfi_gpr_rdata[gpr* XLEN +: XLEN];
endfunction : get_gpr_rdata

// Return valid data of memory transaction "txn"
function automatic logic [ XLEN-1:0] get_mem_data_word( int txn);
  bit [ XLEN-1:0] ret;

  for (int i = 0; i <  XLEN/8; i++) begin
    if (rvfi_mem_wmask[(txn* XLEN/8) + i]) begin
      ret[i*8 +:8] = rvfi_mem_wdata[((txn* XLEN) + (i*8)) +:8];
    end else begin
      ret[i*8 +:8] = rvfi_mem_rdata[((txn* XLEN) + (i*8)) +:8];
    end
  end

  return ret;

endfunction : get_mem_data_word

//Return addr of memory transaction "txn"
function automatic logic [ XLEN-1:0] get_mem_addr(int txn);

  return rvfi_mem_addr[txn* XLEN +: XLEN];

endfunction : get_mem_addr

//Return rmask of memory transaction "txn"
function automatic logic [( XLEN/8)-1:0] get_mem_rmask(int txn);

  return rvfi_mem_rmask[(txn* XLEN/8) +:( XLEN/8)];

endfunction : get_mem_rmask

//Return wmask of memory transaction "txn"
function automatic logic [( XLEN/8)-1:0] get_mem_wmask(int txn);

  return rvfi_mem_wmask[(txn* XLEN/8) +:( XLEN/8)];

endfunction : get_mem_wmask


//Check memory transaction activity

//Checks if a position in the rvfi memory transaction list
//indicates any activity.
//return {read, write}
function automatic logic [1:0] check_mem_act(int txn);
  bit read = 0;
  bit write = 0;

  if (rvfi_mem_rmask[(txn* XLEN/8) +:( XLEN/8)]) begin
    read = 1;
  end
  if (rvfi_mem_wmask[(txn* XLEN/8) +:( XLEN/8)]) begin
    write = 1;
  end

  return {read,write};

endfunction : check_mem_act

function automatic logic is_mem_act_f();
  return  rvfi_valid && (|rvfi_mem_rmask || |rvfi_mem_wmask);
endfunction : is_mem_act_f


// Short functions for recognising special functions

function automatic logic is_dret_f();
  return rvfi_match_instr(INSTR_OPCODE_DRET, INSTR_MASK_FULL);
endfunction : is_dret_f

function automatic logic is_mret_f();
  return rvfi_match_instr(INSTR_OPCODE_MRET, INSTR_MASK_FULL);
endfunction : is_mret_f

function automatic logic is_uret_f();
  return rvfi_match_instr(INSTR_OPCODE_URET, INSTR_MASK_FULL);
endfunction : is_uret_f

function automatic logic is_wfi_f();
  return rvfi_match_instr(INSTR_OPCODE_WFI, INSTR_MASK_FULL);
endfunction : is_wfi_f

function automatic logic is_wfe_f();
  return rvfi_match_instr(INSTR_OPCODE_WFE, INSTR_MASK_FULL);
endfunction : is_wfe_f

function automatic logic is_ebreak_f();
  return rvfi_match_instr(INSTR_OPCODE_EBREAK, INSTR_MASK_FULL) || rvfi_match_instr(INSTR_OPCODE_C_EBREAK, INSTR_MASK_FULL);
endfunction : is_ebreak_f

function automatic logic is_ebreak_compr_f();
  return rvfi_match_instr(INSTR_OPCODE_C_EBREAK, INSTR_MASK_FULL);
endfunction : is_ebreak_compr_f

function automatic logic is_ebreak_noncompr_f();
  return rvfi_match_instr(INSTR_OPCODE_EBREAK, INSTR_MASK_FULL);
endfunction : is_ebreak_noncompr_f

function automatic logic is_ecall_f();
  return rvfi_match_instr(INSTR_OPCODE_ECALL, INSTR_MASK_FULL);
endfunction : is_ecall_f

function automatic logic is_branch_f(); //TODO
  return rvfi_match_instr(INSTR_OPCODE_BEQ, INSTR_MASK_I_S_B_TYPE) ||
         rvfi_match_instr(INSTR_OPCODE_BNE, INSTR_MASK_I_S_B_TYPE) ||
         rvfi_match_instr(INSTR_OPCODE_BLT, INSTR_MASK_I_S_B_TYPE) ||
         rvfi_match_instr(INSTR_OPCODE_BGE, INSTR_MASK_I_S_B_TYPE) ||
         rvfi_match_instr(INSTR_OPCODE_BLTU, INSTR_MASK_I_S_B_TYPE) ||
         rvfi_match_instr(INSTR_OPCODE_BGEU, INSTR_MASK_I_S_B_TYPE) ||
         rvfi_match_instr(INSTR_OPCODE_CBEQZ, INSTR_MASK_CMPR) ||
         rvfi_match_instr(INSTR_OPCODE_CBNEZ, INSTR_MASK_CMPR);
endfunction : is_branch_f

function automatic logic is_div_f();
  return rvfi_match_instr(INSTR_OPCODE_DIV, INSTR_MASK_DIV_REM);
endfunction : is_div_f

function automatic logic is_rem_f();
  return rvfi_match_instr(INSTR_OPCODE_REM, INSTR_MASK_DIV_REM);
endfunction : is_rem_f

function automatic logic is_cslli_f();
  return rvfi_match_instr(INSTR_OPCODE_CSLLI, INSTR_MASK_CMPR);
endfunction : is_cslli_f

function automatic logic is_pushpop_f();
  return  rvfi_match_instr(INSTR_OPCODE_PUSH,    INSTR_MASK_ZC_PUSHPOP)  ||
          rvfi_match_instr(INSTR_OPCODE_POP,     INSTR_MASK_ZC_PUSHPOP)  ||
          rvfi_match_instr(INSTR_OPCODE_POPRET,  INSTR_MASK_ZC_PUSHPOP)  ||
          rvfi_match_instr(INSTR_OPCODE_POPRETZ, INSTR_MASK_ZC_PUSHPOP);
endfunction : is_pushpop_f

function automatic logic is_tablejump_raw_f();
  return  match_instr_raw(INSTR_OPCODE_TABLEJUMP, INSTR_MASK_TABLEJUMP);
endfunction : is_tablejump_raw_f

function automatic logic is_fencefencei_f();
  return  rvfi_match_instr(INSTR_OPCODE_FENCE,  INSTR_MASK_FENCE)  ||
          rvfi_match_instr(INSTR_OPCODE_FENCEI, INSTR_MASK_FENCEI);
endfunction : is_fencefencei_f

function automatic logic is_nmi_f();
  return rvfi_valid && rvfi_intr.intr && (rvfi_intr.cause & INTR_CAUSE_NMI_MASK);
endfunction : is_nmi_f

function automatic logic is_compressed_f();
  return  rvfi_valid && (rvfi_insn[1:0] != 2'b11);
endfunction : is_compressed_f

function automatic logic is_dbg_trg_f();
  return  rvfi_valid &&
          rvfi_trap.trap &&
          rvfi_trap.debug &&
         (rvfi_trap.debug_cause == DBG_CAUSE_TRIGGER);
endfunction : is_dbg_trg_f

function automatic logic is_mmode_f();
  return  rvfi_valid &&
          (rvfi_mode == PRIV_LVL_M);
endfunction : is_mmode_f

function automatic logic is_not_mmode_f();
  return  rvfi_valid &&
          (rvfi_mode != PRIV_LVL_M);
endfunction : is_not_mmode_f

function automatic logic is_umode_f();
  return  rvfi_valid &&
          (rvfi_mode == PRIV_LVL_U);
endfunction : is_umode_f

function automatic logic is_not_umode_f();
  return  rvfi_valid &&
          (rvfi_mode != PRIV_LVL_U);
endfunction : is_not_umode_f

function automatic logic is_pma_instr_fault_f();
  return  rvfi_valid  &&
          rvfi_trap.trap  &&
          rvfi_trap.exception  &&
          (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_ACC_FAULT)  &&
          (rvfi_trap.cause_type == 'h 0);
endfunction : is_pma_instr_fault_f

function automatic logic is_pma_fault_f();
  return  rvfi_valid  &&
          rvfi_trap.trap  &&
          rvfi_trap.exception  &&
          (rvfi_trap.exception_cause  inside {
            EXC_CAUSE_INSTR_ACC_FAULT,
            EXC_CAUSE_LOAD_ACC_FAULT,
            EXC_CAUSE_STORE_ACC_FAULT
          })  &&
          (rvfi_trap.cause_type == 'h 0);
endfunction : is_pma_fault_f

function automatic logic is_instr_bus_valid_f();
  return !( (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_ACC_FAULT) ||
            (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_INTEGRITY_FAULT) ||
            (rvfi_trap.exception_cause == EXC_CAUSE_INSTR_BUS_FAULT)
    );
endfunction : is_instr_bus_valid_f

function automatic logic [31:0] rvfi_mem_addr_word0highbyte_f();
  logic [31:0] addr = rvfi_mem_addr[31:0];
  case (1)
    (rvfi_mem_rmask[3] || rvfi_mem_wmask[3]):
      return  addr + 3;
    (rvfi_mem_rmask[2] || rvfi_mem_wmask[2]):
      return  addr + 2;
    (rvfi_mem_rmask[1] || rvfi_mem_wmask[1]):
      return  addr + 1;
    default:
      return  addr;
  endcase
endfunction : rvfi_mem_addr_word0highbyte_f

function automatic logic is_split_datatrans_actual_f();
  logic [31:0]  low_addr  = rvfi_mem_addr[XLEN-1:0];
  logic [31:0]  high_addr = rvfi_mem_addr_word0highbyte;
  return  is_mem_act_actual && (low_addr[31:2] != high_addr[31:2]);
endfunction : is_split_datatrans_actual_f

function automatic logic is_split_datatrans_intended_f();
  logic [31:0]  low_addr  = rvfi_mem_addr[XLEN-1:0];
  logic [31:0]  high_addr = rvfi_mem_addr_word0highbyte;
  // TODO:ERROR:silabs-robin Create "instr_mem_addr" when decoder facilitates it
  return  is_mem_act_intended && (low_addr[31:2] != high_addr[31:2]);
endfunction : is_split_datatrans_intended_f

// Shows "intended" version of rvfi_mem_wmask
function automatic logic [4*NMEM-1:0] rvfi_mem_rmask_intended_f();
  logic [NMEM-1:0][3:0] rmask = {'0};
  logic [3:0] rlist;
  rlist = rvfi_insn[7:4];

  rmask[0][3] =
    rvfi_match_instr(INSTR_OPCODE_LW,        INSTR_MASK_I_S_B_TYPE)  ||
    rvfi_match_instr(INSTR_OPCODE_CLW,       INSTR_MASK_CMPR)        ||
    rvfi_match_instr(INSTR_OPCODE_CLWSP,     INSTR_MASK_CMPR)        ||
    rvfi_match_instr(INSTR_OPCODE_CMPOP,     INSTR_MASK_ZC_PUSHPOP)  ||
    rvfi_match_instr(INSTR_OPCODE_CMPOPRET,  INSTR_MASK_ZC_PUSHPOP)  ||
    rvfi_match_instr(INSTR_OPCODE_CMPOPRETZ, INSTR_MASK_ZC_PUSHPOP)  ||
    rvfi_match_instr(INSTR_OPCODE_LRW,       INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOSWAPW,  INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOADDW,   INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOXORW,   INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOANDW,   INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOORW,    INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOMINW,   INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOMAXW,   INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOMINUW,  INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOMAXUW,  INSTR_MASK_AMO_TYPE);

  rmask[0][2] = rmask[0][3];

  rmask[0][1] = rmask[0][2] ||
    rvfi_match_instr(INSTR_OPCODE_LH,        INSTR_MASK_I_S_B_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_LHU,       INSTR_MASK_I_S_B_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_CLHU,      INSTR_MASK_CLH_CLHU_CSH)  ||
    rvfi_match_instr(INSTR_OPCODE_CLH,       INSTR_MASK_CLH_CLHU_CSH);

  rmask[0][0] = rmask[0][1] ||
    rvfi_match_instr(INSTR_OPCODE_LOAD,      INSTR_MASK_OPCODE)  ||
    rvfi_match_instr(INSTR_OPCODE_CLBU,      INSTR_MASK_ZC_CLBU_CSB);

  if(rlist > 4 &&
    (rvfi_match_instr(INSTR_OPCODE_CMPOP,     INSTR_MASK_ZC_PUSHPOP) ||
    rvfi_match_instr(INSTR_OPCODE_CMPOPRET,  INSTR_MASK_ZC_PUSHPOP)  ||
    rvfi_match_instr(INSTR_OPCODE_CMPOPRETZ, INSTR_MASK_ZC_PUSHPOP))) begin

    case (rlist)
      5:  begin
        rmask[1:0] = '1;
      end

      6:  begin
        rmask[2:0] = '1;
      end

      7:  begin
        rmask[3:0] = '1;
      end

      8:  begin
        rmask[4:0] = '1;
      end

      9:  begin
        rmask[5:0] = '1;
      end

      10: begin
        rmask[6:0] = '1;
      end

      11: begin
        rmask[7:0] = '1;
      end

      12: begin
        rmask[8:0] = '1;
      end

      13: begin
        rmask[9:0] = '1;
      end

      14: begin
        rmask[10:0] = '1;
      end

      15: begin //Does two extra memory accesses
        rmask[12:0] = '1;
      end

      default: rmask = '0;
    endcase
  end
  return mem_mask_t'(rmask);
endfunction


// Shows "intended" version of rvfi_mem_wmask
function automatic logic [4*NMEM-1:0] rvfi_mem_wmask_intended_f();
  logic [NMEM-1:0][3:0] wmask = {'0};
  logic [3:0] rlist;
  rlist = rvfi_insn[7:4];

  wmask[0][3] =
    rvfi_match_instr(INSTR_OPCODE_SW,        INSTR_MASK_I_S_B_TYPE)  ||
    rvfi_match_instr(INSTR_OPCODE_CSW,       INSTR_MASK_CMPR)        ||
    rvfi_match_instr(INSTR_OPCODE_CSWSP,     INSTR_MASK_CMPR)        ||
    rvfi_match_instr(INSTR_OPCODE_PUSH,      INSTR_MASK_ZC_PUSHPOP)  ||
    rvfi_match_instr(INSTR_OPCODE_SCW,       INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOSWAPW,  INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOADDW,   INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOXORW,   INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOANDW,   INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOORW,    INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOMINW,   INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOMAXW,   INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOMINUW,  INSTR_MASK_AMO_TYPE)    ||
    rvfi_match_instr(INSTR_OPCODE_AMOMAXUW,  INSTR_MASK_AMO_TYPE);


  wmask[0][2] = wmask[0][3];

  wmask[0][1] = wmask[0][2] ||
    rvfi_match_instr(INSTR_OPCODE_SH,  INSTR_MASK_I_S_B_TYPE)  ||
    rvfi_match_instr(INSTR_OPCODE_CSH,    INSTR_MASK_CLH_CLHU_CSH);

  wmask[0][0] = wmask[0][1] ||
    rvfi_match_instr(INSTR_OPCODE_STORE,    INSTR_MASK_OPCODE)   ||
    rvfi_match_instr(INSTR_OPCODE_CSB,      INSTR_MASK_ZC_CLBU_CSB);

  if(rlist > 4 && rvfi_match_instr(INSTR_OPCODE_PUSH, INSTR_MASK_ZC_PUSHPOP)) begin

    case (rlist)
      5:  begin
        wmask[1:0] = '1;
      end

      6:  begin
        wmask[2:0] = '1;
      end

      7:  begin
        wmask[3:0] = '1;
      end

      8:  begin
        wmask[4:0] = '1;
      end

      9:  begin
        wmask[5:0] = '1;
      end

      10: begin
        wmask[6:0] = '1;
      end

      11: begin
        wmask[7:0] = '1;
      end

      12: begin
        wmask[8:0] = '1;
      end

      13: begin
        wmask[9:0] = '1;
      end

      14: begin
        wmask[10:0] = '1;
      end

      15: begin //Does two extra memory accesses
        wmask[12:0] = '1;
      end

      default: wmask = '0;
    endcase
  end
  return mem_mask_t'(wmask);
endfunction

function automatic logic[31:0] get_max_exception_cause_f (
  logic[31:0] exc_a,
  logic[31:0] exc_b
);
  if (EXC_CAUSE_INSTR_ACC_FAULT inside {exc_a, exc_b}) begin
      return EXC_CAUSE_INSTR_ACC_FAULT;
  end else if (EXC_CAUSE_INSTR_INTEGRITY_FAULT inside {exc_a, exc_b}) begin
      return EXC_CAUSE_INSTR_INTEGRITY_FAULT;
  end else if (EXC_CAUSE_INSTR_BUS_FAULT inside {exc_a, exc_b}) begin
      return EXC_CAUSE_INSTR_BUS_FAULT;
  end else if (EXC_CAUSE_ILLEGAL_INSTR inside {exc_a, exc_b}) begin
      return EXC_CAUSE_ILLEGAL_INSTR;
  end else if (EXC_CAUSE_ENV_CALL_U inside {exc_a, exc_b}) begin
      return EXC_CAUSE_ENV_CALL_U;
  end else if (EXC_CAUSE_ENV_CALL_M inside {exc_a, exc_b}) begin
      return EXC_CAUSE_ENV_CALL_M;
  end else if (EXC_CAUSE_BREAKPOINT inside {exc_a, exc_b}) begin
      return EXC_CAUSE_BREAKPOINT;
  end else if (EXC_CAUSE_STORE_ACC_FAULT inside {exc_a, exc_b}) begin
      return EXC_CAUSE_STORE_ACC_FAULT;
  end else if (EXC_CAUSE_LOAD_ACC_FAULT inside {exc_a, exc_b}) begin
      return EXC_CAUSE_LOAD_ACC_FAULT;
  end else begin
    `uvm_error(info_tag, "unhandled 'max' exception cause");
    return '0;
  end
endfunction : get_max_exception_cause_f

function automatic logic is_deprioritized_exception_f (logic[31:0] exc_cause);
  return (
    rvfi_valid  &&
    rvfi_trap.exception  &&
    (rvfi_trap.exception_cause != exc_cause)  &&
    (rvfi_trap.exception_cause ==
      get_max_exception_cause_f({26'd0, rvfi_trap.exception_cause}, exc_cause)
    )
  );
endfunction

endinterface : uvma_rvfi_instr_if_t

// Simplified rvfi interface for use with the reference module
interface rvfi_if_t
  import uvma_rvfi_pkg::*;
  (
  );

  // RVFI field widths
  localparam ORDER_WL         = 64;
  localparam MODE_WL          = 2;
  localparam IXL_WL           = 2;
  localparam TRAP_WL          = 14;
  localparam GPR_ADDR_WL      = 5;
  localparam RVFI_DBG_WL      = 3;
  localparam RVFI_NMIP_WL     = 2;
  localparam CYCLE_CNT_WL     = 32;
  localparam NMEM             = 128;

  // Fields within TRAP
  localparam TRAP_EXCP_LSB         = 0;
  localparam TRAP_EXCP_WL          = 1;
  localparam TRAP_NONDBG_ENTRY_LSB = 1;
  localparam TRAP_NONDBG_ENTRY_WL  = 1;
  localparam TRAP_DBG_ENTRY_LSB    = 2;
  localparam TRAP_DBG_ENTRY_WL     = 1;
  localparam TRAP_CAUSE_LSB        = 3;
  localparam TRAP_CAUSE_WL         = 6;
  localparam TRAP_DBG_CAUSE_LSB    = 9;
  localparam TRAP_DBG_CAUSE_WL     = 3;

  // Lengths & Sizes
  localparam DEFAULT_ILEN     = 32;
  localparam DEFAULT_XLEN     = 32;
  localparam DEFAULT_NRET     = 1;
  localparam ILEN     = 32;
  localparam XLEN     = 32;
  localparam NRET     = 1;




     logic                      clk;
     logic                      reset_n;

     logic                      valid;
     logic [ORDER_WL-1:0]       order;
     logic [ILEN-1:0]           insn;
     rvfi_trap_t                trap;
     logic                      halt;
     logic [RVFI_DBG_WL-1:0]    dbg;
     logic                      dbg_mode;
     logic [RVFI_NMIP_WL-1:0]   nmip;
     rvfi_intr_t                intr;
     logic [MODE_WL-1:0]        mode;
     logic [IXL_WL-1:0]         ixl;
     logic [XLEN-1:0]           pc_rdata;
     logic [XLEN-1:0]           pc_wdata;

     logic [GPR_ADDR_WL-1:0]    rs1_addr;
     logic [XLEN-1:0]           rs1_rdata;

     logic [GPR_ADDR_WL-1:0]    rs2_addr;
     logic [XLEN-1:0]           rs2_rdata;

     logic [GPR_ADDR_WL-1:0]    rs3_addr;
     logic [XLEN-1:0]           rs3_rdata;

     logic [GPR_ADDR_WL-1:0]    rd1_addr;
     logic [XLEN-1:0]           rd1_wdata;

     logic [GPR_ADDR_WL-1:0]    rd2_addr;
     logic [XLEN-1:0]           rd2_wdata;
/*
     logic [(32*XLEN)-1:0]      gpr_rdata;
     logic [(32)-1:0]           gpr_rmask;
     logic [(32*XLEN)-1:0]      gpr_wdata;
     logic [(32)-1:0]           gpr_wmask;
     */

     logic [(NMEM*XLEN)-1:0]    mem_addr;
     logic [(NMEM*XLEN)-1:0]    mem_rdata;
     logic [(NMEM*XLEN/8)-1:0]  mem_rmask;
     logic [(NMEM*XLEN)-1:0]    mem_wdata;
     logic [(NMEM*XLEN/8)-1:0]  mem_wmask;
    
    /*
     logic [2:0]                instr_prot;
     logic [1:0]                instr_memtype;
     logic                      instr_dbg;
     logic [ NMEM*3-1:0]        mem_prot;
     logic [ 1*NMEM-1:0]        mem_exokay;
     logic [ 1*NMEM-1:0]        mem_err;
     logic [ 6*NMEM-1:0]        mem_atop;
     logic [ 2*NMEM-1:0]        mem_memtype;
     logic [ NMEM-1  :0]        mem_db;
 
*/


endinterface : rvfi_if_t


`endif // __UVMA_RVFI_INSTR_IF_SV__
