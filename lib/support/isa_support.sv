// Copyright 2023 Silicon Labs, Inc.
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


`ifndef __ISA_SUPPORT__
`define __ISA_SUPPORT__

/**
 * Encapsulates all functions used on instruction words
 */
  //package uvmt_cv32e40s_instr_pkg;

  localparam CLIC_ID_WIDTH = 5;
  // -------------------------------------------------------------------
  // Local param
  // -------------------------------------------------------------------
  //instruction masks

  localparam INSTR_MASK_FULL        = 32'h FFFF_FFFF;
  localparam INSTR_MASK_R_TYPE      = 32'h FE00_707F;
  localparam INSTR_MASK_I_S_B_TYPE  = 32'h 0000_707F;
  localparam INSTR_MASK_U_J_TYPE    = 32'h 0000_007F;
  localparam INSTR_MASK_CSRADDR     = 32'h FFF0_0000;
  localparam INSTR_MASK_CMPR        = 32'h 0000_E003;

  //instruction comparison values
  localparam INSTR_OPCODE_DRET      = 32'h 7B20_0073;
  localparam INSTR_OPCODE_MRET      = 32'h 3020_0073;
  localparam INSTR_OPCODE_URET      = 32'h 0020_0073;
  localparam INSTR_OPCODE_WFI       = 32'h 1050_0073;
  localparam INSTR_OPCODE_WFE       = 32'h 8C00_0073;
  localparam INSTR_OPCODE_EBREAK    = 32'h 0010_0073;
  localparam INSTR_OPCODE_C_EBREAK  = 32'h 0000_9002;
  localparam INSTR_OPCODE_ECALL     = 32'h 0000_0073;
  localparam INSTR_OPCODE_CSLLI     = 32'h 0000_0002;

  localparam INSTR_OPCODE_CSRRW     = 32'h 0000_1073;
  localparam INSTR_OPCODE_CSRRS     = 32'h 0000_2073;
  localparam INSTR_OPCODE_CSRRC     = 32'h 0000_3073;
  localparam INSTR_OPCODE_CSRRWI    = 32'h 0000_5073;
  localparam INSTR_OPCODE_CSRRSI    = 32'h 0000_6073;
  localparam INSTR_OPCODE_CSRRCI    = 32'h 0000_7073;

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

  //positions
  localparam int INSTR_CSRADDR_POS  = 20;
  localparam DEFAULT_XLEN = 32;

  // -------------------------------------------------------------------
  // CSR Addresses
  // -------------------------------------------------------------------

  // TODO: expand
  typedef enum logic [31:20] {
    MSTATUS       = 12'h300,
    MISA          = 12'h301,
    MIE           = 12'h304,
    MTVEC         = 12'h305,
    MTVT          = 12'h307,
    MSTATUSH      = 12'h310,
    MCOUNTINHIBIT = 12'h320,
    MHPMEVENT3    = 12'h323,
    MHPMEVENT31   = 12'h33F,
    MSCRATCH      = 12'h340,
    MEPC          = 12'h341,
    MCAUSE        = 12'h342,
    MTVAL         = 12'h343,
    MIP           = 12'h344,
    MNXTI         = 12'h345,
    MINTSTATUS    = 12'h346,
    MINTTHRESH    = 12'h347,
    MSCRATCHCSW   = 12'h348,
    MSCRATCHCSWL  = 12'h349,
    MCLICBASE     = 12'h34A,
    TSELECT       = 12'h7A0,
    TDATA1        = 12'h7A1,
    TDATA2        = 12'h7A2,
    TDATA3        = 12'h7A3,
    TINFO         = 12'h7A4,
    TCONTROL      = 12'h7A5,
    DCSR          = 12'h7B0,
    DPC           = 12'h7B1,
    DSCRATCH0     = 12'h7B2,
    DSCRATCH1     = 12'h7B3
  } csr_name_e;

  // Instruction names, TODO: add instructions as needed
  typedef enum {
    FENCEI,
    MRET,
    DRET,
    ECALL,
    EBREAK,
    WFI,
    WFE,
    CSRRW,
    CSRRS,
    CSRRC,
    CSRRWI,
    CSRRSI,
    CSRRCI,
    // RV32I
    LUI,
    AUIPC,
    JAL,
    JALR,
    BEQ,
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU,
    SB,
    SH,
    SW,
    LB,
    LH,
    LW,
    LBU,
    LHU,
    ADDI,
    SLTI,
    SLTIU,
    XORI,
    ORI,
    ANDI,
    SLLI,
    SRLI,
    SRAI,
    ADD,
    SUB,
    SLL,
    SLT,
    SLTU,
    XOR,
    SRL,
    SRA,
    OR,
    AND,
    // Compressed
    CEBREAK,
    // Pseudo name, class of instructions
    STORE_INSN,
    LOAD_INSN,
    // Unknown for instructions that cannot be decoded
    UNKNOWN
  } instr_names_e;

  // GPR Registers

  typedef enum logic [4:0] {
    X0  = 5'd0,
    X1  = 5'd1,
    X2  = 5'd2,
    X3  = 5'd3,
    X4  = 5'd4,
    X5  = 5'd5,
    X6  = 5'd6,
    X7  = 5'd7,
    X8  = 5'd8,
    X9  = 5'd9,
    X10 = 5'd10,
    X11 = 5'd11,
    X12 = 5'd12,
    X13 = 5'd13,
    X14 = 5'd14,
    X15 = 5'd15,
    X16 = 5'd16,
    X17 = 5'd17,
    X18 = 5'd18,
    X19 = 5'd19,
    X20 = 5'd20,
    X21 = 5'd21,
    X22 = 5'd22,
    X23 = 5'd23,
    X24 = 5'd24,
    X25 = 5'd25,
    X26 = 5'd26,
    X27 = 5'd27,
    X28 = 5'd28,
    X29 = 5'd29,
    X30 = 5'd30,
    X31 = 5'd31
  } gpr_name_e;

  typedef enum logic [4:0] {
    ZERO = 5'd0,
    RA   = 5'd1,
    SP   = 5'd2,
    GP   = 5'd3,
    TP   = 5'd4,
    T0   = 5'd5,
    T1   = 5'd6,
    T2   = 5'd7,
    S0   = 5'd8,
    S1   = 5'd9,
    A0   = 5'd10,
    A1   = 5'd11,
    A2   = 5'd12,
    A3   = 5'd13,
    A4   = 5'd14,
    A5   = 5'd15,
    A6   = 5'd16,
    A7   = 5'd17,
    S2   = 5'd18,
    S3   = 5'd19,
    S4   = 5'd20,
    S5   = 5'd21,
    S6   = 5'd22,
    S7   = 5'd23,
    S8   = 5'd24,
    S9   = 5'd25,
    S10  = 5'd26,
    S11  = 5'd27,
    T3   = 5'd28,
    T4   = 5'd29,
    T5   = 5'd30,
    T6   = 5'd31
  } gpr_abi_name_e;

  typedef enum logic [2:0] {
    C_X8  = 3'b000,
    C_X9  = 3'b001,
    C_X10 = 3'b010,
    C_X11 = 3'b011,
    C_X12 = 3'b100,
    C_X13 = 3'b101,
    C_X14 = 3'b110,
    C_X15 = 3'b111
  } c_gpr_name_e;

  typedef enum logic [2:0] {
    C_S0 = 3'b000,
    C_S1 = 3'b001,
    C_A0 = 3'b010,
    C_A1 = 3'b011,
    C_A2 = 3'b100,
    C_A3 = 3'b101,
    C_A4 = 3'b110,
    C_A5 = 3'b111
  } c_gpr_abi_name_e;

  typedef union packed {
    logic [2:0]      raw;
    c_gpr_name_e     gpr;
    c_gpr_abi_name_e gpr_abi;
  } c_gpr_t;

  typedef union packed {
    logic [4:0]    raw;
    gpr_name_e     gpr;
    gpr_abi_name_e gpr_abi;
  } gpr_t;

  // -------------------------------------------------------------------
  // Function types
  // -------------------------------------------------------------------

  // Major opcodes
  typedef enum logic [6:0] {
    LOAD   = 7'b000_0011, LOAD_FP  = 7'b000_0111, CUS_0 = 7'b000_1011, MISC_MEM = 7'b000_1111, OP_IMM = 7'b001_0011, AUIPC_OP = 7'b001_0111,OP_IMM_32 = 7'b001_1011,
    STORE  = 7'b010_0011, STORE_FP = 7'b010_0111, CUS_1 = 7'b010_1011, AMO      = 7'b010_1111, OP     = 7'b011_0011, LUI_OP   = 7'b011_0111,OP_32     = 7'b011_1011,
    MADD   = 7'b100_0011, MSUB     = 7'b100_0111, NMSUB = 7'b100_1011, NMADD    = 7'b100_1111, OP_FP  = 7'b101_0011, RES_1    = 7'b101_0111,CUS_2     = 7'b101_1011,
    BRANCH = 7'b110_0011, JALR_OP  = 7'b110_0111, RES_0 = 7'b110_1011, JAL_OP   = 7'b110_1111, SYSTEM = 7'b111_0011, RES_2    = 7'b111_0111,CUS_3     = 7'b111_1011
  } major_opcode_e;

  typedef enum logic [1:0] {
    C0 = 2'b00, C1 = 2'b01, C2 = 2'b10, C3 = 2'b11
  } compressed_opcode_e;

  // Minor opcodes
  typedef enum logic [2:0] {
    FUNCT3_CSRRW  = 3'b001,
    FUNCT3_CSRRS  = 3'b010,
    FUNCT3_CSRRC  = 3'b011,
    FUNCT3_CSRRWI = 3'b101,
    FUNCT3_CSRRSI = 3'b110,
    FUNCT3_CSRRCI = 3'b111
  } csr_minor_opcode_e;

  typedef enum logic [2:0] {
    FUNCT3_LB  = 3'b000,
    FUNCT3_LH  = 3'b001,
    FUNCT3_LW  = 3'b010,
    FUNCT3_LBU = 3'b100,
    FUNCT3_LHU = 3'b101
  } load_minor_opcode_e;

  typedef enum logic [2:0] {
    FUNCT3_SB = 3'b000,
    FUNCT3_SH = 3'b001,
    FUNCT3_SW = 3'b010
  } store_minor_opcode_e;

  typedef enum logic [2:0] {
    FUNCT3_BEQ  = 3'b000,
    FUNCT3_BNE  = 3'b001,
    FUNCT3_BLT  = 3'b100,
    FUNCT3_BGE  = 3'b101,
    FUNCT3_BLTU = 3'b110,
    FUNCT3_BGEU = 3'b111
  } branch_minor_opcode_e;

  typedef enum logic [2:0] {
    FUNCT3_ADDI      = 3'b000,
    FUNCT3_SLTI      = 3'b010,
    FUNCT3_SLTIU     = 3'b011,
    FUNCT3_XORI      = 3'b100,
    FUNCT3_ORI       = 3'b110,
    FUNCT3_ANDI      = 3'b111,
    FUNCT3_SLLI      = 3'b001,
    FUNCT3_SRLI_SRAI = 3'b101
  } op_imm_minor_opcode_e;

  typedef enum logic [2:0] {
    FUNCT3_ADD_SUB = 3'b000,
    FUNCT3_SLL     = 3'b001,
    FUNCT3_SLT     = 3'b010,
    FUNCT3_SLTU    = 3'b011,
    FUNCT3_XOR     = 3'b100,
    FUNCT3_SRL_SRA = 3'b101,
    FUNCT3_OR      = 3'b110,
    FUNCT3_AND     = 3'b111
  } op_minor_opcode_e;


  // Specific function subtypes
  typedef struct packed {
    csr_name_e           csr;
    union packed {
      gpr_t         rs1;
      logic [19:15] uimm;
    }n;
    csr_minor_opcode_e funct3;
    gpr_t          rd;
    major_opcode_e opcode;
  } csr_instr_t;

  // U type
  typedef struct packed {
    logic [31:12]  imm;
    gpr_t rd;
  } u_type_t;

  // J type
  typedef struct packed {
    logic [31:12] imm;
    gpr_t         rd;
  } j_type_t;

  function logic[20:0] read_j_imm(logic[31:0] instr);
    automatic logic [20:0] imm;
    imm = instr >> 11;
    return { imm[20], imm[10:1], imm[11], imm[18:12], 1'b0 };
  endfunction : read_j_imm


  typedef struct packed {
    logic [31:25] funct7;
    gpr_t         rs2;
  } r_funct12_t;

  // R type
  typedef struct packed {
    logic [31:25]  funct7;
    gpr_t          rs2;
    gpr_t          rs1;
    logic [14:12]  funct3;
    gpr_t          rd;
  } r_type_t;

  // R4 type
  typedef struct packed {
    gpr_t          rs3;
    logic [26:25]  funct2;
    gpr_t          rs2;
    gpr_t          rs1;
    logic [14:12]  funct3;
    gpr_t          rd;
  } r4_type_t;

  typedef struct packed {
    logic [31:25] funct7;
    logic [24:20] shamt;
  } i_imm_t;

  // I type
  typedef struct packed {
    i_imm_t        imm;
    gpr_t          rs1;
    logic [14:12]  funct3;
    gpr_t          rd;
  } i_type_t;

  // I type (Load)
  typedef struct packed {
    i_imm_t             imm;
    gpr_t               rs1;
    load_minor_opcode_e funct3;
    gpr_t               rd;
  } i_type_load_t;

  // B type
  typedef struct packed {
    logic [31:25]  imm;
    gpr_t          rs2;
    gpr_t          rs1;
    logic [14:12]  funct3;
    gpr_t          rd;
  } b_type_t;

  function logic[11:0] read_b_imm(logic[31:0] instr);
    automatic logic [11:0] imm;
    imm = {instr[31], instr[7], instr[30:25], instr[11:8]};
    return imm;
  endfunction : read_b_imm

  // S type
  typedef struct packed {
    logic [31:25]        imm_h;
    gpr_t                rs2;
    gpr_t                rs1;
    store_minor_opcode_e funct3;
    logic [11:7]         imm_l;
  } s_type_t;

  function logic[11:0] read_s_imm(logic[31:0] instr);
    automatic logic [11:0] imm;
    imm = {instr[31:25], instr[11:7]};
    return imm;
  endfunction : read_s_imm

  // Generic
  typedef struct packed {
    union packed {
      logic [31:7]         raw;
      i_type_t             i;
      i_type_load_t        i_load;
      j_type_t             j;
      s_type_t             s;
      r_type_t             r;
      r4_type_t            r4;
      b_type_t             b;
      u_type_t             u;
    } format; // Would like to use type, but type is reserved keyword in sv
    major_opcode_e opcode;
  } uncompressed_instr_t;

  typedef struct packed {
    logic[15:12] funct4;
    gpr_t        rd_rs1;
    gpr_t        rs2;
  } cr_type_t;

  typedef struct packed {
    logic[15:13] funct3;
    logic[12:12] imm_12;
    gpr_t        rd_rs1;
    logic[6:2]   imm_6_2;
  } ci_type_t;

  typedef struct packed {
    logic[15:13] funct3;
    logic[12:7]  imm;
    gpr_t      rs2;
  } css_type_t;

  typedef struct packed {
    logic[15:13] funct3;
    logic[12:5]  imm;
    c_gpr_t      rd;
  } ciw_type_t;

  typedef struct packed {
    logic[15:13] funct3;
    logic[12:10] imm_12_10;
    c_gpr_t      rs1;
    logic[6:5]   imm_6_5;
    c_gpr_t      rd;
  } cl_type_t;

  typedef struct packed {
    logic[15:13] funct3;
    logic[12:10] imm_12_10;
    c_gpr_t      rs1;
    logic[6:5]   imm_6_5;
    c_gpr_t      rs2;
  } cs_type_t;

  typedef struct packed {
    logic[15:10] funct6;
    c_gpr_t      rd_rs1;
    logic[6:5]   funct2;
    c_gpr_t      rs2;
  } ca_type_t;

  typedef struct packed {
    logic[15:13] funct3;
    logic[12:10] offset_12_10;
    c_gpr_t      rd_rs1;
    logic[6:2]   offset_6_2;
  } cb_type_t;

  typedef struct packed {
    logic[15:13] funct3;
    logic[12:2]  imm;
  } cj_type_t;

  // Compressed instruction types
  typedef struct packed {
    logic [31:16]  reserved_31_16;
    union packed {
      logic [15:2] raw;
      cr_type_t    cr;
      ci_type_t    ci;
      css_type_t   css;
      ciw_type_t   ciw;
      cl_type_t    cl;
      cs_type_t    cs;
      ca_type_t    ca;
      cb_type_t    cb;
      cj_type_t    cj;
    } format;
    compressed_opcode_e opcode;
  } compressed_instr_t;

  typedef union packed {
    compressed_instr_t   compressed;
    uncompressed_instr_t uncompressed;
  } instr_t;

  function logic [11:0] get_cj_offset(compressed_instr_t instr);
    get_cj_offset = {
      instr.format.cj.imm[11+1],
      instr.format.cj.imm[4+1],
      instr.format.cj.imm[9+1:8+1],
      instr.format.cj.imm[10+1],
      instr.format.cj.imm[6+1],
      instr.format.cj.imm[7+1],
      instr.format.cj.imm[3+1:1+1],
      instr.format.cj.imm[5+1],
      1'b0
    };
  endfunction : get_cj_offset

  function instr_names_e decode_instr(instr_t instr);
    case (1)
      (   (instr.uncompressed.opcode              == MISC_MEM)
       && (instr.uncompressed.format.i.rd         == 5'b0_0000)
       && (instr.uncompressed.format.i.funct3     == 3'b001)
       && (instr.uncompressed.format.i.rs1        == 5'b0_0000)
       && (instr.uncompressed.format.i.imm        == 12'h000)) :
        decode_instr = FENCEI;

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.imm        == 12'b0000_0000_0000)) :
        decode_instr = ECALL;

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.imm        == 12'b0000_0000_0001)) :
        decode_instr = EBREAK;

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.rd         == 5'b0_0000)
       && (instr.uncompressed.format.i.funct3     == 3'b000)
       && (instr.uncompressed.format.i.rs1        == 5'b0_0000)
       && (instr.uncompressed.format.i.imm        == 12'b0011_0000_0010)) :
        decode_instr = MRET;

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.imm        == 12'b0111_1011_0010)) :
        decode_instr = DRET;

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.rd         == 5'b0_0000)
       && (instr.uncompressed.format.i.funct3     == 3'b000)
       && (instr.uncompressed.format.i.rs1        == 5'b0_0000)
       && (instr.uncompressed.format.i.imm        == 12'b0001_0000_0101)) :
        decode_instr = WFI;

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.rd         == 5'b0_0000)
       && (instr.uncompressed.format.i.funct3     == 3'b000)
       && (instr.uncompressed.format.i.rs1        == 5'b0_0000)
       && (instr.uncompressed.format.i.imm        == 12'b1000_1100_0000)) :
        decode_instr = WFE;

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_CSRRW)) :
        decode_instr = CSRRW;

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_CSRRS)) :
        decode_instr = CSRRS;

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_CSRRC)) :
        decode_instr = CSRRC;

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_CSRRWI)) :
        decode_instr = CSRRWI;

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_CSRRSI)) :
        decode_instr = CSRRSI;

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_CSRRCI)) :
        decode_instr = CSRRCI;

      (   (instr.uncompressed.opcode              == STORE)
       && (instr.uncompressed.format.s.funct3     == FUNCT3_SB)) :
        decode_instr = SB;

      (   (instr.uncompressed.opcode              == STORE)
       && (instr.uncompressed.format.s.funct3     == FUNCT3_SH)) :
        decode_instr = SH;

      (   (instr.uncompressed.opcode              == STORE)
       && (instr.uncompressed.format.s.funct3     == FUNCT3_SW)) :
        decode_instr = SW;

      (   (instr.uncompressed.opcode              == LOAD)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_LB)) :
        decode_instr = LB;

      (   (instr.uncompressed.opcode              == LOAD)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_LH)) :
        decode_instr = LH;

      (   (instr.uncompressed.opcode              == LOAD)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_LW)) :
        decode_instr = LW;

      (   (instr.uncompressed.opcode              == LOAD)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_LBU)) :
        decode_instr = LBU;

      (   (instr.uncompressed.opcode              == LOAD)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_LHU)) :
        decode_instr = LHU;

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_ADDI)) :
        decode_instr = ADDI;

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SLTI)) :
        decode_instr = SLTI;

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SLTIU)) :
        decode_instr = SLTIU;

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_XORI)) :
        decode_instr = XORI;

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_ORI)) :
        decode_instr = ORI;

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_ANDI)) :
        decode_instr = ANDI;

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SLLI)
       && (instr.uncompressed.format.i.imm.funct7 == 7'b0000000)) :
        decode_instr = SLLI;

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SRLI_SRAI)
       && (instr.uncompressed.format.i.imm.funct7 == 7'b0000000)) :
        decode_instr = SRLI;

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SRLI_SRAI)
       && (instr.uncompressed.format.i.imm.funct7 == 7'b0100000)) :
        decode_instr = SRAI;

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_ADD_SUB)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        decode_instr = ADD;

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_ADD_SUB)
       && (instr.uncompressed.format.r.funct7     == 7'b0100000)) :
        decode_instr = SUB;

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SLL)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        decode_instr = SLL;

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SLT)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        decode_instr = SLT;

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SLTU)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        decode_instr = SLTU;

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_XOR)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        decode_instr = XOR;

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SRL_SRA)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        decode_instr = SRL;

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SRL_SRA)
       && (instr.uncompressed.format.r.funct7     == 7'b0100000)) :
        decode_instr = SRA;

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_OR)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        decode_instr = OR;

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_AND)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        decode_instr = AND;

      (   (instr.uncompressed.opcode              == LUI_OP) ) :
        decode_instr = LUI;

      (   (instr.uncompressed.opcode              == AUIPC_OP) ) :
        decode_instr = AUIPC;

      (   (instr.uncompressed.opcode              == JALR_OP) ) :
        decode_instr = JALR;

      (   (instr.uncompressed.opcode              == JAL_OP) ) :
        decode_instr = JAL;

      (   (instr.uncompressed.opcode              == BRANCH)
       && (instr.uncompressed.format.b.funct3     == FUNCT3_BEQ)) :
        decode_instr = BEQ;

      (   (instr.uncompressed.opcode              == BRANCH)
       && (instr.uncompressed.format.b.funct3     == FUNCT3_BNE)) :
        decode_instr = BNE;

      (   (instr.uncompressed.opcode              == BRANCH)
       && (instr.uncompressed.format.b.funct3     == FUNCT3_BLT)) :
        decode_instr = BLT;

      (   (instr.uncompressed.opcode              == BRANCH)
       && (instr.uncompressed.format.b.funct3     == FUNCT3_BGE)) :
        decode_instr = BGE;

      (   (instr.uncompressed.opcode              == BRANCH)
       && (instr.uncompressed.format.b.funct3     == FUNCT3_BLTU)) :
        decode_instr = BLTU;

      (   (instr.uncompressed.opcode              == BRANCH)
       && (instr.uncompressed.format.b.funct3     == FUNCT3_BGEU)) :
        decode_instr = BGEU;

      // Compressed
      (   (instr.compressed.opcode                == 2'b10)
       && (instr.compressed.format.cr.rd_rs1.gpr  == X0)
       && (instr.compressed.format.cr.rs2.gpr     == X0)
       && (instr.compressed.format.cr.funct4      == 4'b1001)) :
        decode_instr = CEBREAK;

      default: decode_instr = UNKNOWN;
    endcase

  endfunction : decode_instr

  function is_instr(instr_t instr, instr_names_e instr_type);
    case (instr_type)
      FENCEI : return (   (instr.uncompressed.opcode              == MISC_MEM)
                       && (instr.uncompressed.format.i.rd         == 5'b0_0000)
                       && (instr.uncompressed.format.i.funct3     == 3'b001)
                       && (instr.uncompressed.format.i.rs1        == 5'b0_0000)
                       && (instr.uncompressed.format.i.imm        == 12'h000));
      ECALL  : return (   (instr.uncompressed.opcode              == SYSTEM)
                       && (instr.uncompressed.format.i.imm        == 12'b0000_0000_0000));
      EBREAK : return (   (instr.uncompressed.opcode              == SYSTEM)
                       && (instr.uncompressed.format.i.imm        == 12'b0000_0000_0001));
      MRET   : return (   (instr.uncompressed.opcode              == SYSTEM)
                       && (instr.uncompressed.format.i.rd         == 5'b0_0000)
                       && (instr.uncompressed.format.i.imm        == 12'b0011_0000_0010)
                       && (instr.uncompressed.format.i.rs1        == 5'b0_0000)
                       && (instr.uncompressed.format.i.funct3     == 3'b000));
      DRET   : return (   (instr.uncompressed.opcode              == SYSTEM)
                       && (instr.uncompressed.format.i.imm        == 12'b0111_1011_0010));
      WFI    : return (   (instr.uncompressed.opcode              == SYSTEM)
                       && (instr.uncompressed.format.i.rd         == 5'b0_0000)
                       && (instr.uncompressed.format.i.funct3     == 3'b000)
                       && (instr.uncompressed.format.i.rs1        == 5'b0_0000)
                       && (instr.uncompressed.format.i.imm        == 12'b0001_0000_0101));
      WFE    : return (   (instr.uncompressed.opcode              == SYSTEM)
                       && (instr.uncompressed.format.i.rd         == 5'b0_0000)
                       && (instr.uncompressed.format.i.funct3     == 3'b000)
                       && (instr.uncompressed.format.i.rs1        == 5'b0_0000)
                       && (instr.uncompressed.format.i.imm        == 12'b1000_1100_0000));
      SB     : return (   (instr.uncompressed.opcode              == STORE)
                       && (instr.uncompressed.format.s.funct3     == FUNCT3_SB));
      SH     : return (   (instr.uncompressed.opcode              == STORE)
                       && (instr.uncompressed.format.s.funct3     == FUNCT3_SH));
      SW     : return (   (instr.uncompressed.opcode              == STORE)
                       && (instr.uncompressed.format.s.funct3     == FUNCT3_SW));
      LB     : return (   (instr.uncompressed.opcode              == LOAD)
                       && (instr.uncompressed.format.i.funct3     == FUNCT3_LB));
      LH     : return (   (instr.uncompressed.opcode              == LOAD)
                       && (instr.uncompressed.format.i.funct3     == FUNCT3_LH));
      LW     : return (   (instr.uncompressed.opcode              == LOAD)
                       && (instr.uncompressed.format.i.funct3     == FUNCT3_LW));
      LBU    : return (   (instr.uncompressed.opcode              == LOAD)
                       && (instr.uncompressed.format.i.funct3     == FUNCT3_LBU));
      LHU    : return (   (instr.uncompressed.opcode              == LOAD)
                       && (instr.uncompressed.format.i.funct3     == FUNCT3_LHU));
      // Not actual instructions but rather classification
      STORE_INSN : return (instr.uncompressed.opcode              == STORE)
                       && (instr.uncompressed.format.s.funct3 inside { FUNCT3_SB, FUNCT3_SH, FUNCT3_SW });
      LOAD_INSN  : return (instr.uncompressed.opcode              == LOAD)
                       && (instr.uncompressed.format.i.funct3 inside { FUNCT3_LB, FUNCT3_LH, FUNCT3_LW, FUNCT3_LBU, FUNCT3_LHU });
      // Compressed
      CEBREAK: return (   (instr.compressed.opcode                == 2'b10)
                       && (instr.compressed.format.cr.rd_rs1.gpr  == X0)
                       && (instr.compressed.format.cr.rs2.gpr     == X0)
                       && (instr.compressed.format.cr.funct4      == 4'b1001));
    endcase
  endfunction : is_instr

  // -------------------------------------------------------------------
  // CSR Types - TODO replace with include when autogen in place
  // -------------------------------------------------------------------
  typedef struct packed {
    logic [31:24] mil;
    logic [23:16] reserved;
    logic [15:8]  sil;
    logic [7:0]   uil;
  } mintstatus_t;

  typedef struct packed {
    logic [31:8] reserved_0;
    logic [7:0]  th;
  } mintthresh_t;

  typedef struct packed {
    logic [31:31] sd;
    logic [30:23] reserved_3;
    logic [22:22] tsr;
    logic [21:21] tw;
    logic [20:20] tvm;
    logic [19:19] mxr;
    logic [18:18] sum;
    logic [17:17] mprv;
    logic [16:15] xs;
    logic [14:13] fs;
    logic [12:11] mpp;
    logic [10:9]  vs;
    logic [8:8]   spp;
    logic [7:7]   mpie;
    logic [6:6]   ube;
    logic [5:5]   spie;
    logic [4:4]   reserved_2;
    logic [3:3]   mie;
    logic [2:2]   reserved_1;
    logic [1:1]   sie;
    logic [0:0]   reserved_0;
  } mstatus_t;

  // TODO non-clic union
  typedef struct packed {
    logic [31:7] base_31_7;
    logic [6:2]  base_6_2;
    logic [1:0]  mode;
  } mtvec_clic_t;

  // TODO CLIC_ID_WIDTH readable?
  localparam N_MTVT = 2+CLIC_ID_WIDTH > 6 ? 2+CLIC_ID_WIDTH : 6;

  typedef struct packed {
    logic [31:N_MTVT]  base_31_n;
    logic [N_MTVT-1:6] base_n_6;
    logic [5:0]        reserved;
  } mtvt_t;

  typedef struct packed {
    logic [31:1] m_exception_pc;
    logic [0:0]  reserved;
  } mepc_t;

  // TODO exccode_t core specific?
  typedef struct packed {
    logic [31:31] interrupt;
    logic [30:30] minhv;
    logic [29:28] mpp;
    logic [27:27] mpie;
    logic [26:24] reserved_1;
    logic [23:16] mpil;
    logic [15:12] reserved_0;
    logic [11:0]  exccode; // TODO typedef - core specific how to handle properly?
  } mcause_t;

  typedef struct packed {
    logic [31:28] debugver;
    logic [27:18] reserved_27_18;
    logic [17:17] ebreakvs;
    logic [16:16] ebreakvu;
    logic [15:15] ebreakm;
    logic [14:14] reserved_14;
    logic [13:13] ebreaks;
    logic [12:12] ebreaku;
    logic [11:11] stepie;
    logic [10:10] stopcount;
    logic [9:9]   stoptime;
    logic [8:6]   cause;
    logic [5:5]   v;
    logic [4:4]   mprven;
    logic [3:3]   nmip;
    logic [2:2]   step;
    logic [1:0]   prv;
  } dcsr_t;

  // -------------------------------------------------------------------
  // Functions
  // -------------------------------------------------------------------

  function automatic logic [4:0] rs1_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return instr[19:15];
  endfunction : rs1_f

  function automatic logic [4:0] rs2_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return instr[24:20];
  endfunction : rs2_f

  function automatic logic [4:0] rd_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return instr[11:7];
  endfunction : rd_f

  function automatic logic [6:0] opcode_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return instr[6:0];
  endfunction : opcode_f

  function automatic logic [2:0] funct3_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return instr[14:12];
  endfunction : funct3_f

  function automatic logic [6:0] funct7_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return instr[31:25];
  endfunction : funct7_f

  function automatic logic [12:0] branch_imm_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return ({instr[31], instr[7], instr[30:25], instr[11:8], 1'b0});
  endfunction : branch_imm_f


  // Check if instruction is of a certain type, without verifying the instr word is valid
  // Usage: instr_mask sets the parts of the instruction you want to compare,
  //        instr_ref is the reference to match
  function automatic logic match_instr_raw_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [ DEFAULT_XLEN-1:0] instr_ref,
    logic [ DEFAULT_XLEN-1:0] instr_mask
  );

  return ((instr & instr_mask) == instr_ref);

  endfunction : match_instr_raw_f

// Match instr types
  function automatic logic match_instr_r_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [ DEFAULT_XLEN-1:0] instr_ref
  );
    return match_instr_raw_f(instr, instr_ref, INSTR_MASK_R_TYPE);
  endfunction : match_instr_r_f

  function automatic logic match_instr_r_var_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [6:0] funct7,
    logic [2:0] funct3,
    logic [6:0] opcode
  );
  return match_instr_r_f(instr, {funct7, 10'b0, funct3, 5'b0, opcode});
  endfunction : match_instr_r_var_f

  function automatic logic match_instr_isb_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [ DEFAULT_XLEN-1:0] instr_ref
  );

    return match_instr_raw_f(instr, instr_ref, INSTR_MASK_I_S_B_TYPE);
  endfunction : match_instr_isb_f

  function automatic logic match_instr_isb_var_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [2:0] funct3,
    logic [6:0] opcode
  );
    return match_instr_isb_f(instr, {17'b0, funct3, 5'b0, opcode});
  endfunction : match_instr_isb_var_f

  function automatic logic match_instr_uj_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [ DEFAULT_XLEN-1:0] instr_ref
  );
    return  match_instr_raw_f(instr, instr_ref, INSTR_MASK_U_J_TYPE);
  endfunction : match_instr_uj_f

  function automatic logic match_instr_uj_var_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [6:0] opcode
  );
    return  match_instr_uj_f(instr, {25'b0, opcode});
  endfunction : match_instr_uj_var_f

  function automatic logic [6:0] cslli_shamt_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return  {instr[12], instr[6:2]};
  endfunction : cslli_shamt_f


  // Match CSR functions
  // These instruction are used to check for csr activity.
  // All instructions has the input csr_addr. Setting this limits the query to
  // that single address, leaving the input as 0 returns any csr activity.
  function automatic logic is_csr_instr_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [11:0] csr_addr = 0
  );
    if (csr_addr == 0) begin //not specified
      return  match_instr_isb_f(instr, INSTR_OPCODE_CSRRW)  ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRS)  ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRC)  ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRWI) ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRSI) ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRCI);
    end else begin
      return  match_instr_raw_f(instr, 32'h0 | (csr_addr << INSTR_CSRADDR_POS), INSTR_MASK_CSRADDR) &&
              ( match_instr_isb_f(instr, INSTR_OPCODE_CSRRW)  ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRS)  ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRC)  ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRWI) ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRSI) ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRCI));
    end
  endfunction : is_csr_instr_f

  // NOTE!  This instruction differs from the strict definition of "reading a CSR"
  //        in the RISCV-spec, as it returns true only if the read value is actually
  //        stored somewhere.
  function automatic logic is_csr_read_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [ 4:0] rd_addr,
    logic [11:0] csr_addr = 0
  );
    if (rd_addr != 0) begin
      return is_csr_instr_f(instr, csr_addr);
    end else begin // rd is X0, not a read instruction
      return 0;
    end
  endfunction

  // NOTE!  This instruction differs from the strict definition of "writing a CSR"
  //        in the RISCV-spec, as it returns true only if the csr is actually
  //        written.
  function automatic logic is_csr_write_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [ 4:0] rs1_addr,
    logic [11:0] csr_addr = 0
  );
    if (csr_addr == 0) begin //not specified
      return  ( (rs1_addr != 0) && match_instr_isb_f(instr, INSTR_OPCODE_CSRRW))  ||
              ( (rs1_addr != 0) && match_instr_isb_f(instr, INSTR_OPCODE_CSRRS))  ||
              ( (rs1_addr != 0) && match_instr_isb_f(instr, INSTR_OPCODE_CSRRC))  ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRWI) ||
              //TODO:MT add set and clear with immediate nonzero
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRSI) ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRCI);
    end else begin
      return  match_instr_raw_f(instr, 32'h0 | (csr_addr << INSTR_CSRADDR_POS), INSTR_MASK_CSRADDR) &&
              ( ( (rs1_addr != 0) && match_instr_isb_f(instr, INSTR_OPCODE_CSRRW))  ||
                ( (rs1_addr != 0) && match_instr_isb_f(instr, INSTR_OPCODE_CSRRS))  ||
                ( (rs1_addr != 0) && match_instr_isb_f(instr, INSTR_OPCODE_CSRRC))  ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRWI) ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRSI) ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRCI));
    end
  endfunction


  // Short functions for recognising special functions

  function automatic logic is_dret_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_DRET, INSTR_MASK_FULL);
  endfunction : is_dret_f

  function automatic logic is_mret_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_MRET, INSTR_MASK_FULL);
  endfunction : is_mret_f

  function automatic logic is_uret_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_URET, INSTR_MASK_FULL);
  endfunction : is_uret_f

  function automatic logic is_wfi_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_WFI, INSTR_MASK_FULL);
  endfunction : is_wfi_f

  function automatic logic is_wfe_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_WFE, INSTR_MASK_FULL);
  endfunction : is_wfe_f

  function automatic logic is_ebreak_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_EBREAK, INSTR_MASK_FULL) || match_instr_raw_f(instr, INSTR_OPCODE_C_EBREAK, INSTR_MASK_FULL);
  endfunction : is_ebreak_f

  function automatic logic is_ebreak_compr_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_C_EBREAK, INSTR_MASK_FULL);
  endfunction : is_ebreak_compr_f

  function automatic logic is_ebreak_noncompr_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_EBREAK, INSTR_MASK_FULL);
  endfunction : is_ebreak_noncompr_f

  function automatic logic is_ecall_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_ECALL, INSTR_MASK_FULL);
  endfunction : is_ecall_f

  function logic is_cslli_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_CSLLI, INSTR_MASK_CMPR);
  endfunction : is_cslli_f

  function automatic logic is_pushpop_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return  match_instr_raw_f(instr, INSTR_OPCODE_PUSH,    INSTR_MASK_PUSHPOP)  ||
            match_instr_raw_f(instr, INSTR_OPCODE_POP,     INSTR_MASK_PUSHPOP)  ||
            match_instr_raw_f(instr, INSTR_OPCODE_POPRET,  INSTR_MASK_PUSHPOP)  ||
            match_instr_raw_f(instr, INSTR_OPCODE_POPRETZ, INSTR_MASK_PUSHPOP);
  endfunction : is_pushpop_f

  function automatic logic is_tablejump_raw_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return  match_instr_raw_f(instr, INSTR_OPCODE_TABLEJUMP, INSTR_MASK_TABLEJUMP);
  endfunction : is_tablejump_raw_f

  function automatic logic is_fencefencei_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return  match_instr_raw_f(instr, INSTR_OPCODE_FENCE,  INSTR_MASK_FENCE)  ||
            match_instr_raw_f(instr, INSTR_OPCODE_FENCEI, INSTR_MASK_FENCEI);
  endfunction : is_fencefencei_f

  function automatic logic is_compressed_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return (instr[1:0] != 2'b11);
  endfunction : is_compressed_f

//endpackage

`endif // __ISA_SUPPORT__

