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
    DSCRATCH1     = 12'h7B3,
    CPUCTRL       = 12'hBF0,
    SECURESEED0   = 12'hBF9,
    SECURESEED1   = 12'hBFA,
    SECURESEED2   = 12'hBFC
  } csr_name_e;

  // ---------------------------------------------------------------------------
  // Instruction names, add instructions as needed
  // ---------------------------------------------------------------------------
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
    //Zba
    SH1ADD,
    SH2ADD,
    SH3ADD,
    //Zbb
    MIN,
    MINU,
    MAX,
    MAXU,
    CPOP,
    CTZ,
    ORCB,
    ORN,
    CLZ,
    ANDN,
    ROL,
    ROR,
    RORI,
    XNOR,
    REV8,
    SEXTB,
    SEXTH,
    ZEXTH,
    //Zbc
    CLMUL,
    CLMULH,
    CLMULR,
    //Zbs
    BCLR,
    BCLRI,
    BEXT,
    BEXTI,
    BINV,
    BINVI,
    BSET,
    BSETI,
    //M
    MUL,
    MULH,
    MULHSU,
    MULHU,
    DIV,
    DIVU,
    REM,
    REMU,
    // Compressed
    //Zca
    C_EBREAK,
    C_LWSP,
    C_FLWSP, //QUESTION: Not included in Zca?
    C_FLDSP, //QUESTION: Not included in Zca?
    C_SWSP,
    C_FSWSP,
    C_FSDSP,
    //Zcb
    C_LBU,
    C_LHU,
    C_LH,
    C_SB,
    C_SH,
    C_ZEXTB,
    C_SEXTB,
    C_ZEXTH,
    C_SEXTH,
    C_NOT,
    C_MUL,
    //Zcmp
    CM_PUSH,
    CM_POP,
    CM_POPRET,
    CM_POPRETZ,
    CM_MVA01S,
    CM_MVSA01,
    //Zcmt
    CM_JT,
    CM_JALT,


    // Pseudo name, class of instructions
    STORE_INSTR,
    LOAD_INSTR,
    // Unknown for instructions that cannot be decoded
    UNKNOWN_INSTR
  } instr_name_e;

  // ---------------------------------------------------------------------------
  // GPR Registers
  // ---------------------------------------------------------------------------
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


  // TODO opcode map for rv32c - problem here is that it is multi-field dependent.
  typedef enum logic [1:0] {
    C0 = 2'b00, C1 = 2'b01, C2 = 2'b10, C3 = 2'b11 /* C3 does not exist, is uncompressed */
  } compressed_major_opcode_e;



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


  // Minor opcodes for Zba
  typedef enum logic [2:0] {
    FUNCT3_SH2ADD = 3'b100,
    FUNCT3_SH3ADD = 3'b110,
    FUNCT3_SH1ADD = 3'b010
  } zba_minor_opcode_e;

  // Minor opcodes for Zbb
  // Minor opcodes for min and max instructions
  typedef enum logic [2:0] {
    FUNCT3_MIN   = 3'b100,
    FUNCT3_MINU  = 3'b101,
    FUNCT3_MAX   = 3'b110,
    FUNCT3_MAXU  = 3'b111
  } zbb_min_max_minor_opcode_e;

  // Minor opcodes for logical operators and sign extend (FUNCT3_SEXT)
  typedef enum logic [2:0] {
    FUNCT3_XNOR = 3'b100,
    FUNCT3_ORCB = 3'b101,
    FUNCT3_ORN  = 3'b110,
    FUNCT3_ANDN = 3'b111,
    FUNCT3_SEXT = 3'b001
  } zbb_logical_minor_opcode_e;

  // Minor opcodes for rotate instructions
  typedef enum logic [2:0] {
    FUNCT3_ROR_RORI = 3'b101,
    FUNCT3_ROL      = 3'b001
  } zbb_rotate_minor_opcode_e;

  // Minor opcodes for byte reverse register (FUNCT3_REV8), count instructions (FUNCT3_C)
  // and zero extend halfword instruction (FUNCT3_ZEXTH).
  // FUNCT3_C is correct for all count isntructions.
  typedef enum logic [2:0] {
    FUNCT3_REV8  = 3'b101,
    FUNCT3_C     = 3'b001,
    FUNCT3_ZEXTH = 3'b100
  } zbb_rev8_c_zexth_minor_opcode_e;

  // Minor opcodes for Zbc
  typedef enum logic [2:0] {
    FUNCT3_CLMUL  = 3'b001,
    FUNCT3_CLMULR = 3'b010,
    FUNCT3_CLMULH = 3'b011
  } zbc_minor_opcode_e;

  // Minor opcodes for Zbs
  // FUNCT3_B_BI corresponds to all single-Bit instructions other than BEXT and BEXTI.
  typedef enum logic [2:0] {
    FUNCT3_BEXT_BEXTI = 3'b101,
    FUNCT3_B_BI       = 3'b001
  } zbs_single_bit_minor_opcode_e;

  // Minor opcodes for multiplication and division, "M".
  typedef enum logic [2:0] {
    FUNCT3_MUL    = 3'b000,
    FUNCT3_MULH   = 3'b001,
    FUNCT3_MULHSU = 3'b010,
    FUNCT3_MULHU  = 3'b011,
    FUNCT3_DIV    = 3'b100,
    FUNCT3_DIVU   = 3'b101,
    FUNCT3_REM    = 3'b110,
    FUNCT3_REMU   = 3'b111
  } m_minor_opcode_e;

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
    logic [31:25]  imm_h;
    gpr_t          rs2;
    gpr_t          rs1;
    logic [14:12]  funct3;
    logic [11:7]   imm_l;
  } b_type_t;

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
    compressed_major_opcode_e opcode;
  } compressed_instr_t;

  typedef union packed {
    compressed_instr_t   compressed;
    uncompressed_instr_t uncompressed;
  } instr_t;

  // ---------------------------------------------------------------------------
  // Datatypes used for disassembled instructions, fields that are not
  // applicable to all instructions are qualified with a valid bit in the
  // respective structure.
  // ---------------------------------------------------------------------------


  // ---------------------------------------------------------------------------
  // gpr structure, can represent raw value, enumerated non-abi machine register
  // and enumerated abi register names
  // ---------------------------------------------------------------------------
  typedef struct packed {
    gpr_t gpr;
    bit   valid;
  } reg_operand_t;

  // ---------------------------------------------------------------------------
  // Datatype to represent disassemblede immediate
  //
  // TODO: defer until needed
  // * Add non-interpreted sorted bitfields for immediates
  // * Add width-fields and associated logic for setting immediate
  //   and non-interpreted immediate bitfield widths
  // * Add type/sign-extension fields and associated logic
  // ---------------------------------------------------------------------------
  typedef struct packed {
    logic[31:0] imm;
    //logic[31:0] imm_raw;
    //imm_e       imm_type;
    //int         width;
    //bit         sign_ext;
    bit         valid;
  } imm_operand_t;

  typedef struct packed {
    union packed {
      csr_name_e    name;
    } address;
    bit           valid;
  } csr_operand_t;
  // ---------------------------------------------------------------------------
  // Currently not used, can be used as an intermediate representation for
  // an register + offset field in assembly
  // ---------------------------------------------------------------------------
  typedef struct packed {
    int   offset;
    gpr_t gpr;
    bit   valid;
  } mem_operand_t;

  // TODO Zc
  // typedef struct packed {
  //   rlist_t rlist;
  //   bit     valid;
  // } rlist_operand_t;

  // ---------------------------------------------------------------------------
  // Instruction formats
  // ---------------------------------------------------------------------------
  typedef enum logic[7:0] {
    I_TYPE,
    J_TYPE,
    S_TYPE,
    R_TYPE,
    R4_TYPE,
    B_TYPE,
    U_TYPE,
    // Compressed formats
    CR_TYPE,
    CI_TYPE,
    CSS_TYPE,
    CIW_TYPE,
    CL_TYPE,
    CS_TYPE,
    CA_TYPE,
    CB_TYPE,
    CJ_TYPE,
    // Others
    UNKNOWN_FORMAT
  } instr_format_e;

  // ---------------------------------------------------------------------------
  // Main _decoded_ and _disassembled_ data structure
  // ---------------------------------------------------------------------------
  typedef struct packed {
    instr_name_e  instr;    // Instruction name
    instr_format_e format;  // Instruction format type
    reg_operand_t rd;       // Destination register, qualified by rd.valid
    reg_operand_t rs1;      // source register 1, qualified by rs1.valid
    reg_operand_t rs2;      //      --         2,      --        2
    reg_operand_t rs3;      //      --         3,      --        3
    imm_operand_t imm;      // Immediate, qualified by imm.valid
    csr_operand_t csr;      // CSR register address, qualified by csr.valid
    // rlist_operand_t rlist; // TODO: structure to handle rlist fields for Zcmp-instructions
  } asm_t;


  // ---------------------------------------------------------------------------
  // Non-trivial immediate decoder
  // ---------------------------------------------------------------------------
  function logic [20:0] get_j_imm(instr_t instr);
    get_j_imm = {
      instr.uncompressed.format.j.imm[31],
      instr.uncompressed.format.j.imm[21:12],
      instr.uncompressed.format.j.imm[22],
      instr.uncompressed.format.j.imm[30:23],
      1'b0
    };
  endfunction : get_j_imm

  function logic [11:0] get_s_imm(instr_t instr);
    get_s_imm = {
      instr.uncompressed.format.s.imm_h,
      instr.uncompressed.format.s.imm_l
    };
  endfunction : get_s_imm

  function logic[11:0] get_b_imm(instr_t instr);
    get_b_imm = {
      instr.uncompressed.format.b.imm_h[31],
      instr.uncompressed.format.b.imm_l[7],
      instr.uncompressed.format.b.imm_h[30:25],
      instr.uncompressed.format.b.imm_l[11:8]
    };
  endfunction : get_b_imm

  // ---------------------------------------------------------------------------
  // build_asm intends to implement a decoder for the Risc-V ISA
  // (Currently only RV32I, Zicsr plus a few select other instructions are
  // supported)
  //
  // The ouput format intends to decode the instruction in a human readable
  // manner, and aims to populate a structure that can be easily parsed to
  // generate proper risc-v assembly code.
  // ---------------------------------------------------------------------------

  function automatic asm_t build_asm(instr_name_e name, instr_format_e format, instr_t instr);
    asm_t asm  = { '0 };
    asm.instr  = name;
    asm.format = format;

    casex (format)
      I_TYPE: begin
        if (asm.instr inside { FENCEI, ECALL, EBREAK, MRET, DRET, WFI, WFE }) begin
          asm.rd.valid    = 0;
          asm.rs1.valid   = 0;
          asm.rs2.valid   = 0;
          asm.imm.valid   = 0;
        end else if (asm.instr inside { CSRRW, CSRRS, CSRRC }) begin
          asm.rd.gpr      = instr.uncompressed.format.i.rd.gpr;
          asm.rs1.gpr     = instr.uncompressed.format.i.rs1.gpr;
          asm.csr.address = instr.uncompressed.format.i.imm;
          asm.rd.valid    = 1;
          asm.rs1.valid   = 1;
          asm.csr.valid   = 1;
        end else if (asm.instr inside { CSRRWI, CSRRSI, CSRRCI }) begin
          asm.rd.gpr      = instr.uncompressed.format.i.rd.gpr;
          asm.imm.imm     = instr.uncompressed.format.i.rs1;
          asm.csr.address = instr.uncompressed.format.i.imm;
          asm.rd.valid    = 1;
          asm.imm.valid   = 1;
          asm.csr.valid   = 1;
        end else if (asm.instr inside { RORI, BEXTI, BCLRI, BINVI, BSETI, SLLI, SRLI, SRAI }) begin
          asm.rd.gpr      = instr.uncompressed.format.i.rd.gpr;
          asm.rs1.gpr     = instr.uncompressed.format.i.rs1.gpr;
          asm.imm.imm     = instr.uncompressed.format.i.imm.shamt;
          asm.rd.valid    = 1;
          asm.rs1.valid   = 1;
          asm.imm.valid   = 1;
        end else begin
          asm.rd.gpr      = instr.uncompressed.format.i.rd.gpr;
          asm.rs1.gpr     = instr.uncompressed.format.i.rs1.gpr;
          asm.imm.imm     = instr.uncompressed.format.i.imm;
          asm.rd.valid    = 1;
          asm.rs1.valid   = 1;
          asm.imm.valid   = 1;
        end
      end

      J_TYPE: begin
        asm.rd.gpr      = instr.uncompressed.format.j.rd.gpr;
        asm.imm.imm     = get_j_imm(instr);
        asm.rd.valid    = 1;
        asm.imm.valid   = 1;
      end
      S_TYPE: begin
        asm.rs1.gpr     = instr.uncompressed.format.s.rs1.gpr;
        asm.rs2.gpr     = instr.uncompressed.format.s.rs2.gpr;
        asm.imm.imm     = get_s_imm(instr);
        asm.rs1.valid   = 1;
        asm.rs2.valid   = 1;
        asm.imm.valid   = 1;
      end
      R_TYPE: begin
        asm.rd.gpr      = instr.uncompressed.format.r.rd.gpr;
        asm.rs1.gpr     = instr.uncompressed.format.r.rs1.gpr;
        asm.rs2.gpr     = instr.uncompressed.format.r.rs2.gpr;
        asm.rd.valid    = 1;
        asm.rs1.valid   = 1;
        asm.rs2.valid   = 1;
      end
      R4_TYPE: begin
        asm.rd.gpr      = instr.uncompressed.format.r4.rd.gpr;
        asm.rs1.gpr     = instr.uncompressed.format.r4.rs1.gpr;
        asm.rs2.gpr     = instr.uncompressed.format.r4.rs2.gpr;
        asm.rs3.gpr     = instr.uncompressed.format.r4.rs3.gpr;
        asm.rd.valid    = 1;
        asm.rs1.valid   = 1;
        asm.rs2.valid   = 1;
        asm.rs3.valid   = 1;
      end
      B_TYPE: begin
        asm.rs1.gpr     = instr.uncompressed.format.b.rs1.gpr;
        asm.rs2.gpr     = instr.uncompressed.format.b.rs2.gpr;
        asm.imm.imm     = get_b_imm(instr);
        asm.rs1.valid   = 1;
        asm.rs2.valid   = 1;
        asm.imm.valid   = 1;
      end
      U_TYPE: begin
        asm.rd.gpr      = instr.uncompressed.format.u.rd.gpr;
        asm.imm.imm     = { instr.uncompressed.format.u.imm, 12'b0000_0000_0000 };
        asm.rd.valid    = 1;
        asm.imm.valid   = 1;
      end
      // TODO: Expand with compressed
      CR_TYPE: begin
        if (name inside { C_EBREAK }) begin
          asm.rd.valid  = 0;
          asm.rs1.valid = 0;
          asm.rs2.valid = 0;
          asm.rs3.valid = 0;
          asm.imm.valid = 0;
        end
      end

      //TODO:
      // CI_TYPE: begin

      // end
      // CSS_TYPE: begin

      // end
      // CIW_TYPE: begin

      // end
      // CL_TYPE: begin

      // end
      // CS_TYPE: begin

      // end
      // CA_TYPE: begin

      // end
      // CB_TYPE: begin

      // end
      // CJ_TYPE: begin

      // end

      default : ;
    endcase

    return asm;
  endfunction : build_asm

  // ---------------------------------------------------------------------------
  // Main decoder logic, identifies type and instruction name,
  // add instructions here as needed.
  // ---------------------------------------------------------------------------
  function automatic asm_t decode_instr(instr_t instr);
    asm_t asm = { '0 };
    casex (1)
      (   (instr.uncompressed.opcode              == MISC_MEM)
       && (instr.uncompressed.format.i.rd         == 5'b0_0000)
       && (instr.uncompressed.format.i.funct3     == 3'b001)
       && (instr.uncompressed.format.i.rs1        == 5'b0_0000)
       && (instr.uncompressed.format.i.imm        == 12'h000)) :
        asm = build_asm(FENCEI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.imm        == 12'b0000_0000_0000)) :
        asm = build_asm(ECALL, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.imm        == 12'b0000_0000_0001)) :
        asm = build_asm(EBREAK, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.rd         == 5'b0_0000)
       && (instr.uncompressed.format.i.funct3     == 3'b000)
       && (instr.uncompressed.format.i.rs1        == 5'b0_0000)
       && (instr.uncompressed.format.i.imm        == 12'b0011_0000_0010)) :
        asm = build_asm(MRET, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.imm        == 12'b0111_1011_0010)) :
        asm = build_asm(DRET, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.rd         == 5'b0_0000)
       && (instr.uncompressed.format.i.funct3     == 3'b000)
       && (instr.uncompressed.format.i.rs1        == 5'b0_0000)
       && (instr.uncompressed.format.i.imm        == 12'b0001_0000_0101)) :
        asm = build_asm(WFI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.rd         == 5'b0_0000)
       && (instr.uncompressed.format.i.funct3     == 3'b000)
       && (instr.uncompressed.format.i.rs1        == 5'b0_0000)
       && (instr.uncompressed.format.i.imm        == 12'b1000_1100_0000)) :
        asm = build_asm(WFE, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_CSRRW)) :
        asm = build_asm(CSRRW, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_CSRRS)) :
        asm = build_asm(CSRRS, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_CSRRC)) :
        asm = build_asm(CSRRC, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_CSRRWI)) :
        asm = build_asm(CSRRWI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_CSRRSI)) :
        asm = build_asm(CSRRSI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == SYSTEM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_CSRRCI)) :
        asm = build_asm(CSRRCI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == STORE)
       && (instr.uncompressed.format.s.funct3     == FUNCT3_SB)) :
        asm = build_asm(SB, S_TYPE, instr);

      (   (instr.uncompressed.opcode              == STORE)
       && (instr.uncompressed.format.s.funct3     == FUNCT3_SH)) :
        asm = build_asm(SH, S_TYPE, instr);

      (   (instr.uncompressed.opcode              == STORE)
       && (instr.uncompressed.format.s.funct3     == FUNCT3_SW)) :
        asm = build_asm(SW, S_TYPE, instr);

      (   (instr.uncompressed.opcode              == LOAD)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_LB)) :
        asm = build_asm(LB, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == LOAD)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_LH)) :
        asm = build_asm(LH, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == LOAD)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_LW)) :
        asm = build_asm(LW, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == LOAD)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_LBU)) :
        asm = build_asm(LBU, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == LOAD)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_LHU)) :
        asm = build_asm(LHU, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_ADDI)) :
        asm = build_asm(ADDI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SLTI)) :
        asm = build_asm(SLTI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SLTIU)) :
        asm = build_asm(SLTIU, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_XORI)) :
        asm = build_asm(XORI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_ORI)) :
        asm = build_asm(ORI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_ANDI)) :
        asm = build_asm(ANDI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SLLI)
       && (instr.uncompressed.format.i.imm.funct7 == 7'b0000000)) :
        asm = build_asm(SLLI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SRLI_SRAI)
       && (instr.uncompressed.format.i.imm.funct7 == 7'b0000000)) :
        asm = build_asm(SRLI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SRLI_SRAI)
       && (instr.uncompressed.format.i.imm.funct7 == 7'b0100000)) :
        asm = build_asm(SRAI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_ADD_SUB)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        asm = build_asm(ADD, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_ADD_SUB)
       && (instr.uncompressed.format.r.funct7     == 7'b0100000)) :
        asm = build_asm(SUB, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SLL)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        asm = build_asm(SLL, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SLT)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        asm = build_asm(SLT, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SLTU)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        asm = build_asm(SLTU, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_XOR)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        asm = build_asm(XOR, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SRL_SRA)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        asm = build_asm(SRL, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SRL_SRA)
       && (instr.uncompressed.format.r.funct7     == 7'b0100000)) :
        asm = build_asm(SRA, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_OR)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        asm = build_asm(OR, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_AND)
       && (instr.uncompressed.format.r.funct7     == 7'b0000000)) :
        asm = build_asm(AND, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == LUI_OP) ) :
        asm = build_asm(LUI, U_TYPE, instr);

      (   (instr.uncompressed.opcode              == AUIPC_OP) ) :
        asm = build_asm(AUIPC, U_TYPE, instr);

      (   (instr.uncompressed.opcode              == JALR_OP) ) :
        asm = build_asm(JALR, J_TYPE, instr);

      (   (instr.uncompressed.opcode              == JAL_OP) ) :
        asm = build_asm(JAL, J_TYPE, instr);

      (   (instr.uncompressed.opcode              == BRANCH)
       && (instr.uncompressed.format.b.funct3     == FUNCT3_BEQ)) :
        asm = build_asm(BEQ, B_TYPE, instr);

      (   (instr.uncompressed.opcode              == BRANCH)
       && (instr.uncompressed.format.b.funct3     == FUNCT3_BNE)) :
        asm = build_asm(BNE, B_TYPE, instr);

      (   (instr.uncompressed.opcode              == BRANCH)
       && (instr.uncompressed.format.b.funct3     == FUNCT3_BLT)) :
        asm = build_asm(BLT, B_TYPE, instr);

      (   (instr.uncompressed.opcode              == BRANCH)
       && (instr.uncompressed.format.b.funct3     == FUNCT3_BGE)) :
        asm = build_asm(BGE, B_TYPE, instr);

      (   (instr.uncompressed.opcode              == BRANCH)
       && (instr.uncompressed.format.b.funct3     == FUNCT3_BLTU)) :
        asm = build_asm(BLTU, B_TYPE, instr);

      (   (instr.uncompressed.opcode              == BRANCH)
       && (instr.uncompressed.format.b.funct3     == FUNCT3_BGEU)) :
        asm = build_asm(BGEU, B_TYPE, instr);

      //Zba
      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SH1ADD)
       && (instr.uncompressed.format.r.funct7     == 7'b001_0000)) :
        asm = build_asm(SH1ADD, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SH2ADD)
       && (instr.uncompressed.format.r.funct7     == 7'b001_0000)) :
        asm = build_asm(SH2ADD, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SH3ADD)
       && (instr.uncompressed.format.r.funct7     == 7'b001_0000)) :
        asm = build_asm(SH3ADD, R_TYPE, instr);

      //Zbb
      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MIN)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0101)) :
        asm = build_asm(MIN, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MINU)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0101)) :
        asm = build_asm(MINU, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MAX)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0101)) :
        asm = build_asm(MAX, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MAXU)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0101)) :
        asm = build_asm(MAXU, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_C)
       && (instr.uncompressed.format.i.imm        == 12'b0110_0000_0010)) :
        asm = build_asm(CPOP, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_C)
       && (instr.uncompressed.format.i.imm        == 12'b0110_0000_0001)) :
        asm = build_asm(CTZ, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_ORCB)
       && (instr.uncompressed.format.i.imm        == 12'b0010_1000_0111)) :
        asm = build_asm(ORCB, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_ORN)
       && (instr.uncompressed.format.r.funct7     == 7'b010_0000)) :
        asm = build_asm(ORN, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_C)
       && (instr.uncompressed.format.i.imm        == 12'b0110_0000_0000)) :
        asm = build_asm(CLZ, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_ANDN)
       && (instr.uncompressed.format.r.funct7     == 7'b010_0000)) :
        asm = build_asm(ANDN, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_ROL)
       && (instr.uncompressed.format.r.funct7     == 7'b011_0000)) :
        asm = build_asm(ROL, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_ROR_RORI)
       && (instr.uncompressed.format.r.funct7     == 7'b011_0000)) :
        asm = build_asm(ROR, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_ROR_RORI)
       && (instr.uncompressed.format.i.imm.funct7 == 7'b011_0000)) :
        asm = build_asm(RORI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_XNOR)
       && (instr.uncompressed.format.r.funct7     == 7'b010_0000)) :
        asm = build_asm(XNOR, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_REV8)
       && (instr.uncompressed.format.i.imm        == 12'b0110_1001_1000)) :
        asm = build_asm(REV8, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SEXT)
       && (instr.uncompressed.format.i.imm        == 12'b0110_0000_0100)) :
        asm = build_asm(SEXTB, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SEXT)
       && (instr.uncompressed.format.i.imm        == 12'b0110_0000_0101)) :
        asm = build_asm(SEXTH, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_ZEXTH)
       && (instr.uncompressed.format.i.imm        == 12'b0000_1000_0000)) :
        asm = build_asm(ZEXTH, I_TYPE, instr);

      //Zbc
      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_CLMUL)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0101)) :
        asm = build_asm(CLMUL, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_CLMULH)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0101)) :
        asm = build_asm(CLMULH, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_CLMULR)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0101)) :
        asm = build_asm(CLMULR, R_TYPE, instr);

      //Zbs
      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_BEXT_BEXTI)
       && (instr.uncompressed.format.r.funct7     == 7'b010_0100)) :
        asm = build_asm(BEXT, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_BEXT_BEXTI)
       && (instr.uncompressed.format.i.imm.funct7 == 7'b010_0100)) :
        asm = build_asm(BEXTI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_B_BI)
       && (instr.uncompressed.format.r.funct7     == 7'b010_0100)) :
        asm = build_asm(BCLR, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_B_BI)
       && (instr.uncompressed.format.i.imm.funct7 == 7'b010_0100)) :
        asm = build_asm(BCLRI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_B_BI)
       && (instr.uncompressed.format.r.funct7     == 7'b011_0100)) :
        asm = build_asm(BINV, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_B_BI)
       && (instr.uncompressed.format.i.imm.funct7 == 7'b011_0100)) :
        asm = build_asm(BINVI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_B_BI)
       && (instr.uncompressed.format.r.funct7     == 7'b001_0100)) :
        asm = build_asm(BSET, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_B_BI)
       && (instr.uncompressed.format.i.imm.funct7 == 7'b001_0100)) :
        asm = build_asm(BSETI, I_TYPE, instr);

      //M
      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MUL)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0001)) :
        asm = build_asm(MUL, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MULH)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0001)) :
        asm = build_asm(MULH, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MULHSU)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0001)) :
        asm = build_asm(MULHSU, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MULHU)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0001)) :
        asm = build_asm(MULHU, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_DIV)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0001)) :
        asm = build_asm(DIV, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_DIVU)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0001)) :
        asm = build_asm(DIVU, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_REM)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0001)) :
        asm = build_asm(REM, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_REMU)
       && (instr.uncompressed.format.r.funct7     == 7'b000_0001)) :
        asm = build_asm(REMU, R_TYPE, instr);

      // Compressed
      //Zca
      (   (instr.compressed.opcode                == 2'b10)
       && (instr.compressed.format.cr.rd_rs1.gpr  == X0)
       && (instr.compressed.format.cr.rs2.gpr     == X0)
       && (instr.compressed.format.cr.funct4      == 4'b1001)) :
        asm = build_asm(C_EBREAK, CR_TYPE, instr);


      //Zcb
      //Zcmp
      //Zcmt

      default: asm = build_asm(UNKNOWN_INSTR, UNKNOWN_FORMAT, instr_t'(32'h0));
    endcase

    return asm;

  endfunction : decode_instr

  // ---------------------------------------------------------------------------
  // Identify if a given instruction matches an expected instruction name
  // ---------------------------------------------------------------------------
  function match_instr(instr_t instr, instr_name_e instr_type);
    match_instr = (decode_instr(instr).instr == instr_type);
  endfunction : match_instr

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

  function automatic logic is_csr_read_spec_f(asm_t asm);
    if (asm.instr inside { CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI }) begin
      case (asm.instr)
        CSRRW, CSRRWI : is_csr_read_spec_f  = asm.rd.gpr ? 1'b1 : 1'b0;
        CSRRS, CSRRC  : is_csr_read_spec_f  = 1'b1;
        CSRRSI, CSRRCI: is_csr_read_spec_f  = 1'b1;
        // Should never be here
        default       : is_csr_read_spec_f  = 1'b0;
      endcase
    end else begin
      is_csr_read_spec_f = 1'b0;
    end
  endfunction : is_csr_read_spec_f

  function logic is_csr_write_spec_f(asm_t asm);
    if (asm.instr inside { CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI }) begin
      case (asm.instr)
        CSRRW, CSRRWI : is_csr_write_spec_f = 1'b1;
        CSRRS, CSRRC  : is_csr_write_spec_f = asm.rs1.gpr  ? 1'b1 : 1'b0;
        CSRRSI, CSRRCI: is_csr_write_spec_f = asm.imm.imm  ? 1'b1 : 1'b0;
        // Should never be here
        default       : is_csr_write_spec_f = 1'b0;
      endcase
    end else begin
      is_csr_write_spec_f = 1'b0;
    end
  endfunction : is_csr_write_spec_f

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

