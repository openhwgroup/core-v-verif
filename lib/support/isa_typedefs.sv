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

// -------------------------------------------------------------------
// This file holds typedefs related to the ISA
// -------------------------------------------------------------------

`ifndef __ISA_TYPEDEFS__
`define __ISA_TYPEDEFS__

`include "isa_typedefs_csr.sv"

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


`endif // __ISA_TYPEDEFS__
