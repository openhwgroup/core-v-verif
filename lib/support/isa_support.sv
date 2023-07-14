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
    // Unknown for instructions that cannot be decoded
    UNKNOWN_INSTR = 0,
    FENCE,
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
    ILLEGAL_INSTR,
    //Zca
    C_LWSP,
    C_SWSP,
    C_LW,
    C_SW,
    C_EBREAK,
    C_MV,
    C_ADD,
    C_LI,
    C_LUI,
    C_JR,
    C_JALR,
    C_J,
    C_JAL,
    C_ANDI,
    C_AND,
    C_OR,
    C_XOR,
    C_SUB,
    C_NOP,
    C_ADDI4SPN,
    C_ADDI16SP,
    C_ADDI,
    C_SLLI,
    C_SRLI,
    C_SRAI,
    C_BEQZ,
    C_BNEZ,
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
    //Hints
    HINT_C_LI,
    HINT_C_LUI,
    HINT_C_NOP,
    HINT_C_ADDI,
    HINT_C_MV,
    HINT_C_ADD,
    // Pseudo name, class of instructions
    STORE_INSTR,
    LOAD_INSTR

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
    bit [2:0]        raw;
    c_gpr_name_e     gpr;
    c_gpr_abi_name_e gpr_abi;
  } c_gpr_t;

  typedef union packed {
    bit [4:0]      raw;
    gpr_name_e     gpr;
    gpr_abi_name_e gpr_abi;
  } gpr_t;

  // ---------------------------------------------------------------------------
  // Rlist for zcmp instructions
  // ---------------------------------------------------------------------------
  typedef enum logic [3:0] {
    X1__                = 4'd4,
    X1__X8              = 4'd5,
    X1__X8_X9           = 4'd6,
    X1__X8_X9__X18      = 4'd7,
    X1__X8_X9__X18_X19  = 4'd8,
    X1__X8_X9__X18_X20  = 4'd9,
    X1__X8_X9__X18_X21  = 4'd10,
    X1__X8_X9__X18_X22  = 4'd11,
    X1__X8_X9__X18_X23  = 4'd12,
    X1__X8_X9__X18_X24  = 4'd13,
    X1__X8_X9__X18_X25  = 4'd14,
    X1__X8_X9__X18_X27  = 4'd15
  } rlist_name_e;

  typedef enum logic [3:0] {
    RA__        = 4'd4,
    RA__S0      = 4'd5,
    RA__S0_S1   = 4'd6,
    RA__S0_S2   = 4'd7,
    RA__S0_S3   = 4'd8,
    RA__S0_S4   = 4'd9,
    RA__S0_S5   = 4'd10,
    RA__S0_S6   = 4'd11,
    RA__S0_S7   = 4'd12,
    RA__S0_S8   = 4'd13,
    RA__S0_S9   = 4'd14,
    RA__S0_S11  = 4'd15
  } rlist_abi_name_e;

  typedef union packed {
    bit [3:0]      raw;
    rlist_name_e     rlist;
    rlist_abi_name_e rlist_abi;
  } rlist_t;

  // ---------------------------------------------------------------------------
  // Stack_adj for zcmp instructions
  // ---------------------------------------------------------------------------
  function int get_stack_adj( rlist_t rlist, logic[5:4] spimm);
    int stack_adj_base;
    int stack_adj;

    case(rlist) inside
      [4:7]:    stack_adj_base = 16;
      [8:11]:   stack_adj_base = 32;
      [12:14]:  stack_adj_base = 48;
      15:       stack_adj_base = 64;
      default:  stack_adj_base = 0;
    endcase

    stack_adj = stack_adj_base + spimm*16;
    return stack_adj;
  endfunction

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

  typedef enum logic [2:0] {
    FUNCT3_C_SRLI_SRAI  = 3'b100,
    FUNCT3_C_SLLI       = 3'b000,
    FUNCT3_C_SW         = 3'b110
  } compressed_shift_store_minor_opcode_e;

  typedef enum logic [2:0] {
    FUNCT3_C_BEQZ  = 3'b110,
    FUNCT3_C_BNEZ  = 3'b111,
    FUNCT3_C_J     = 3'b101,
    FUNCT3_C_JAL   = 3'b001
  } compressed_branch_jump_minor_opcode_e;

  typedef enum logic [2:0] {
    FUNCT3_C_LI_LW  = 3'b010,
    FUNCT3_C_LUI    = 3'b011
  } compressed_load_minor_opcode_e;

  typedef enum logic [2:0] {
    FUNCT3_C_LWSP     = 3'b010,
    FUNCT3_C_SWSP     = 3'b110,
    FUNCT3_C_ADDI4SPN = 3'b000,
    FUNCT3_C_ADDI16SP = 3'b011
  } compressed_sp_minor_opcode_e;

  typedef enum logic [2:0] {
    FUNCT3_C_ANDI     = 3'b100,
    FUNCT3_C_ADDI_NOP = 3'b000
  } compressed_minor_opcode_e;

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


  typedef enum logic [4:0] {
    FUNCT5_C_ZEXTB = 5'b11000,
    FUNCT5_C_SEXTB = 5'b11001,
    FUNCT5_C_ZEXTH = 5'b11010,
    FUNCT5_C_SEXTH = 5'b11011,
    FUNCT5_C_NOT   = 5'b11101
  } funct5_e;

  // Funct7
  typedef enum logic [6:0] {
    FUNCT7_ZBB_MIN_MAX 		= 7'b000_0101,
    FUNCT7_ZBB_LOGICAL 		= 7'b010_0000,
    FUNCT7_ZBB_ROTATE  		= 7'b011_0000,
    FUNCT7_ZBS_BCLR_BEXT 	= 7'b010_0100,
    FUNCT7_ZBS_BINV 		  = 7'b011_0100,
    FUNCT7_ZBS_BSET  		  = 7'b001_0100
  } zbb_zbs_funct7_e;

  typedef enum logic [6:0] {
    FUNCT7_ZBA  = 7'b001_0000,
    FUNCT7_ZBC  = 7'b000_0101,
    FUNCT7_M	  = 7'b000_0001
  } zba_zbc_m_funct7_e;

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

  typedef struct packed {
    logic[15:10] funct6;
    c_gpr_t      rs1;
    logic[6:5]   uimm;
    c_gpr_t      rd;
  } clb_type_t;

  typedef struct packed {
    logic[15:10] funct6;
    c_gpr_t      rs1;
    logic[6:5]   uimm;
    c_gpr_t      rs2;
  } csb_type_t;

  typedef struct packed {
    logic[15:10] funct6;
    c_gpr_t      rs1;
    logic     funct1;
    logic     uimm;
    c_gpr_t      rd;
  } clh_type_t;

  typedef struct packed {
    logic[15:10] funct6;
    c_gpr_t      rs1;
    logic     funct1;
    logic     uimm;
    c_gpr_t      rs2;
  } csh_type_t;

  typedef struct packed {
    logic[15:10] funct6;
    c_gpr_t      rd_rs1;
    logic[6:2]   funct5;
  } cu_type_t;

  typedef struct packed {
    logic[15:10] funct6;
    c_gpr_t      r1s;
    logic[6:5]   funct2;
    c_gpr_t      r2s;
  } cmmv_type_t;

  typedef struct packed {
    logic[15:10] funct6;
    logic[9:2]   index;
  } cmjt_type_t;

  typedef struct packed {
    logic[15:10] funct6;
    logic[9:8]   funct2;
    rlist_t      urlist;
    logic[5:4]   spimm;
  } cmpp_type_t;

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
      clb_type_t   clb;
      csb_type_t   csb;
      clh_type_t   clh;
      csh_type_t   csh;
      cu_type_t    cu;
      cmmv_type_t  cmmv;
      cmjt_type_t  cmjt;
      cmpp_type_t  cmpp;
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

  //Immediate types
  typedef enum {
    IMM,
    NZIMM,
    NZUIMM,
    OFFSET,
    I_IMM,
    U_IMM,
    SHAMT,
    UIMM,
    SPIMM,
    INDEX
  } imm_e;

  typedef struct packed {
    int       imm_value;
    bit[31:0] imm_raw;        // The immediate in the order it is presented in the instruction without shifting.
    bit[31:0] imm_raw_sorted; // The immediate sorted in the correct order. No shifitng.
    imm_e     imm_type;       // States the type of the immediate
    int       width;          // Number of bits in immediate
    bit       sign_ext;       // Indicates whether the immediate is sign-extended or not.
    bit       valid;
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

  // rlist operand for Zcmp instructions
  typedef struct packed {
    rlist_t rlist;
    bit     valid;
  } rlist_operand_t;

  // stack_adj operand for Zcmp instructions
  typedef struct packed {
    int         stack_adj;
    bit         valid;
  } stack_adj_operand_t;

  // ---------------------------------------------------------------------------
  // Instruction formats
  // ---------------------------------------------------------------------------
  typedef enum logic[7:0] {
    // Others
    UNKNOWN_FORMAT = 0,
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
    CLB_TYPE,
    CSB_TYPE,
    CLH_TYPE,
    CSH_TYPE,
    CU_TYPE,
    CMMV_TYPE,
    CMJT_TYPE,
    CMPP_TYPE
  } instr_format_e;

  // ---------------------------------------------------------------------------
  // Main _decoded_ and _disassembled_ data structure
  // ---------------------------------------------------------------------------
  typedef struct packed {
    instr_name_e        instr;    // Instruction name
    instr_format_e      format;  // Instruction format type
    reg_operand_t       rd;       // Destination register, qualified by rd.valid
    reg_operand_t       rs1;      // source register 1, qualified by rs1.valid
    reg_operand_t       rs2;      //      --         2,      --        2
    reg_operand_t       rs3;      //      --         3,      --        3
    imm_operand_t       imm;      // Immediate, qualified by imm.valid
    csr_operand_t       csr;      // CSR register address, qualified by csr.valid
    logic               is_hint;  // Indicates whether the current instruction is a HINT.
    rlist_operand_t     rlist;  // structure to handle rlist fields for Zcmp-instructions
    stack_adj_operand_t stack_adj; // structure to handle stack_adj fields for Zcmp-instructions
  } asm_t;


  // ---------------------------------------------------------------------------
  // Non-trivial immediate decoder
  // ---------------------------------------------------------------------------
  function logic [20:1] get_sort_j_imm(instr_t instr);
    get_sort_j_imm = {
      instr.uncompressed.format.j.imm[31],
      instr.uncompressed.format.j.imm[21:12],
      instr.uncompressed.format.j.imm[22],
      instr.uncompressed.format.j.imm[30:23]
    };
  endfunction : get_sort_j_imm

  function logic [11:0] get_sort_s_imm(instr_t instr);
    get_sort_s_imm = {
      instr.uncompressed.format.s.imm_h,
      instr.uncompressed.format.s.imm_l
    };
  endfunction : get_sort_s_imm

  function logic [12:1] get_sort_b_imm(instr_t instr);
    get_sort_b_imm = {
      instr.uncompressed.format.b.imm_h[31],
      instr.uncompressed.format.b.imm_l[7],
      instr.uncompressed.format.b.imm_h[30:25],
      instr.uncompressed.format.b.imm_l[11:8]
    };
  endfunction : get_sort_b_imm

  function logic [5:0] get_sort_ci_imm_lwsp(instr_t instr);
    get_sort_ci_imm_lwsp = {
      instr.compressed.format.ci.imm_6_2[3:2],
      instr.compressed.format.ci.imm_12,
      instr.compressed.format.ci.imm_6_2[6:4]
    };
  endfunction : get_sort_ci_imm_lwsp

  function logic [5:0] get_sort_ci_imm_addi16sp(instr_t instr);
    get_sort_ci_imm_addi16sp = {
      instr.compressed.format.ci.imm_12,
      instr.compressed.format.ci.imm_6_2[4:3],
      instr.compressed.format.ci.imm_6_2[5],
      instr.compressed.format.ci.imm_6_2[2],
      instr.compressed.format.ci.imm_6_2[6]
    };
  endfunction : get_sort_ci_imm_addi16sp

  function logic [8:0] get_sort_cb_imm_not_sequential(instr_t instr);
    get_sort_cb_imm_not_sequential = {
      instr.compressed.format.cb.offset_12_10[12],
      instr.compressed.format.cb.offset_6_2[6:5],
      instr.compressed.format.cb.offset_6_2[2],
      instr.compressed.format.cb.offset_12_10[11:10],
      instr.compressed.format.cb.offset_6_2[4:3]
    };
  endfunction : get_sort_cb_imm_not_sequential

  function logic [5:0] get_sort_cj_imm(instr_t instr);
      get_sort_cj_imm = {
        instr.compressed.format.cj.imm[12],
        instr.compressed.format.cj.imm[8],
        instr.compressed.format.cj.imm[10:9],
        instr.compressed.format.cj.imm[6],
        instr.compressed.format.cj.imm[7],
        instr.compressed.format.cj.imm[2],
        instr.compressed.format.cj.imm[11],
        instr.compressed.format.cj.imm[5:3]
      };
  endfunction : get_sort_cj_imm

  function logic [4:0] get_sort_cl_imm(instr_t instr);
      get_sort_cl_imm = {
        instr.compressed.format.cl.imm_6_5[5],
        instr.compressed.format.cl.imm_12_10,
        instr.compressed.format.cl.imm_6_5[6]
      };
  endfunction : get_sort_cl_imm

  function logic [4:0] get_sort_cs_imm(instr_t instr);
      get_sort_cs_imm = {
        instr.compressed.format.cs.imm_6_5[5],
        instr.compressed.format.cs.imm_12_10,
        instr.compressed.format.cs.imm_6_5[6]
      };
  endfunction : get_sort_cs_imm

  function logic [7:0] get_sort_ciw_imm(instr_t instr);
    get_sort_ciw_imm = {
      instr.compressed.format.ciw.imm[10:7],
      instr.compressed.format.ciw.imm[12:11],
      instr.compressed.format.ciw.imm[6],
      instr.compressed.format.ciw.imm[5]
      };
  endfunction : get_sort_ciw_imm

  // ---------------------------------------------------------------------------
  // Find the value of immediate
  // ---------------------------------------------------------------------------
  function int get_imm_value_i(logic[11:0] imm);
    if(imm[11] == 1) begin
      get_imm_value_i = {20'hfffff, imm};
    end else begin
      get_imm_value_i = {20'b0, imm};
    end
  endfunction : get_imm_value_i

  function int get_imm_value_j(logic[20:1] imm);
    if(imm[20] == 1) begin
      get_imm_value_j = {11'h7ff, imm, 1'b0};
    end else begin
      get_imm_value_j = {11'b0, imm, 1'b0};
    end
  endfunction : get_imm_value_j

  function int get_imm_value_b(logic[12:1] imm);
    if(imm[12] == 1) begin
      get_imm_value_b = {19'h7ffff, imm, 1'b0};
    end else begin
      get_imm_value_b = {19'b0, imm, 1'b0};
    end
  endfunction : get_imm_value_b

  function int get_imm_value_ci(logic[5:0] imm);
    if(imm[5] == 1) begin
      get_imm_value_ci = {26'h3ffffff, imm};
    end else begin
      get_imm_value_ci = {26'b0, imm};
    end
  endfunction : get_imm_value_ci

  function int get_imm_value_ci_lui(logic[17:12] imm);
    if(imm[17] == 1) begin
      get_imm_value_ci_lui = {14'h3fff, imm, 12'b0};
    end else begin
      get_imm_value_ci_lui = {14'b0, imm, 12'b0};
    end
  endfunction : get_imm_value_ci_lui

  function int get_imm_value_ci_addi16sp(logic[9:4] imm);
    if(imm[9] == 1) begin
      get_imm_value_ci_addi16sp = {22'h3fffff, imm, 4'b0};
    end else begin
      get_imm_value_ci_addi16sp = {22'b0, imm, 4'b0};
    end
  endfunction : get_imm_value_ci_addi16sp

  function int get_imm_value_cb(logic[8:1] imm);
    if(imm[8] == 1) begin
      get_imm_value_cb = {23'h7fffff, imm, 1'b0};
    end else begin
      get_imm_value_cb = {22'b0, imm, 1'b0};
    end
  endfunction : get_imm_value_cb

  function int get_imm_value_cj(logic[11:1] imm);
    if(imm[11] == 1) begin
      get_imm_value_cj = {20'hfffff, imm, 1'b0};
    end else begin
      get_imm_value_cj = {20'b0, imm, 1'b0};
    end
  endfunction : get_imm_value_cj

  // ---------------------------------------------------------------------------
  // HINT
  // ---------------------------------------------------------------------------
  typedef enum logic[7:0] {
    ADDI_H,
    FENCE_H,
    C_NOP_H,
    C_ADDI_H,
    C_LI_H,
    REG_IMM_I_H,
    REG_IMM_U_H,
    REG_REG_R_H,
    REG_REG_CR_H,
    CONST_GEN_CI_H,
    // Others
    UNKNOWN_HINT
  } hint_name_e;

  // Get the correspopnding name of the hint instruction
  function hint_name_e get_hint_name(instr_name_e name);
    hint_name_e hint_name;

    casex(name)
      SLTI, SLTIU, ANDI, ORI, XORI, SLLI, SRLI, SRAI:   hint_name = REG_IMM_I_H;

      ADD, SUB, AND, OR, XOR, SLL, SRL, SRA, SLT, SLTU: hint_name = REG_REG_R_H;

      C_LUI, C_SLLI: hint_name = CONST_GEN_CI_H;

      C_MV, C_ADD: hint_name = REG_REG_CR_H;

      LUI, AUIPC:hint_name = REG_IMM_U_H;

      ADDI: hint_name = ADDI_H;

      FENCE: hint_name = FENCE_H;

      C_NOP: hint_name = C_NOP_H;

      C_ADDI: hint_name = C_ADDI_H;

      C_LI: hint_name = C_LI_H;

    default : hint_name = UNKNOWN_HINT;
    endcase

    return hint_name;
  endfunction

  // Find out if the instruction is a HINT.
  function logic check_if_hint(instr_name_e name, instr_format_e format, instr_t instr);
    logic hint;

    casex (get_hint_name(name))
      ADDI_H:         hint = (instr.uncompressed.format.i.rd == X0 && (instr.uncompressed.format.i.rs1 != X0 || instr.uncompressed.format.i.imm != 12'b0));

      FENCE_H:        hint = ((instr.uncompressed.format.i.imm.funct7[27:25] == 3'b0 && instr.uncompressed.format.i.imm.shamt[24] == 1'b0) || instr.uncompressed.format.i.imm.shamt[23:20] == 4'b0);

      REG_IMM_I_H:    hint = (instr.uncompressed.format.i.rd == X0);

      REG_IMM_U_H:    hint = (instr.uncompressed.format.u.rd == X0);

      REG_REG_R_H:    hint = (instr.uncompressed.format.r.rd == X0);

      C_NOP_H:        hint = ((instr.compressed.format.ci.imm_12 != 1'b0 || instr.compressed.format.ci.imm_6_2 != 5'b0));

      C_ADDI_H:       hint = ((instr.compressed.format.ci.imm_12 == 1'b0 && instr.compressed.format.ci.imm_6_2 == 5'b0) && instr.compressed.format.ci.rd_rs1 != X0);

      C_LI_H:         hint = (instr.compressed.format.ci.rd_rs1 == X0);

      CONST_GEN_CI_H: hint = (instr.compressed.format.ci.rd_rs1 == X0 && (instr.compressed.format.ci.imm_12 != 1'b0 || instr.compressed.format.ci.imm_6_2 != 5'b0));

      REG_REG_CR_H:   hint = (instr.compressed.format.cr.rd_rs1 == X0 && instr.compressed.format.cr.rs2 != X0);

    default : hint = 0;
    endcase

    return hint;
  endfunction



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

    if(check_if_hint(name, format, instr)) begin
      asm.is_hint     = 1;
      return asm;
    end

    casex (format)
      I_TYPE: begin
        if (asm.instr inside { FENCEI, ECALL, EBREAK, MRET, DRET, WFI, WFE }) begin
          asm.rd.valid    = 0;
          asm.rs1.valid   = 0;
          asm.rs2.valid   = 0;
          asm.imm.valid   = 0;
        end else if (asm.instr inside { FENCE }) begin
          asm.imm.imm_raw         = instr.uncompressed.format.i.imm;
          asm.imm.imm_raw_sorted  = instr.uncompressed.format.i.imm;
          asm.imm.imm_type        = IMM;
          asm.imm.width           = 12;
          asm.imm.sign_ext        = 1;
          asm.imm.imm_value       = get_imm_value_i(instr.uncompressed.format.i.imm);
          asm.imm.valid           = 1;
        end else if (asm.instr inside { CSRRW, CSRRS, CSRRC }) begin
          asm.rd.gpr      = instr.uncompressed.format.i.rd.gpr;
          asm.rs1.gpr     = instr.uncompressed.format.i.rs1.gpr;
          asm.csr.address = instr.uncompressed.format.i.imm;
          asm.rd.valid    = 1;
          asm.rs1.valid   = 1;
          asm.csr.valid   = 1;
        end else if (asm.instr inside { CSRRWI, CSRRSI, CSRRCI }) begin
          asm.rd.gpr              = instr.uncompressed.format.i.rd.gpr;
          asm.imm.imm_raw         = instr.uncompressed.format.i.rs1;
          asm.imm.imm_raw_sorted  = instr.uncompressed.format.i.rs1;
          asm.imm.imm_type        = UIMM;
          asm.imm.width           = 5;
          asm.imm.imm_value       = instr.uncompressed.format.i.rs1;
          asm.csr.address         = instr.uncompressed.format.i.imm;
          asm.rd.valid            = 1;
          asm.imm.valid           = 1;
          asm.csr.valid           = 1;
        end else if (asm.instr inside { RORI, BEXTI, BCLRI, BINVI, BSETI, SLLI, SRLI, SRAI }) begin
          asm.rd.gpr              = instr.uncompressed.format.i.rd.gpr;
          asm.rs1.gpr             = instr.uncompressed.format.i.rs1.gpr;
          asm.imm.imm_raw         = instr.uncompressed.format.i.imm.shamt;
          asm.imm.imm_raw_sorted  = instr.uncompressed.format.i.imm.shamt;
          asm.imm.imm_type        = SHAMT;
          asm.imm.width           = 5;
          asm.imm.imm_value       = instr.uncompressed.format.i.imm.shamt;
          asm.rd.valid            = 1;
          asm.rs1.valid           = 1;
          asm.imm.valid           = 1;
        end else begin
          asm.rd.gpr              = instr.uncompressed.format.i.rd.gpr;
          asm.rs1.gpr             = instr.uncompressed.format.i.rs1.gpr;
          asm.imm.imm_raw         = instr.uncompressed.format.i.imm;
          asm.imm.imm_raw_sorted  = instr.uncompressed.format.i.imm;
          asm.imm.imm_type        = IMM;
          asm.imm.width           = 12;
          asm.imm.sign_ext        = 1;
          asm.imm.imm_value       = get_imm_value_i(instr.uncompressed.format.i.imm);
          asm.rd.valid            = 1;
          asm.rs1.valid           = 1;
          asm.imm.valid           = 1;
        end
      end
      J_TYPE: begin
        asm.rd.gpr              = instr.uncompressed.format.j.rd.gpr;
        asm.imm.imm_raw         = instr.uncompressed.format.j.imm;
        asm.imm.imm_raw_sorted  = get_sort_j_imm(instr);
        asm.imm.imm_type        = OFFSET;
        asm.imm.width           = 20;
        asm.imm.sign_ext        = 1;
        asm.imm.imm_value       = get_imm_value_j(get_sort_j_imm(instr));
        asm.rd.valid            = 1;
        asm.imm.valid           = 1;
      end
      S_TYPE: begin
        asm.rs1.gpr             = instr.uncompressed.format.s.rs1.gpr;
        asm.rs2.gpr             = instr.uncompressed.format.s.rs2.gpr;
        asm.imm.imm_raw         = get_sort_s_imm(instr);
        asm.imm.imm_raw_sorted  = get_sort_s_imm(instr);
        asm.imm.imm_type        = IMM;
        asm.imm.width           = 12;
        asm.imm.sign_ext        = 1;
        asm.imm.imm_value       = get_imm_value_i(get_sort_s_imm(instr));
        asm.rs1.valid           = 1;
        asm.rs2.valid           = 1;
        asm.imm.valid           = 1;
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
        asm.rs1.gpr             = instr.uncompressed.format.b.rs1.gpr;
        asm.rs2.gpr             = instr.uncompressed.format.b.rs2.gpr;
        asm.imm.imm_raw         = {instr.uncompressed.format.b.imm_h, instr.uncompressed.format.b.imm_l};
        asm.imm.imm_raw_sorted  = get_sort_b_imm(instr);
        asm.imm.imm_type        = IMM;
        asm.imm.width           = 12;
        asm.imm.sign_ext        = 1;
        asm.imm.imm_value       = get_imm_value_b(get_sort_b_imm(instr));
        asm.rs1.valid           = 1;
        asm.rs2.valid           = 1;
        asm.imm.valid           = 1;
      end
      U_TYPE: begin
        asm.rd.gpr              = instr.uncompressed.format.u.rd.gpr;
        asm.imm.imm_raw         = instr.uncompressed.format.u.imm;
        asm.imm.imm_raw_sorted  = instr.uncompressed.format.u.imm;
        asm.imm.imm_type        = IMM;
        asm.imm.width           = 20;
        asm.imm.imm_value       = { instr.uncompressed.format.u.imm, 12'b0000_0000_0000 };
        asm.rd.valid            = 1;
        asm.imm.valid           = 1;
      end
      // Compressed
      CR_TYPE: begin
        if (name inside { C_EBREAK }) begin
          asm.rd.valid  = 0;
          asm.rs1.valid = 0;
          asm.rs2.valid = 0;
          asm.rs3.valid = 0;
          asm.imm.valid = 0;
        end else if (name inside { C_MV }) begin
          asm.rd.gpr    = instr.compressed.format.cr.rd_rs1.gpr;
          asm.rs2.gpr   = instr.compressed.format.cr.rs2.gpr;
          asm.rd.valid  = 1;
          asm.rs2.valid = 1;
        end else if (name inside { C_ADD }) begin
          asm.rd.gpr    = instr.compressed.format.cr.rd_rs1.gpr;
          asm.rs1.gpr   = instr.compressed.format.cr.rd_rs1.gpr;
          asm.rs2.gpr   = instr.compressed.format.cr.rs2.gpr;
          asm.rd.valid  = 1;
          asm.rs1.valid = 1;
          asm.rs2.valid = 1;
        end else if (name inside { C_JR, C_JALR }) begin
          asm.rs1.gpr   = instr.compressed.format.cr.rd_rs1.gpr;
          asm.rs2.gpr   = instr.compressed.format.cr.rs2.gpr;
          asm.rs1.valid = 1;
          asm.rs2.valid = 1;
        end
      end
      CI_TYPE: begin
        if (name inside { C_LI, C_NOP, C_ADDI }) begin
          asm.rd.gpr              = instr.compressed.format.ci.rd_rs1.gpr;
          asm.imm.imm_raw         = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_raw_sorted  = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_type        = IMM;
          asm.imm.width           = 6;
          asm.imm.sign_ext        = 1;
          asm.imm.imm_value       = get_imm_value_ci({ instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 });
          asm.rd.valid            = 1;
          asm.imm.valid           = 1;
        end else if (name == C_LUI) begin
          asm.rd.gpr              = instr.compressed.format.ci.rd_rs1.gpr;
          asm.imm.imm_raw         = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_raw_sorted  = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_type        = NZIMM;
          asm.imm.width           = 6;
          asm.imm.sign_ext        = 1;
          asm.imm.imm_value       = get_imm_value_ci_lui({ instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 });
          asm.rd.valid            = 1;
          asm.imm.valid           = 1;
        end else if (name inside { C_LWSP }) begin
          asm.rd.gpr              = instr.compressed.format.ci.rd_rs1.gpr;
          asm.imm.imm_raw         = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_raw_sorted  = get_sort_ci_imm_lwsp(instr);
          asm.imm.imm_type        = OFFSET;
          asm.imm.width           = 6;
          asm.imm.imm_value       = {24'b0, get_sort_ci_imm_lwsp(instr), 2'b0};
          asm.rd.valid            = 1;
          asm.imm.valid           = 1;
        end else if (name inside { C_ADDI16SP }) begin
          asm.rs1.gpr             = instr.compressed.format.ci.rd_rs1.gpr;
          asm.rd.gpr              = instr.compressed.format.ci.rd_rs1.gpr;
          asm.imm.imm_raw         = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_raw_sorted  = get_sort_ci_imm_addi16sp(instr);
          asm.imm.imm_type        = NZIMM;
          asm.imm.width           = 6;
          asm.imm.sign_ext        = 1;
          asm.imm.imm_value       = get_imm_value_ci_addi16sp(get_sort_ci_imm_addi16sp(instr));
          asm.rs1.valid           = 1;
          asm.rd.valid            = 1;
          asm.imm.valid           = 1;
        end else if (name inside { C_SLLI }) begin
          asm.rs1.gpr             = instr.compressed.format.ci.rd_rs1.gpr;
          asm.rd.gpr              = instr.compressed.format.ci.rd_rs1.gpr;
          asm.imm.imm_raw         = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_raw_sorted  = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_type        = SHAMT;
          asm.imm.width           = 6;
          asm.imm.imm_value       = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.rs1.valid           = 1;
          asm.rd.valid            = 1;
          asm.imm.valid           = 1;
        end
      end
      CSS_TYPE: begin
        asm.rs2.gpr             = instr.compressed.format.css.rs2.gpr;
        asm.imm.imm_raw         = instr.compressed.format.css.imm;
        asm.imm.imm_raw_sorted  = { instr.compressed.format.css.imm[9:7], instr.compressed.format.css.imm[12:10] };
        asm.imm.imm_type        = OFFSET;
        asm.imm.width           = 6;
        asm.imm.imm_value       = { 24'b0, instr.compressed.format.css.imm[9:7], instr.compressed.format.css.imm[12:10], 2'b0 };
        asm.rs2.valid           = 1;
        asm.imm.valid           = 1;
      end
      CIW_TYPE: begin
        asm.rd.gpr              = instr.compressed.format.ciw.rd.gpr;
        asm.imm.imm_raw         = instr.compressed.format.ciw.imm;
        asm.imm.imm_raw_sorted  = get_sort_ciw_imm(instr);
        asm.imm.imm_type        = NZUIMM;
        asm.imm.width           = 8;
        asm.imm.imm_value       = { 22'b0, get_sort_ciw_imm(instr), 2'b0 };
        asm.imm.valid           = 1;
        asm.rd.valid            = 1;
      end
      CL_TYPE: begin
        asm.rd.gpr              = instr.compressed.format.cl.rd.gpr;
        asm.rs1.gpr             = instr.compressed.format.cl.rs1.gpr;
        asm.imm.imm_raw         = { instr.compressed.format.cl.imm_12_10, instr.compressed.format.cl.imm_6_5 };
        asm.imm.imm_raw_sorted  = get_sort_cl_imm(instr);
        asm.imm.imm_type        = OFFSET;
        asm.imm.width           = 5;
        asm.imm.imm_value       = { 25'b0, get_sort_cl_imm(instr), 2'b0 };
        asm.rd.valid            = 1;
        asm.rs1.valid           = 1;
        asm.imm.valid           = 1;
      end
      CS_TYPE: begin
        asm.rs2.gpr             = instr.compressed.format.cs.rs2.gpr;
        asm.rs1.gpr             = instr.compressed.format.cs.rs1.gpr;
        asm.imm.imm_raw         = { instr.compressed.format.cs.imm_12_10, instr.compressed.format.cs.imm_6_5 };
        asm.imm.imm_raw_sorted  = get_sort_cs_imm(instr);
        asm.imm.imm_type        = OFFSET;
        asm.imm.width           = 5;
        asm.imm.imm_value       = { 25'b0, get_sort_cs_imm(instr), 2'b0 };
        asm.rs2.valid           = 1;
        asm.rs1.valid           = 1;
        asm.imm.valid           = 1;
      end
      CA_TYPE: begin
        asm.rd.gpr    = instr.compressed.format.ca.rd_rs1.gpr;
        asm.rs1.gpr   = instr.compressed.format.ca.rd_rs1.gpr;
        asm.rs2.gpr   = instr.compressed.format.ca.rs2.gpr;
        asm.rd.valid  = 1;
        asm.rs1.valid = 1;
        asm.rs2.valid = 1;
      end
      CB_TYPE: begin
        if (name inside { C_SRLI, C_SRAI }) begin
          asm.rd.gpr              = instr.compressed.format.cb.rd_rs1.gpr;
          asm.rs1.gpr             = instr.compressed.format.cb.rd_rs1.gpr;
          asm.imm.imm_raw         = { instr.compressed.format.cb.offset_12_10[12], instr.compressed.format.cb.offset_6_2 };
          asm.imm.imm_raw_sorted  = { instr.compressed.format.cb.offset_12_10[12], instr.compressed.format.cb.offset_6_2 };
          asm.imm.imm_type        = SHAMT;
          asm.imm.width           = 6;
          asm.imm.imm_value       = { instr.compressed.format.cb.offset_12_10[12], instr.compressed.format.cb.offset_6_2 };
          asm.rd.valid            = 1;
          asm.rs1.valid           = 1;
          asm.imm.valid           = 1;
        end else if (name inside { C_BEQZ, C_BNEZ }) begin
          asm.rs1.gpr             = instr.compressed.format.cb.rd_rs1.gpr;
          asm.imm.imm_raw         = { instr.compressed.format.cb.offset_12_10, instr.compressed.format.cb.offset_6_2 };
          asm.imm.imm_raw_sorted  = get_sort_cb_imm_not_sequential(instr);
          asm.imm.imm_type        = OFFSET;
          asm.imm.width           = 8;
          asm.imm.sign_ext        = 1;
          asm.imm.imm_value       = get_imm_value_cb(get_sort_cb_imm_not_sequential(instr));
          asm.rs1.valid           = 1;
          asm.imm.valid           = 1;
        end
      end
      CJ_TYPE: begin
        asm.imm.imm_raw         = instr.compressed.format.cj.imm;
        asm.imm.imm_raw_sorted  = get_sort_cj_imm(instr);
        asm.imm.imm_type        = OFFSET;
        asm.imm.width           = 11;
        asm.imm.sign_ext        = 1;
        asm.imm.imm_value       = get_imm_value_cj(get_sort_cj_imm(instr));
        asm.imm.valid           = 1;
      end
      CLB_TYPE: begin
        asm.imm.imm_raw         = instr.compressed.format.clb.uimm;
        asm.imm.imm_raw_sorted  = { instr.compressed.format.clb.uimm[5], instr.compressed.format.clb.uimm[6] };
        asm.imm.imm_type        = UIMM;
        asm.imm.width           = 2;
        asm.imm.imm_value       = { instr.compressed.format.clb.uimm[5], instr.compressed.format.clb.uimm[6] };
        asm.rs1.gpr             = instr.compressed.format.clb.rs1.gpr;
        asm.rd.gpr              = instr.compressed.format.clb.rd.gpr;
        asm.rs1.valid           = 1;
        asm.rd.valid            = 1;
        asm.imm.valid           = 1;
      end
      CSB_TYPE: begin
        asm.imm.imm_raw         = instr.compressed.format.csb.uimm;
        asm.imm.imm_raw_sorted  = { instr.compressed.format.csb.uimm[5], instr.compressed.format.csb.uimm[6] };
        asm.imm.imm_type        = UIMM;
        asm.imm.width           = 2;
        asm.imm.imm_value       = { instr.compressed.format.csb.uimm[5], instr.compressed.format.csb.uimm[6] };
        asm.rs1.gpr             = instr.compressed.format.csb.rs1.gpr;
        asm.rs2.gpr             = instr.compressed.format.csb.rs2.gpr;
        asm.rs1.valid           = 1;
        asm.rs2.valid           = 1;
        asm.imm.valid           = 1;
      end
      CLH_TYPE: begin
        asm.imm.imm_raw         = instr.compressed.format.clh.uimm;
        asm.imm.imm_raw_sorted  = instr.compressed.format.clh.uimm;
        asm.imm.imm_type        = UIMM;
        asm.imm.width           = 1;
        asm.imm.imm_value       = { 30'b0, instr.compressed.format.clh.uimm };
        asm.rs1.gpr             = instr.compressed.format.clh.rs1.gpr;
        asm.rd.gpr              = instr.compressed.format.clh.rd.gpr;
        asm.rs1.valid           = 1;
        asm.rd.valid            = 1;
        asm.imm.valid           = 1;
      end
      CSH_TYPE: begin
        asm.imm.imm_raw         = instr.compressed.format.csh.uimm;
        asm.imm.imm_raw_sorted  = instr.compressed.format.csh.uimm;
        asm.imm.imm_type        = UIMM;
        asm.imm.width           = 1;
        asm.imm.imm_value       = {30'b0, instr.compressed.format.csh.uimm, 1'b0};
        asm.rs1.gpr             = instr.compressed.format.csh.rs1.gpr;
        asm.rs2.gpr             = instr.compressed.format.csh.rs2.gpr;
        asm.rs1.valid           = 1;
        asm.rs2.valid           = 1;
        asm.imm.valid           = 1;
      end
      CU_TYPE: begin
        asm.rs1.gpr = instr.compressed.format.cu.rd_rs1.gpr;
        asm.rd.gpr  = instr.compressed.format.cu.rd_rs1.gpr;
        asm.rs1.valid  = 1;
        asm.rd.valid   = 1;
      end
      CMMV_TYPE: begin
        asm.rs1.gpr = instr.compressed.format.cmmv.r1s.gpr;
        asm.rs2.gpr  = instr.compressed.format.cmmv.r2s.gpr;
        asm.rs1.valid  = 1;
        asm.rs2.valid   = 1;
      end
      CMJT_TYPE: begin
        asm.imm.imm_raw         = instr.compressed.format.cmjt.index;
        asm.imm.imm_raw_sorted  = instr.compressed.format.cmjt.index;
        asm.imm.imm_type        = INDEX;
        asm.imm.width           = 1;
        asm.imm.imm_value       = instr.compressed.format.cmjt.index;
        asm.imm.valid           = 1;
      end
      CMPP_TYPE: begin
        asm.imm.imm_raw         = instr.compressed.format.cmpp.spimm;
        asm.imm.imm_raw_sorted  = instr.compressed.format.cmpp.spimm;
        asm.imm.imm_type        = SPIMM;
        asm.imm.width           = 1;
        asm.rlist.rlist         = instr.compressed.format.cmpp.urlist;
        asm.stack_adj.stack_adj = get_stack_adj(instr.compressed.format.cmpp.urlist, instr.compressed.format.cmpp.spimm);
        asm.imm.valid           = 1;
        asm.rs1.gpr             = instr.compressed.format.csh.rs1.gpr;
        asm.rs2.gpr             = instr.compressed.format.csh.rs2.gpr;
        asm.rs1.valid           = 1;
        asm.rs2.valid           = 1;
        asm.rlist.valid         = 1;
        asm.stack_adj.valid     = 1;
      end

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
    case (1)

      (   (instr.uncompressed.opcode                     == MISC_MEM)
       && (instr.uncompressed.format.i.funct3            == 3'b0)) :
        asm = build_asm(FENCE, I_TYPE, instr);

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
        asm = build_asm(JALR, I_TYPE, instr);

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
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBA)) :
        asm = build_asm(SH1ADD, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SH2ADD)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBA)) :
        asm = build_asm(SH2ADD, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_SH3ADD)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBA)) :
        asm = build_asm(SH3ADD, R_TYPE, instr);

      //Zbb
      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MIN)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBB_MIN_MAX)) :
        asm = build_asm(MIN, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MINU)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBB_MIN_MAX)) :
        asm = build_asm(MINU, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MAX)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBB_MIN_MAX)) :
        asm = build_asm(MAX, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MAXU)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBB_MIN_MAX)) :
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
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBB_LOGICAL)) :
        asm = build_asm(ORN, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_C)
       && (instr.uncompressed.format.i.imm        == 12'b0110_0000_0000)) :
        asm = build_asm(CLZ, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_ANDN)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBB_LOGICAL)) :
        asm = build_asm(ANDN, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_ROL)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBB_ROTATE)) :
        asm = build_asm(ROL, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_ROR_RORI)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBB_ROTATE)) :
        asm = build_asm(ROR, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_ROR_RORI)
       && (instr.uncompressed.format.i.imm.funct7 == FUNCT7_ZBB_ROTATE )) :
        asm = build_asm(RORI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_XNOR)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBB_LOGICAL)) :
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
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBC)) :
        asm = build_asm(CLMUL, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_CLMULH)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBC)) :
        asm = build_asm(CLMULH, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_CLMULR)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBC)) :
        asm = build_asm(CLMULR, R_TYPE, instr);

      //Zbs
      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_BEXT_BEXTI)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBS_BCLR_BEXT)) :
        asm = build_asm(BEXT, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_BEXT_BEXTI)
       && (instr.uncompressed.format.i.imm.funct7 == FUNCT7_ZBS_BCLR_BEXT)) :
        asm = build_asm(BEXTI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_B_BI)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBS_BCLR_BEXT)) :
        asm = build_asm(BCLR, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_B_BI)
       && (instr.uncompressed.format.i.imm.funct7 == FUNCT7_ZBS_BCLR_BEXT)) :
        asm = build_asm(BCLRI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_B_BI)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBS_BINV)) :
        asm = build_asm(BINV, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_B_BI)
       && (instr.uncompressed.format.i.imm.funct7 == FUNCT7_ZBS_BINV)) :
        asm = build_asm(BINVI, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_B_BI)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_ZBS_BSET)) :
        asm = build_asm(BSET, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_B_BI)
       && (instr.uncompressed.format.i.imm.funct7 == FUNCT7_ZBS_BSET)) :
        asm = build_asm(BSETI, I_TYPE, instr);

      //M
      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MUL)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_M)) :
        asm = build_asm(MUL, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MULH)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_M)) :
        asm = build_asm(MULH, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MULHSU)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_M)) :
        asm = build_asm(MULHSU, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_MULHU)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_M)) :
        asm = build_asm(MULHU, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_DIV)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_M)) :
        asm = build_asm(DIV, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_DIVU)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_M)) :
        asm = build_asm(DIVU, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_REM)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_M)) :
        asm = build_asm(REM, R_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.r.funct3     == FUNCT3_REMU)
       && (instr.uncompressed.format.r.funct7     == FUNCT7_M)) :
        asm = build_asm(REMU, R_TYPE, instr);

      // Compressed
      (   (instr.compressed.opcode                        == C0)
       && (instr.compressed.format.ci.rd_rs1.gpr          == X0)
       && (instr.compressed.format.ci.imm_12              == 1'b0)
       && (instr.compressed.format.ci.imm_6_2             == 5'b0)
       && (instr.compressed.format.ci.funct3              == 3'b0)) :
        asm = build_asm(ILLEGAL_INSTR, CI_TYPE, instr);

      // Zca
      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cr.rd_rs1.gpr          == X0)
       && (instr.compressed.format.cr.rs2.gpr             == X0)
       && (instr.compressed.format.cr.funct4              == 4'b1001)) :
        asm = build_asm(C_EBREAK, CR_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cr.rs2.gpr             != X0)
       && (instr.compressed.format.cr.funct4              == 4'b1000)) :
        asm = build_asm(C_MV, CR_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cr.rs2.gpr             != X0)
       && (instr.compressed.format.cr.funct4              == 4'b1001)) :
        asm = build_asm(C_ADD, CR_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cr.rd_rs1.gpr          != X0)
       && (instr.compressed.format.cr.rs2.gpr             == X0)
       && (instr.compressed.format.cr.funct4              == 4'b1000)) :
        asm = build_asm(C_JR, CR_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cr.rd_rs1.gpr          != X0)
       && (instr.compressed.format.cr.rs2.gpr             == X0)
       && (instr.compressed.format.cr.funct4              == 4'b1001)) :
        asm = build_asm(C_JALR, CR_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.ci.rd_rs1.gpr          != X0)
       && (instr.compressed.format.ci.funct3              == FUNCT3_C_LWSP)) :
        asm = build_asm(C_LWSP, CI_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.ci.funct3              == FUNCT3_C_LI_LW)) :
        asm = build_asm(C_LI, CI_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.ci.rd_rs1.gpr          != X2)
       && (instr.compressed.format.ci.funct3              == FUNCT3_C_LUI)) :
        asm = build_asm(C_LUI, CI_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.ci.funct3              == FUNCT3_C_ADDI_NOP)) :
        asm = build_asm(C_ADDI, CI_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.ci.rd_rs1.gpr          == X2)
       && (instr.compressed.format.ci.funct3              == FUNCT3_C_ADDI16SP)) :
        asm = build_asm(C_ADDI16SP, CI_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.ci.funct3              == FUNCT3_C_SLLI)) :
        asm = build_asm(C_SLLI, CI_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.ci.rd_rs1.gpr          == X0)
       && (instr.compressed.format.ci.funct3              == FUNCT3_C_ADDI_NOP)) :
        asm = build_asm(C_NOP, CI_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.ca.funct2              == 2'b00)
       && (instr.compressed.format.ca.funct6              == 6'b100011)) :
        asm = build_asm(C_SUB, CA_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.ca.funct2              == 2'b01)
       && (instr.compressed.format.ca.funct6              == 6'b100011)) :
        asm = build_asm(C_XOR, CA_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.ca.funct2              == 2'b10)
       && (instr.compressed.format.ca.funct6              == 6'b100011)) :
        asm = build_asm(C_OR, CA_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.ca.funct2              == 2'b11)
       && (instr.compressed.format.ca.funct6              == 6'b100011)) :
        asm = build_asm(C_AND, CA_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cb.offset_12_10[12]    == 1'b0)
       && (instr.compressed.format.cb.offset_12_10[11:10] == 2'b00)
       && (instr.compressed.format.cb.funct3              == FUNCT3_C_SRLI_SRAI)) :
        asm = build_asm(C_SRLI, CB_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cb.offset_12_10[12]    == 1'b0)
       && (instr.compressed.format.cb.offset_12_10[11:10] == 2'b01)
       && (instr.compressed.format.cb.funct3              == FUNCT3_C_SRLI_SRAI)) :
        asm = build_asm(C_SRAI, CB_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cb.funct3              == FUNCT3_C_BEQZ)) :
        asm = build_asm(C_BEQZ, CB_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cb.funct3              == FUNCT3_C_BNEZ)) :
        asm = build_asm(C_BNEZ, CB_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cb.offset_12_10[11:10] == 2'b10)
       && (instr.compressed.format.cb.funct3              == FUNCT3_C_ANDI)) :
        asm = build_asm(C_ANDI, CB_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.css.funct3             == FUNCT3_C_SWSP)) :
        asm = build_asm(C_SWSP, CSS_TYPE, instr);

      (   (instr.compressed.opcode                        == C0)
       && (instr.compressed.format.ciw.imm                != X0)
       && (instr.compressed.format.ciw.funct3             == FUNCT3_C_ADDI4SPN)) :
        asm = build_asm(C_ADDI4SPN, CIW_TYPE, instr);

      (   (instr.compressed.opcode                        == C0)
       && (instr.compressed.format.cl.funct3              == FUNCT3_C_LI_LW)) :
        asm = build_asm(C_LW, CL_TYPE, instr);

      (   (instr.compressed.opcode                        == C0)
       && (instr.compressed.format.cs.funct3              == FUNCT3_C_SW)) :
        asm = build_asm(C_SW, CS_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cj.funct3              == FUNCT3_C_J)) :
        asm = build_asm(C_J, CJ_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cj.funct3              == FUNCT3_C_JAL)) :
        asm = build_asm(C_JAL, CJ_TYPE, instr);

      //Zcb

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cu.funct5              == FUNCT5_C_ZEXTB)
       && (instr.compressed.format.cu.funct6              == 6'b100111)) :
        asm = build_asm(C_ZEXTB, CU_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cu.funct5              == FUNCT5_C_SEXTB)
       && (instr.compressed.format.cu.funct6              == 6'b100111)) :
        asm = build_asm(C_SEXTB, CU_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cu.funct5              == FUNCT5_C_ZEXTH)
       && (instr.compressed.format.cu.funct6              == 6'b100111)) :
        asm = build_asm(C_ZEXTH, CU_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cu.funct5              == FUNCT5_C_SEXTH)
       && (instr.compressed.format.cu.funct6              == 6'b100111)) :
        asm = build_asm(C_SEXTH, CU_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cu.funct5              == FUNCT5_C_NOT)
       && (instr.compressed.format.cu.funct6              == 6'b100111)) :
        asm = build_asm(C_NOT, CU_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.ca.funct2              == 2'b10)
       && (instr.compressed.format.ca.funct6              == 6'b100111)) :
        asm = build_asm(C_MUL, CA_TYPE, instr);

      (   (instr.compressed.opcode                        == C0)
       && (instr.compressed.format.clb.funct6             == 6'b100000)) :
        asm = build_asm(C_LBU, CLB_TYPE, instr);

      (   (instr.compressed.opcode                        == C0)
       && (instr.compressed.format.clh.funct1             == 1'b0)
       && (instr.compressed.format.clh.funct6             == 6'b100001)) :
        asm = build_asm(C_LHU, CLH_TYPE, instr);

      (   (instr.compressed.opcode                        == C0)
       && (instr.compressed.format.clh.funct1             == 1'b1)
       && (instr.compressed.format.clh.funct6             == 6'b100001)) :
        asm = build_asm(C_LH, CLH_TYPE, instr);

      (   (instr.compressed.opcode                        == C0)
       && (instr.compressed.format.csb.funct6             == 6'b100010)) :
        asm = build_asm(C_SB, CSB_TYPE, instr);

      (   (instr.compressed.opcode                        == C0)
       && (instr.compressed.format.csh.funct1             == 1'b0)
       && (instr.compressed.format.csh.funct6             == 6'b100011)) :
        asm = build_asm(C_SH, CSH_TYPE, instr);


      //Zcmp
      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cmpp.funct2            == 2'b00)
       && (instr.compressed.format.cmpp.funct6            == 6'b101110)) :
        asm = build_asm(CM_PUSH, CMPP_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cmpp.funct2            == 2'b10)
       && (instr.compressed.format.cmpp.funct6            == 6'b101110)) :
        asm = build_asm(CM_POP, CMPP_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cmpp.funct2            == 2'b00)
       && (instr.compressed.format.cmpp.funct6            == 6'b101111)) :
        asm = build_asm(CM_POPRETZ, CMPP_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cmpp.funct2            == 2'b10)
       && (instr.compressed.format.cmpp.funct6            == 6'b101111)) :
        asm = build_asm(CM_POPRET, CMPP_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cmmv.funct2            == 2'b11)
       && (instr.compressed.format.cmmv.funct6            == 6'b101011)) :
        asm = build_asm(CM_MVA01S, CMMV_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cmmv.funct2            == 2'b01)
       && (instr.compressed.format.cmmv.funct6            == 6'b101011)) :
        asm = build_asm(CM_MVSA01, CMMV_TYPE, instr);

      //Zcmt
      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cmjt.index             < 32)
       && (instr.compressed.format.cmjt.funct6            == 6'b101000)) :
        asm = build_asm(CM_JT, CMJT_TYPE, instr);

      (   (instr.compressed.opcode                        == C2)
       && (instr.compressed.format.cmjt.index             >= 32)
       && (instr.compressed.format.cmjt.funct6            == 6'b101000)) :
        asm = build_asm(CM_JALT, CMJT_TYPE, instr);

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
        CSRRSI, CSRRCI: is_csr_write_spec_f = asm.imm.imm_value  ? 1'b1 : 1'b0;
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

