// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVME_CV32E40P_MACROS_SV__
`define __UVME_CV32E40P_MACROS_SV__


`define per_instance_fcov `ifndef DSIM option.per_instance = 1; `endif

`define UVME_CV32E40P_MEM_SIZE 22

`define COVIF_CB cntxt.cov_vif.mon_cb

`define APU_INSTR_WITH_NO_FD \
 APU_OP_FCMP, APU_OP_FCLASSIFY, APU_OP_F2I, APU_OP_F2I_U

 // LIST1 is CV32E40P_INSTR_OPCODE_BIT_6_0_BINS__NO_RV32C_FC_F
`define RV32_OPCODE_LIST1_WITH_RD \
  TB_OPCODE_OP, TB_OPCODE_OPIMM, TB_OPCODE_LOAD, TB_OPCODE_JALR, TB_OPCODE_JAL, TB_OPCODE_AUIPC, TB_OPCODE_LUI, \
  OPCODE_CUSTOM_0, OPCODE_CUSTOM_1, OPCODE_CUSTOM_2, OPCODE_CUSTOM_3

`define RV32_OPCODE_WITH_NO_RS2 \
  TB_OPCODE_LUI,TB_OPCODE_AUIPC,TB_OPCODE_JAL,TB_OPCODE_JALR,TB_OPCODE_LOAD,TB_OPCODE_OPIMM,TB_OPCODE_FENCE,TB_OPCODE_SYSTEM

`define RV32F_INSTR_WITH_FS1 \
  TB_INS_FMADD, TB_INS_FNMADD, TB_INS_FMSUB, TB_INS_FNMSUB, TB_INS_FADD, TB_INS_FSUB, TB_INS_FMUL, TB_INS_FDIV, TB_INS_FSQRT, \
  TB_INS_FSGNJS, TB_INS_FSGNJNS, TB_INS_FSGNJXS, TB_INS_FMIN, TB_INS_FMAX, TB_INS_FCVTWS, TB_INS_FCVTWUS, TB_INS_FMVXS, \
  TB_INS_FEQS, TB_INS_FLTS, TB_INS_FLES, TB_INS_FCLASS

`define RV32F_INSTR_WITH_FS2 \
  TB_INS_FMADD, TB_INS_FNMADD, TB_INS_FMSUB, TB_INS_FNMSUB, TB_INS_FADD, TB_INS_FSUB, TB_INS_FMUL, TB_INS_FDIV, \
  TB_INS_FSGNJS, TB_INS_FSGNJNS, TB_INS_FSGNJXS, TB_INS_FMIN, TB_INS_FMAX, \
  TB_INS_FEQS, TB_INS_FLTS, TB_INS_FLES

`define RV32F_INSTR_WITH_FS3 \
  TB_INS_FMADD, TB_INS_FNMADD, TB_INS_FMSUB, TB_INS_FNMSUB
  
`define RV32F_INSTR_WITH_RS1 \
  TB_INS_FLW, TB_INS_FSW, TB_INS_FMVSX, TB_INS_FCVTSW, TB_INS_FCVTSWU

// `define RV32ZFINX_INSTR_W_RS1 `RV32F_INSTR_WITH_FS1
`define RV32ZFINX_INSTR_W_RS2 `RV32F_INSTR_WITH_FS2
`define RV32ZFINX_INSTR_W_RS3 `RV32F_INSTR_WITH_FS3

`define RV32F_OP_WITHOUT_FDIV_FSQRT \
  APU_OP_FMADD, APU_OP_FNMSUB, APU_OP_FADD, APU_OP_FMUL, APU_OP_FSGNJ, APU_OP_FMINMAX, APU_OP_FCMP, \
  APU_OP_FCLASSIFY, APU_OP_F2I, APU_OP_I2F, APU_OP_FMSUB, APU_OP_FNMADD, APU_OP_FSUB, APU_OP_FSGNJ_SE, \
  APU_OP_F2I_U, APU_OP_I2F_U

`define RV32F_INSTR_BINS \
 wildcard bins fadd       =    {TB_INS_FADD}; \
 wildcard bins fsub       =    {TB_INS_FSUB}; \
 wildcard bins fmul       =    {TB_INS_FMUL}; \
 wildcard bins fdiv       =    {TB_INS_FDIV}; \
 wildcard bins fsqrt      =    {TB_INS_FSQRT}; \
 wildcard bins fsgnjs     =    {TB_INS_FSGNJS}; \
 wildcard bins fsgnjns    =    {TB_INS_FSGNJNS}; \
 wildcard bins fsgnjxs    =    {TB_INS_FSGNJXS}; \
 wildcard bins fmin       =    {TB_INS_FMIN}; \
 wildcard bins fmax       =    {TB_INS_FMAX}; \
 wildcard bins fcvtws     =    {TB_INS_FCVTWS}; \
 wildcard bins fcvtwus    =    {TB_INS_FCVTWUS}; \
 wildcard bins fmvxw      =    {TB_INS_FMVXS}; \
 wildcard bins feqs       =    {TB_INS_FEQS}; \
 wildcard bins flts       =    {TB_INS_FLTS}; \
 wildcard bins fles       =    {TB_INS_FLES}; \
 wildcard bins fclass     =    {TB_INS_FCLASS}; \
 wildcard bins fcvtsw     =    {TB_INS_FCVTSW}; \
 wildcard bins fcvtswu    =    {TB_INS_FCVTSWU}; \
 wildcard bins fmvwx      =    {TB_INS_FMVSX}; \
 wildcard bins fmadd      =    {TB_INS_FMADD}; \
 wildcard bins fmsub      =    {TB_INS_FMSUB}; \
 wildcard bins fnmsub     =    {TB_INS_FNMSUB}; \
 wildcard bins fnmadd     =    {TB_INS_FNMADD}; \
 wildcard bins flw        =    {TB_INS_FLW}; \
 wildcard bins fsw        =    {TB_INS_FSW};

`define ZFINX_INSTR_BINS \
 wildcard bins fadd       =    {TB_INS_FADD}; \
 wildcard bins fsub       =    {TB_INS_FSUB}; \
 wildcard bins fmul       =    {TB_INS_FMUL}; \
 wildcard bins fdiv       =    {TB_INS_FDIV}; \
 wildcard bins fsqrt      =    {TB_INS_FSQRT}; \
 wildcard bins fsgnjs     =    {TB_INS_FSGNJS}; \
 wildcard bins fsgnjns    =    {TB_INS_FSGNJNS}; \
 wildcard bins fsgnjxs    =    {TB_INS_FSGNJXS}; \
 wildcard bins fmin       =    {TB_INS_FMIN}; \
 wildcard bins fmax       =    {TB_INS_FMAX}; \
 wildcard bins fcvtws     =    {TB_INS_FCVTWS}; \
 wildcard bins fcvtwus    =    {TB_INS_FCVTWUS}; \
 wildcard bins feqs       =    {TB_INS_FEQS}; \
 wildcard bins flts       =    {TB_INS_FLTS}; \
 wildcard bins fles       =    {TB_INS_FLES}; \
 wildcard bins fclass     =    {TB_INS_FCLASS}; \
 wildcard bins fcvtsw     =    {TB_INS_FCVTSW}; \
 wildcard bins fcvtswu    =    {TB_INS_FCVTSWU}; \
 wildcard bins fmadd      =    {TB_INS_FMADD}; \
 wildcard bins fmsub      =    {TB_INS_FMSUB}; \
 wildcard bins fnmsub     =    {TB_INS_FNMSUB}; \
 wildcard bins fnmadd     =    {TB_INS_FNMADD};

`define JUMP_INSTR_BINS \
  wildcard bins jal     = {TB_INSTR_JAL}; \
  wildcard bins jalr    = {TB_INSTR_JALR};

`define BRANCH_INSTR_BINS \
  wildcard bins beq     = {TB_INSTR_BEQ}; \
  wildcard bins bne     = {TB_INSTR_BNE}; \
  wildcard bins blt     = {TB_INSTR_BLT}; \
  wildcard bins bge     = {TB_INSTR_BGE}; \
  wildcard bins bltu    = {TB_INSTR_BLTU}; \
  wildcard bins bgeu    = {TB_INSTR_BGEU};

`define OPIMM_INSTR_BINS \
  wildcard bins addi     = {TB_INSTR_ADDI}; \
  wildcard bins slti     = {TB_INSTR_SLTI}; \
  wildcard bins sltiu    = {TB_INSTR_SLTIU}; \
  wildcard bins xori     = {TB_INSTR_XORI}; \
  wildcard bins ori      = {TB_INSTR_ORI}; \
  wildcard bins andi     = {TB_INSTR_ANDI}; \
  wildcard bins slli     = {TB_INSTR_SLLI}; \
  wildcard bins srli     = {TB_INSTR_SRLI}; \
  wildcard bins srai     = {TB_INSTR_SRAI};

`define OP_INSTR_BINS \
  wildcard bins _add      = {TB_INSTR_ADD}; \
  wildcard bins _sub      = {TB_INSTR_SUB}; \
  wildcard bins _sll      = {TB_INSTR_SLL}; \
  wildcard bins _slt      = {TB_INSTR_SLT}; \
  wildcard bins _sltu     = {TB_INSTR_SLTU}; \
  wildcard bins _xor      = {TB_INSTR_XOR}; \
  wildcard bins _srl      = {TB_INSTR_SRL}; \
  wildcard bins _sra      = {TB_INSTR_SRA}; \
  wildcard bins _or       = {TB_INSTR_OR}; \
  wildcard bins _and      = {TB_INSTR_AND}; \

`define FENCE_INSTR_BINS \
  wildcard bins fence     = {TB_INSTR_FENCE}; \
  wildcard bins fencei    = {TB_INSTR_FENCEI};

`define RV32M_INSTR_BINS \
  wildcard bins div      = {TB_INSTR_DIV}; \
  wildcard bins divu     = {TB_INSTR_DIVU}; \
  wildcard bins rem      = {TB_INSTR_REM}; \
  wildcard bins remu     = {TB_INSTR_REMU}; \
  wildcard bins pmul     = {TB_INSTR_PMUL}; \
  wildcard bins pmuh     = {TB_INSTR_PMUH}; \
  wildcard bins pmulhsu  = {TB_INSTR_PMULHSU}; \
  wildcard bins pmulhu   = {TB_INSTR_PMULHU};

`define LOAD_STORE_INSTR_BINS \
  wildcard bins lb       = {TB_INSTR_LB}; \
  wildcard bins lh       = {TB_INSTR_LH}; \
  wildcard bins lw       = {TB_INSTR_LW}; \
  wildcard bins lbu      = {TB_INSTR_LBU}; \
  wildcard bins lhu      = {TB_INSTR_LHU}; \
  wildcard bins sb       = {TB_INSTR_SB}; \
  wildcard bins sh       = {TB_INSTR_SH}; \
  wildcard bins sw       = {TB_INSTR_SW};

`define RV32C_INSTR_BINS \
 wildcard bins c_lw       = {TB_INSTR_C_LW}; \
 wildcard bins c_flw      = {TB_INSTR_C_FLW}; \
 wildcard bins c_sw       = {TB_INSTR_C_SW}; \
 wildcard bins c_fsw      = {TB_INSTR_C_FSW}; \
 wildcard bins c_nop      = {TB_INSTR_C_NOP}; \
 wildcard bins c_jal      = {TB_INSTR_C_JAL}; \
 wildcard bins c_srli     = {TB_INSTR_C_SRLI}; \
 wildcard bins c_srai     = {TB_INSTR_C_SRAI}; \
 wildcard bins c_andi     = {TB_INSTR_C_ANDI}; \
 wildcard bins c_sub      = {TB_INSTR_C_SUB}; \
 wildcard bins c_xor      = {TB_INSTR_C_XOR}; \
 wildcard bins c_or       = {TB_INSTR_C_OR}; \
 wildcard bins c_and      = {TB_INSTR_C_AND}; \
 wildcard bins c_j        = {TB_INSTR_C_J}; \
 wildcard bins c_beqz     = {TB_INSTR_C_BEQZ}; \
 wildcard bins c_bnez     = {TB_INSTR_C_BNEZ}; \
 wildcard bins c_flwsp    = {TB_INSTR_C_FLWSP}; \
 wildcard bins c_ebreak   = {TB_INSTR_C_EBREAK}; \
 wildcard bins c_swsp     = {TB_INSTR_C_SWSP}; \
 wildcard bins c_fswsp    = {TB_INSTR_C_FSWSP}; \
 wildcard bins c_addi4spn = {TB_USER_DEF_C_ADDI4SPN}; \
 wildcard bins c_addi     = {TB_USER_DEF_C_ADDI}; \
 wildcard bins c_li       = {TB_USER_DEF_C_LI}; \
 wildcard bins c_addi16sp = {TB_USER_DEF_C_ADDI16SP}; \
 wildcard bins c_lui      = {TB_USER_DEF_C_LUI}; \
 wildcard bins c_slli     = {TB_USER_DEF_C_SLLI}; \
 wildcard bins c_lwsp     = {TB_USER_DEF_C_LWSP}; \
 wildcard bins c_jr       = {TB_USER_DEF_C_JR}; \
 wildcard bins c_mv       = {TB_USER_DEF_C_MV}; \
 wildcard bins c_jalr     = {TB_USER_DEF_C_JALR}; \
 wildcard bins c_add      = {TB_USER_DEF_C_ADD};

`define FPU_OP_BINS \
 bins apu_op_fmadd      =    {APU_OP_FMADD}; \
 bins apu_op_fnmsub     =    {APU_OP_FNMSUB}; \
 bins apu_op_fadd       =    {APU_OP_FADD}; \
 bins apu_op_fmul       =    {APU_OP_FMUL}; \
 bins apu_op_fdiv       =    {APU_OP_FDIV}; \
 bins apu_op_fsqrt      =    {APU_OP_FSQRT}; \
 bins apu_op_fsgnj      =    {APU_OP_FSGNJ}; \
 bins apu_op_fminmax    =    {APU_OP_FMINMAX}; \
 bins apu_op_fcmp       =    {APU_OP_FCMP}; \
 bins apu_op_fclassify  =    {APU_OP_FCLASSIFY}; \
 bins apu_op_f2i        =    {APU_OP_F2I}; \
 bins apu_op_i2f        =    {APU_OP_I2F}; \
 bins apu_op_fmsub      =    {APU_OP_FMSUB}; \
 bins apu_op_fnmadd     =    {APU_OP_FNMADD}; \
 bins apu_op_fsub       =    {APU_OP_FSUB}; \
 bins apu_op_fsgnj_se   =    {APU_OP_FSGNJ_SE}; \
 bins apu_op_f2i_u      =    {APU_OP_F2I_U}; \
 bins apu_op_i2f_u      =    {APU_OP_I2F_U};
 // bins apu_op_f2f        =    {APU_OP_F2F}; \ exclude this from above macro because it is for RV32D

`define ZFINX_OP_BINS \
 bins apu_op_fmadd      =    {APU_OP_FMADD}; \
 bins apu_op_fnmsub     =    {APU_OP_FNMSUB}; \
 bins apu_op_fadd       =    {APU_OP_FADD}; \
 bins apu_op_fmul       =    {APU_OP_FMUL}; \
 bins apu_op_fdiv       =    {APU_OP_FDIV}; \
 bins apu_op_fsqrt      =    {APU_OP_FSQRT}; \
 bins apu_op_fsgnj      =    {APU_OP_FSGNJ}; \
 bins apu_op_fminmax    =    {APU_OP_FMINMAX}; \
 bins apu_op_fcmp       =    {APU_OP_FCMP}; \
 bins apu_op_fclassify  =    {APU_OP_FCLASSIFY}; \
 bins apu_op_f2i        =    {APU_OP_F2I}; \
 bins apu_op_i2f        =    {APU_OP_I2F}; \
 bins apu_op_fmsub      =    {APU_OP_FMSUB}; \
 bins apu_op_fnmadd     =    {APU_OP_FNMADD}; \
 bins apu_op_fsub       =    {APU_OP_FSUB}; \
 bins apu_op_f2i_u      =    {APU_OP_F2I_U}; \
 bins apu_op_i2f_u      =    {APU_OP_I2F_U};
 // bins apu_op_fsgnj_se   =    {APU_OP_FSGNJ_SE}; \ exclude this from macro because it is fmv for RV32F
 // bins apu_op_f2f        =    {APU_OP_F2F};      \ exclude this from above macro because it is for RV32D

// cv32e40p opcode (exclude compress and f-compress)
`define CV32E40P_INSTR_OPCODE_BIT_6_0_BINS__NO_RV32C_FC \
 bins system_opcode          =    {TB_OPCODE_SYSTEM}; \
 bins fence_opcode           =    {TB_OPCODE_FENCE}; \
 bins op_opcode              =    {TB_OPCODE_OP}; \
 bins opimm_opcode           =    {TB_OPCODE_OPIMM}; \
 bins store_opcode           =    {TB_OPCODE_STORE}; \
 bins load_opcode            =    {TB_OPCODE_LOAD}; \
 bins branch_opcode          =    {TB_OPCODE_BRANCH}; \
 bins jalr_opcode            =    {TB_OPCODE_JALR}; \
 bins jal_opcode             =    {TB_OPCODE_JAL}; \
 bins auipc_opcode           =    {TB_OPCODE_AUIPC}; \
 bins lui_opcode             =    {TB_OPCODE_LUI}; \
 bins fpu_fp_opcode          =    {TB_OPCODE_OP_FP}; \
 bins fpu_fmadd_opcode       =    {TB_OPCODE_OP_FMADD}; \
 bins fpu_fnmadd_opcode      =    {TB_OPCODE_OP_FNMADD}; \
 bins fpu_fmsub_opcode       =    {TB_OPCODE_OP_FMSUB}; \
 bins fpu_fnmsub_opcode      =    {TB_OPCODE_OP_FNMSUB}; \
 bins fpu_str_opcode         =    {TB_OPCODE_STORE_FP}; \
 bins fpu_ld_opcode          =    {TB_OPCODE_LOAD_FP}; \
 bins xpulp_custom_0         =    {OPCODE_CUSTOM_0}; \
 bins xpulp_custom_1         =    {OPCODE_CUSTOM_1}; \
 bins xpulp_custom_2         =    {OPCODE_CUSTOM_2}; \
 bins xpulp_custom_3         =    {OPCODE_CUSTOM_3};

// cv32e40p opcode (exclude compress, f-compress, f-load/store)
`define CV32E40P_INSTR_OPCODE_BIT_6_0_BINS__NO_RV32C_FC_FPLS \
 bins system_opcode          =    {TB_OPCODE_SYSTEM}; \
 bins fence_opcode           =    {TB_OPCODE_FENCE}; \
 bins op_opcode              =    {TB_OPCODE_OP}; \
 bins opimm_opcode           =    {TB_OPCODE_OPIMM}; \
 bins store_opcode           =    {TB_OPCODE_STORE}; \
 bins load_opcode            =    {TB_OPCODE_LOAD}; \
 bins branch_opcode          =    {TB_OPCODE_BRANCH}; \
 bins jalr_opcode            =    {TB_OPCODE_JALR}; \
 bins jal_opcode             =    {TB_OPCODE_JAL}; \
 bins auipc_opcode           =    {TB_OPCODE_AUIPC}; \
 bins lui_opcode             =    {TB_OPCODE_LUI}; \
 bins fpu_fp_opcode          =    {TB_OPCODE_OP_FP}; \
 bins fpu_fmadd_opcode       =    {TB_OPCODE_OP_FMADD}; \
 bins fpu_fnmadd_opcode      =    {TB_OPCODE_OP_FNMADD}; \
 bins fpu_fmsub_opcode       =    {TB_OPCODE_OP_FMSUB}; \
 bins fpu_fnmsub_opcode      =    {TB_OPCODE_OP_FNMSUB}; \
 bins xpulp_custom_0         =    {OPCODE_CUSTOM_0}; \
 bins xpulp_custom_1         =    {OPCODE_CUSTOM_1}; \
 bins xpulp_custom_2         =    {OPCODE_CUSTOM_2}; \
 bins xpulp_custom_3         =    {OPCODE_CUSTOM_3};

// cv32e40p opcode (exclude compress, f-compress and f)
`define CV32E40P_INSTR_OPCODE_BIT_6_0_BINS__NO_RV32C_FC_F \
 bins system_opcode          =    {TB_OPCODE_SYSTEM}; \
 bins fence_opcode           =    {TB_OPCODE_FENCE}; \
 bins op_opcode              =    {TB_OPCODE_OP}; \
 bins opimm_opcode           =    {TB_OPCODE_OPIMM}; \
 bins store_opcode           =    {TB_OPCODE_STORE}; \
 bins load_opcode            =    {TB_OPCODE_LOAD}; \
 bins branch_opcode          =    {TB_OPCODE_BRANCH}; \
 bins jalr_opcode            =    {TB_OPCODE_JALR}; \
 bins jal_opcode             =    {TB_OPCODE_JAL}; \
 bins auipc_opcode           =    {TB_OPCODE_AUIPC}; \
 bins lui_opcode             =    {TB_OPCODE_LUI}; \
 bins xpulp_custom_0         =    {OPCODE_CUSTOM_0}; \
 bins xpulp_custom_1         =    {OPCODE_CUSTOM_1}; \
 bins xpulp_custom_2         =    {OPCODE_CUSTOM_2}; \
 bins xpulp_custom_3         =    {OPCODE_CUSTOM_3};

`define RV32X_PULP_INSTR_BINS \
 wildcard bins cv_lb_pi_ri          =    {INSTR_CV_LB_PI_RI}; \
 wildcard bins cv_lh_pi_ri          =    {INSTR_CV_LH_PI_RI}; \
 wildcard bins cv_lw_pi_ri          =    {INSTR_CV_LW_PI_RI}; \
 wildcard bins cv_elw_pi_ri         =    {INSTR_CV_ELW_PI_RI}; \
 wildcard bins cv_lbu_pi_ri         =    {INSTR_CV_LBU_PI_RI}; \
 wildcard bins cv_lhu_pi_ri         =    {INSTR_CV_LHU_PI_RI}; \
 wildcard bins cv_beqimm            =    {INSTR_CV_BEQIMM}; \
 wildcard bins cv_bneimm            =    {INSTR_CV_BNEIMM}; \
 wildcard bins cv_lb_pi_rr          =    {INSTR_CV_LB_PI_RR}; \
 wildcard bins cv_lh_pi_rr          =    {INSTR_CV_LH_PI_RR}; \
 wildcard bins cv_lw_pi_rr          =    {INSTR_CV_LW_PI_RR}; \
 wildcard bins cv_lbu_pi_rr         =    {INSTR_CV_LBU_PI_RR}; \
 wildcard bins cv_lhu_pi_rr         =    {INSTR_CV_LHU_PI_RR}; \
 wildcard bins cv_lb_rr             =    {INSTR_CV_LB_RR}; \
 wildcard bins cv_lh_rr             =    {INSTR_CV_LH_RR}; \
 wildcard bins cv_lw_rr             =    {INSTR_CV_LW_RR}; \
 wildcard bins cv_lbu_rr            =    {INSTR_CV_LBU_RR}; \
 wildcard bins cv_lhu_rr            =    {INSTR_CV_LHU_RR}; \
 wildcard bins cv_sb_pi_ri          =    {INSTR_CV_SB_PI_RI}; \
 wildcard bins cv_sh_pi_ri          =    {INSTR_CV_SH_PI_RI}; \
 wildcard bins cv_sw_pi_ri          =    {INSTR_CV_SW_PI_RI}; \
 wildcard bins cv_sb_pi_rr          =    {INSTR_CV_SB_PI_RR}; \
 wildcard bins cv_sh_pi_rr          =    {INSTR_CV_SH_PI_RR}; \
 wildcard bins cv_sw_pi_rr          =    {INSTR_CV_SW_PI_RR}; \
 wildcard bins cv_sb_rr             =    {INSTR_CV_SB_RR}; \
 wildcard bins cv_sh_rr             =    {INSTR_CV_SH_RR}; \
 wildcard bins cv_sw_rr             =    {INSTR_CV_SW_RR}; \
 wildcard bins cv_starti0           =    {INSTR_CV_STARTI_0}; \
 wildcard bins cv_start0            =    {INSTR_CV_START_0}; \
 wildcard bins cv_endi0             =    {INSTR_CV_ENDI_0}; \
 wildcard bins cv_end0              =    {INSTR_CV_END_0}; \
 wildcard bins cv_counti0           =    {INSTR_CV_COUNTI_0}; \
 wildcard bins cv_count0            =    {INSTR_CV_COUNT_0}; \
 wildcard bins cv_setupi0           =    {INSTR_CV_SETUPI_0}; \
 wildcard bins cv_setup0            =    {INSTR_CV_SETUP_0}; \
 wildcard bins cv_starti1           =    {INSTR_CV_STARTI_1}; \
 wildcard bins cv_start1            =    {INSTR_CV_START_1}; \
 wildcard bins cv_endi1             =    {INSTR_CV_ENDI_1}; \
 wildcard bins cv_end1              =    {INSTR_CV_END_1}; \
 wildcard bins cv_counti1           =    {INSTR_CV_COUNTI_1}; \
 wildcard bins cv_count1            =    {INSTR_CV_COUNT_1}; \
 wildcard bins cv_setupi1           =    {INSTR_CV_SETUPI_1}; \
 wildcard bins cv_setup1            =    {INSTR_CV_SETUP_1}; \
 wildcard bins cv_extractr          =    {INSTR_CV_EXTRACTR}; \
 wildcard bins cv_extractur         =    {INSTR_CV_EXTRACTUR}; \
 wildcard bins cv_insertr           =    {INSTR_CV_INSERTR}; \
 wildcard bins cv_bclrr             =    {INSTR_CV_BCLRR}; \
 wildcard bins cv_bsetr             =    {INSTR_CV_BSETR}; \
 wildcard bins cv_ror               =    {INSTR_CV_ROR}; \
 wildcard bins cv_ff1               =    {INSTR_CV_FF1}; \
 wildcard bins cv_fl1               =    {INSTR_CV_FL1}; \
 wildcard bins cv_clb               =    {INSTR_CV_CLB}; \
 wildcard bins cv_cnt               =    {INSTR_CV_CNT}; \
 wildcard bins cv_abs               =    {INSTR_CV_ABS}; \
 wildcard bins cv_sle               =    {INSTR_CV_SLE}; \
 wildcard bins cv_sleu              =    {INSTR_CV_SLEU}; \
 wildcard bins cv_min               =    {INSTR_CV_MIN}; \
 wildcard bins cv_minu              =    {INSTR_CV_MINU}; \
 wildcard bins cv_max               =    {INSTR_CV_MAX}; \
 wildcard bins cv_maxu              =    {INSTR_CV_MAXU}; \
 wildcard bins cv_exths             =    {INSTR_CV_EXTHS}; \
 wildcard bins cv_exthz             =    {INSTR_CV_EXTHZ}; \
 wildcard bins cv_extbs             =    {INSTR_CV_EXTBS}; \
 wildcard bins cv_extbz             =    {INSTR_CV_EXTBZ}; \
 wildcard bins cv_clip              =    {INSTR_CV_CLIP}; \
 wildcard bins cv_clipu             =    {INSTR_CV_CLIPU}; \
 wildcard bins cv_clipr             =    {INSTR_CV_CLIPR}; \
 wildcard bins cv_clipur            =    {INSTR_CV_CLIPUR}; \
 wildcard bins cv_addnr             =    {INSTR_CV_ADDNR}; \
 wildcard bins cv_addunr            =    {INSTR_CV_ADDUNR}; \
 wildcard bins cv_addrnr            =    {INSTR_CV_ADDRNR}; \
 wildcard bins cv_addurnr           =    {INSTR_CV_ADDURNR}; \
 wildcard bins cv_subnr             =    {INSTR_CV_SUBNR}; \
 wildcard bins cv_subunr            =    {INSTR_CV_SUBUNR}; \
 wildcard bins cv_subrnr            =    {INSTR_CV_SUBRNR}; \
 wildcard bins cv_suburnr           =    {INSTR_CV_SUBURNR}; \
 wildcard bins cv_mac               =    {INSTR_CV_MAC}; \
 wildcard bins cv_msu               =    {INSTR_CV_MSU}; \
 wildcard bins cv_extract           =    {INSTR_CV_EXTRACT}; \
 wildcard bins cv_extractu          =    {INSTR_CV_EXTRACTU}; \
 wildcard bins cv_insert            =    {INSTR_CV_INSERT}; \
 wildcard bins cv_bclr              =    {INSTR_CV_BCLR}; \
 wildcard bins cv_bset              =    {INSTR_CV_BSET}; \
 wildcard bins cv_bitrev            =    {INSTR_CV_BITREV}; \
 wildcard bins cv_addn              =    {INSTR_CV_ADDN}; \
 wildcard bins cv_addun             =    {INSTR_CV_ADDUN}; \
 wildcard bins cv_addrn             =    {INSTR_CV_ADDRN}; \
 wildcard bins cv_addurn            =    {INSTR_CV_ADDURN}; \
 wildcard bins cv_subn              =    {INSTR_CV_SUBN}; \
 wildcard bins cv_subun             =    {INSTR_CV_SUBUN}; \
 wildcard bins cv_subrn             =    {INSTR_CV_SUBRN}; \
 wildcard bins cv_suburn            =    {INSTR_CV_SUBURN}; \
 wildcard bins cv_mulsn             =    {INSTR_CV_MULSN}; \
 wildcard bins cv_mulhhsn           =    {INSTR_CV_MULHHSN}; \
 wildcard bins cv_mulsrn            =    {INSTR_CV_MULSRN}; \
 wildcard bins cv_mulhhsrn          =    {INSTR_CV_MULHHSRN}; \
 wildcard bins cv_mulun             =    {INSTR_CV_MULUN}; \
 wildcard bins cv_mulhhun           =    {INSTR_CV_MULHHUN}; \
 wildcard bins cv_mulurn            =    {INSTR_CV_MULURN}; \
 wildcard bins cv_mulhhurn          =    {INSTR_CV_MULHHURN}; \
 wildcard bins cv_macsn             =    {INSTR_CV_MACSN}; \
 wildcard bins cv_machhsn           =    {INSTR_CV_MACHHSN}; \
 wildcard bins cv_macsrn            =    {INSTR_CV_MACSRN}; \
 wildcard bins cv_machhsrn          =    {INSTR_CV_MACHHSRN}; \
 wildcard bins cv_macun             =    {INSTR_CV_MACUN}; \
 wildcard bins cv_machhun           =    {INSTR_CV_MACHHUN}; \
 wildcard bins cv_macurn            =    {INSTR_CV_MACURN}; \
 wildcard bins cv_machhurn          =    {INSTR_CV_MACHHURN}; \
 wildcard bins cv_add_h             =    {INSTR_CV_ADD_H}; \
 wildcard bins cv_add_sc_h          =    {INSTR_CV_ADD_SC_H}; \
 wildcard bins cv_add_sci_h         =    {INSTR_CV_ADD_SCI_H}; \
 wildcard bins cv_add_b             =    {INSTR_CV_ADD_B}; \
 wildcard bins cv_add_sc_b          =    {INSTR_CV_ADD_SC_B}; \
 wildcard bins cv_add_sci_b         =    {INSTR_CV_ADD_SCI_B}; \
 wildcard bins cv_sub_h             =    {INSTR_CV_SUB_H}; \
 wildcard bins cv_sub_sc_h          =    {INSTR_CV_SUB_SC_H}; \
 wildcard bins cv_sub_sci_h         =    {INSTR_CV_SUB_SCI_H}; \
 wildcard bins cv_sub_b             =    {INSTR_CV_SUB_B}; \
 wildcard bins cv_sub_sc_b          =    {INSTR_CV_SUB_SC_B}; \
 wildcard bins cv_sub_sci_b         =    {INSTR_CV_SUB_SCI_B}; \
 wildcard bins cv_avg_h             =    {INSTR_CV_AVG_H}; \
 wildcard bins cv_avg_sc_h          =    {INSTR_CV_AVG_SC_H}; \
 wildcard bins cv_avg_sci_h         =    {INSTR_CV_AVG_SCI_H}; \
 wildcard bins cv_avg_b             =    {INSTR_CV_AVG_B}; \
 wildcard bins cv_avg_sc_b          =    {INSTR_CV_AVG_SC_B}; \
 wildcard bins cv_avg_sci_b         =    {INSTR_CV_AVG_SCI_B}; \
 wildcard bins cv_avgu_h            =    {INSTR_CV_AVGU_H}; \
 wildcard bins cv_avgu_sc_h         =    {INSTR_CV_AVGU_SC_H}; \
 wildcard bins cv_avgu_sci_h        =    {INSTR_CV_AVGU_SCI_H}; \
 wildcard bins cv_avgu_b            =    {INSTR_CV_AVGU_B}; \
 wildcard bins cv_avgu_sc_b         =    {INSTR_CV_AVGU_SC_B}; \
 wildcard bins cv_avgu_sci_b        =    {INSTR_CV_AVGU_SCI_B}; \
 wildcard bins cv_min_h             =    {INSTR_CV_MIN_H}; \
 wildcard bins cv_min_sc_h          =    {INSTR_CV_MIN_SC_H}; \
 wildcard bins cv_min_sci_h         =    {INSTR_CV_MIN_SCI_H}; \
 wildcard bins cv_min_b             =    {INSTR_CV_MIN_B}; \
 wildcard bins cv_min_sc_b          =    {INSTR_CV_MIN_SC_B}; \
 wildcard bins cv_min_sci_b         =    {INSTR_CV_MIN_SCI_B}; \
 wildcard bins cv_minu_h            =    {INSTR_CV_MINU_H}; \
 wildcard bins cv_minu_sc_h         =    {INSTR_CV_MINU_SC_H}; \
 wildcard bins cv_minu_sci_h        =    {INSTR_CV_MINU_SCI_H}; \
 wildcard bins cv_minu_b            =    {INSTR_CV_MINU_B}; \
 wildcard bins cv_minu_sc_b         =    {INSTR_CV_MINU_SC_B}; \
 wildcard bins cv_minu_sci_b        =    {INSTR_CV_MINU_SCI_B}; \
 wildcard bins cv_max_h             =    {INSTR_CV_MAX_H}; \
 wildcard bins cv_max_sc_h          =    {INSTR_CV_MAX_SC_H}; \
 wildcard bins cv_max_sci_h         =    {INSTR_CV_MAX_SCI_H}; \
 wildcard bins cv_max_b             =    {INSTR_CV_MAX_B}; \
 wildcard bins cv_max_sc_b          =    {INSTR_CV_MAX_SC_B}; \
 wildcard bins cv_max_sci_b         =    {INSTR_CV_MAX_SCI_B}; \
 wildcard bins cv_maxu_h            =    {INSTR_CV_MAXU_H}; \
 wildcard bins cv_maxu_sc_h         =    {INSTR_CV_MAXU_SC_H}; \
 wildcard bins cv_maxu_sci_h        =    {INSTR_CV_MAXU_SCI_H}; \
 wildcard bins cv_maxu_b            =    {INSTR_CV_MAXU_B}; \
 wildcard bins cv_maxu_sc_b         =    {INSTR_CV_MAXU_SC_B}; \
 wildcard bins cv_maxu_sci_b        =    {INSTR_CV_MAXU_SCI_B}; \
 wildcard bins cv_srl_h             =    {INSTR_CV_SRL_H}; \
 wildcard bins cv_srl_sc_h          =    {INSTR_CV_SRL_SC_H}; \
 wildcard bins cv_srl_sci_h         =    {INSTR_CV_SRL_SCI_H}; \
 wildcard bins cv_srl_b             =    {INSTR_CV_SRL_B}; \
 wildcard bins cv_srl_sc_b          =    {INSTR_CV_SRL_SC_B}; \
 wildcard bins cv_srl_sci_b         =    {INSTR_CV_SRL_SCI_B}; \
 wildcard bins cv_sra_h             =    {INSTR_CV_SRA_H}; \
 wildcard bins cv_sra_sc_h          =    {INSTR_CV_SRA_SC_H}; \
 wildcard bins cv_sra_sci_h         =    {INSTR_CV_SRA_SCI_H}; \
 wildcard bins cv_sra_b             =    {INSTR_CV_SRA_B}; \
 wildcard bins cv_sra_sc_b          =    {INSTR_CV_SRA_SC_B}; \
 wildcard bins cv_sra_sci_b         =    {INSTR_CV_SRA_SCI_B}; \
 wildcard bins cv_sll_h             =    {INSTR_CV_SLL_H}; \
 wildcard bins cv_sll_sc_h          =    {INSTR_CV_SLL_SC_H}; \
 wildcard bins cv_sll_sci_h         =    {INSTR_CV_SLL_SCI_H}; \
 wildcard bins cv_sll_b             =    {INSTR_CV_SLL_B}; \
 wildcard bins cv_sll_sc_b          =    {INSTR_CV_SLL_SC_B}; \
 wildcard bins cv_sll_sci_b         =    {INSTR_CV_SLL_SCI_B}; \
 wildcard bins cv_or_h              =    {INSTR_CV_OR_H}; \
 wildcard bins cv_or_sc_h           =    {INSTR_CV_OR_SC_H}; \
 wildcard bins cv_or_sci_h          =    {INSTR_CV_OR_SCI_H}; \
 wildcard bins cv_or_b              =    {INSTR_CV_OR_B}; \
 wildcard bins cv_or_sc_b           =    {INSTR_CV_OR_SC_B}; \
 wildcard bins cv_or_sci_b          =    {INSTR_CV_OR_SCI_B}; \
 wildcard bins cv_xor_h             =    {INSTR_CV_XOR_H}; \
 wildcard bins cv_xor_sc_h          =    {INSTR_CV_XOR_SC_H}; \
 wildcard bins cv_xor_sci_h         =    {INSTR_CV_XOR_SCI_H}; \
 wildcard bins cv_xor_b             =    {INSTR_CV_XOR_B}; \
 wildcard bins cv_xor_sc_b          =    {INSTR_CV_XOR_SC_B}; \
 wildcard bins cv_xor_sci_b         =    {INSTR_CV_XOR_SCI_B}; \
 wildcard bins cv_and_h             =    {INSTR_CV_AND_H}; \
 wildcard bins cv_and_sc_h          =    {INSTR_CV_AND_SC_H}; \
 wildcard bins cv_and_sci_h         =    {INSTR_CV_AND_SCI_H}; \
 wildcard bins cv_and_b             =    {INSTR_CV_AND_B}; \
 wildcard bins cv_and_sc_b          =    {INSTR_CV_AND_SC_B}; \
 wildcard bins cv_and_sci_b         =    {INSTR_CV_AND_SCI_B}; \
 wildcard bins cv_abs_h             =    {INSTR_CV_ABS_H}; \
 wildcard bins cv_abs_b             =    {INSTR_CV_ABS_B}; \
 wildcard bins cv_dotup_h           =    {INSTR_CV_DOTUP_H}; \
 wildcard bins cv_dotup_sc_h        =    {INSTR_CV_DOTUP_SC_H}; \
 wildcard bins cv_dotup_sci_h       =    {INSTR_CV_DOTUP_SCI_H}; \
 wildcard bins cv_dotup_b           =    {INSTR_CV_DOTUP_B}; \
 wildcard bins cv_dotup_sc_b        =    {INSTR_CV_DOTUP_SC_B}; \
 wildcard bins cv_dotup_sci_b       =    {INSTR_CV_DOTUP_SCI_B}; \
 wildcard bins cv_dotusp_h          =    {INSTR_CV_DOTUSP_H}; \
 wildcard bins cv_dotusp_sc_h       =    {INSTR_CV_DOTUSP_SC_H}; \
 wildcard bins cv_dotusp_sci_h      =    {INSTR_CV_DOTUSP_SCI_H}; \
 wildcard bins cv_dotusp_b          =    {INSTR_CV_DOTUSP_B}; \
 wildcard bins cv_dotusp_sc_b       =    {INSTR_CV_DOTUSP_SC_B}; \
 wildcard bins cv_dotusp_sci_b      =    {INSTR_CV_DOTUSP_SCI_B}; \
 wildcard bins cv_dotsp_h           =    {INSTR_CV_DOTSP_H}; \
 wildcard bins cv_dotsp_sc_h        =    {INSTR_CV_DOTSP_SC_H}; \
 wildcard bins cv_dotsp_sci_h       =    {INSTR_CV_DOTSP_SCI_H}; \
 wildcard bins cv_dotsp_b           =    {INSTR_CV_DOTSP_B}; \
 wildcard bins cv_dotsp_sc_b        =    {INSTR_CV_DOTSP_SC_B}; \
 wildcard bins cv_dotsp_sci_b       =    {INSTR_CV_DOTSP_SCI_B}; \
 wildcard bins cv_sdotup_h          =    {INSTR_CV_SDOTUP_H}; \
 wildcard bins cv_sdotup_sc_h       =    {INSTR_CV_SDOTUP_SC_H}; \
 wildcard bins cv_sdotup_sci_h      =    {INSTR_CV_SDOTUP_SCI_H}; \
 wildcard bins cv_sdotup_b          =    {INSTR_CV_SDOTUP_B}; \
 wildcard bins cv_sdotup_sc_b       =    {INSTR_CV_SDOTUP_SC_B}; \
 wildcard bins cv_sdotup_sci_b      =    {INSTR_CV_SDOTUP_SCI_B}; \
 wildcard bins cv_sdotusp_h         =    {INSTR_CV_SDOTUSP_H}; \
 wildcard bins cv_sdotusp_sc_h      =    {INSTR_CV_SDOTUSP_SC_H}; \
 wildcard bins cv_sdotusp_sci_h     =    {INSTR_CV_SDOTUSP_SCI_H}; \
 wildcard bins cv_sdotusp_b         =    {INSTR_CV_SDOTUSP_B}; \
 wildcard bins cv_sdotusp_sc_b      =    {INSTR_CV_SDOTUSP_SC_B}; \
 wildcard bins cv_sdotusp_sci_b     =    {INSTR_CV_SDOTUSP_SCI_B}; \
 wildcard bins cv_sdotsp_h          =    {INSTR_CV_SDOTSP_H}; \
 wildcard bins cv_sdotsp_sc_h       =    {INSTR_CV_SDOTSP_SC_H}; \
 wildcard bins cv_sdotsp_sci_h      =    {INSTR_CV_SDOTSP_SCI_H}; \
 wildcard bins cv_sdotsp_b          =    {INSTR_CV_SDOTSP_B}; \
 wildcard bins cv_sdotsp_sc_b       =    {INSTR_CV_SDOTSP_SC_B}; \
 wildcard bins cv_sdotsp_sci_b      =    {INSTR_CV_SDOTSP_SCI_B}; \
 wildcard bins cv_extract_h         =    {INSTR_CV_EXTRACT_H}; \
 wildcard bins cv_extract_b         =    {INSTR_CV_EXTRACT_B}; \
 wildcard bins cv_extractu_h        =    {INSTR_CV_EXTRACTU_H}; \
 wildcard bins cv_extractu_b        =    {INSTR_CV_EXTRACTU_B}; \
 wildcard bins cv_insert_h          =    {INSTR_CV_INSERT_H}; \
 wildcard bins cv_insert_b          =    {INSTR_CV_INSERT_B}; \
 wildcard bins cv_shuffle_h         =    {INSTR_CV_SHUFFLE_H}; \
 wildcard bins cv_shuffle_sci_h     =    {INSTR_CV_SHUFFLE_SCI_H}; \
 wildcard bins cv_shuffle_b         =    {INSTR_CV_SHUFFLE_B}; \
 wildcard bins cv_shufflei0_sci_b   =    {INSTR_CV_SHUFFLEI0_SCI_B}; \
 wildcard bins cv_shufflei1_sci_b   =    {INSTR_CV_SHUFFLEI1_SCI_B}; \
 wildcard bins cv_shufflei2_sci_b   =    {INSTR_CV_SHUFFLEI2_SCI_B}; \
 wildcard bins cv_shufflei3_sci_b   =    {INSTR_CV_SHUFFLEI3_SCI_B}; \
 wildcard bins cv_shuffle2_h        =    {INSTR_CV_SHUFFLE2_H}; \
 wildcard bins cv_shuffle2_b        =    {INSTR_CV_SHUFFLE2_B}; \
 wildcard bins cv_pack              =    {INSTR_CV_PACK}; \
 wildcard bins cv_pack_h            =    {INSTR_CV_PACK_H}; \
 wildcard bins cv_packhi_b          =    {INSTR_CV_PACKHI_B}; \
 wildcard bins cv_packlo_b          =    {INSTR_CV_PACKLO_B}; \
 wildcard bins cv_cmpeq_h           =    {INSTR_CV_CMPEQ_H}; \
 wildcard bins cv_cmpeq_sc_h        =    {INSTR_CV_CMPEQ_SC_H}; \
 wildcard bins cv_cmpeq_sci_h       =    {INSTR_CV_CMPEQ_SCI_H}; \
 wildcard bins cv_cmpeq_b           =    {INSTR_CV_CMPEQ_B}; \
 wildcard bins cv_cmpeq_sc_b        =    {INSTR_CV_CMPEQ_SC_B}; \
 wildcard bins cv_cmpeq_sci_b       =    {INSTR_CV_CMPEQ_SCI_B}; \
 wildcard bins cv_cmpne_h           =    {INSTR_CV_CMPNE_H}; \
 wildcard bins cv_cmpne_sc_h        =    {INSTR_CV_CMPNE_SC_H}; \
 wildcard bins cv_cmpne_sci_h       =    {INSTR_CV_CMPNE_SCI_H}; \
 wildcard bins cv_cmpne_b           =    {INSTR_CV_CMPNE_B}; \
 wildcard bins cv_cmpne_sc_b        =    {INSTR_CV_CMPNE_SC_B}; \
 wildcard bins cv_cmpne_sci_b       =    {INSTR_CV_CMPNE_SCI_B}; \
 wildcard bins cv_cmpgt_h           =    {INSTR_CV_CMPGT_H}; \
 wildcard bins cv_cmpgt_sc_h        =    {INSTR_CV_CMPGT_SC_H}; \
 wildcard bins cv_cmpgt_sci_h       =    {INSTR_CV_CMPGT_SCI_H}; \
 wildcard bins cv_cmpgt_b           =    {INSTR_CV_CMPGT_B}; \
 wildcard bins cv_cmpgt_sc_b        =    {INSTR_CV_CMPGT_SC_B}; \
 wildcard bins cv_cmpgt_sci_b       =    {INSTR_CV_CMPGT_SCI_B}; \
 wildcard bins cv_cmpge_h           =    {INSTR_CV_CMPGE_H}; \
 wildcard bins cv_cmpge_sc_h        =    {INSTR_CV_CMPGE_SC_H}; \
 wildcard bins cv_cmpge_sci_h       =    {INSTR_CV_CMPGE_SCI_H}; \
 wildcard bins cv_cmpge_b           =    {INSTR_CV_CMPGE_B}; \
 wildcard bins cv_cmpge_sc_b        =    {INSTR_CV_CMPGE_SC_B}; \
 wildcard bins cv_cmpge_sci_b       =    {INSTR_CV_CMPGE_SCI_B}; \
 wildcard bins cv_cmplt_h           =    {INSTR_CV_CMPLT_H}; \
 wildcard bins cv_cmplt_sc_h        =    {INSTR_CV_CMPLT_SC_H}; \
 wildcard bins cv_cmplt_sci_h       =    {INSTR_CV_CMPLT_SCI_H}; \
 wildcard bins cv_cmplt_b           =    {INSTR_CV_CMPLT_B}; \
 wildcard bins cv_cmplt_sc_b        =    {INSTR_CV_CMPLT_SC_B}; \
 wildcard bins cv_cmplt_sci_b       =    {INSTR_CV_CMPLT_SCI_B}; \
 wildcard bins cv_cmple_h           =    {INSTR_CV_CMPLE_H}; \
 wildcard bins cv_cmple_sc_h        =    {INSTR_CV_CMPLE_SC_H}; \
 wildcard bins cv_cmple_sci_h       =    {INSTR_CV_CMPLE_SCI_H}; \
 wildcard bins cv_cmple_b           =    {INSTR_CV_CMPLE_B}; \
 wildcard bins cv_cmple_sc_b        =    {INSTR_CV_CMPLE_SC_B}; \
 wildcard bins cv_cmple_sci_b       =    {INSTR_CV_CMPLE_SCI_B}; \
 wildcard bins cv_cmpgtu_h          =    {INSTR_CV_CMPGTU_H}; \
 wildcard bins cv_cmpgtu_sc_h       =    {INSTR_CV_CMPGTU_SC_H}; \
 wildcard bins cv_cmpgtu_sci_h      =    {INSTR_CV_CMPGTU_SCI_H}; \
 wildcard bins cv_cmpgtu_b          =    {INSTR_CV_CMPGTU_B}; \
 wildcard bins cv_cmpgtu_sc_b       =    {INSTR_CV_CMPGTU_SC_B}; \
 wildcard bins cv_cmpgtu_sci_b      =    {INSTR_CV_CMPGTU_SCI_B}; \
 wildcard bins cv_cmpgeu_h          =    {INSTR_CV_CMPGEU_H}; \
 wildcard bins cv_cmpgeu_sc_h       =    {INSTR_CV_CMPGEU_SC_H}; \
 wildcard bins cv_cmpgeu_sci_h      =    {INSTR_CV_CMPGEU_SCI_H}; \
 wildcard bins cv_cmpgeu_b          =    {INSTR_CV_CMPGEU_B}; \
 wildcard bins cv_cmpgeu_sc_b       =    {INSTR_CV_CMPGEU_SC_B}; \
 wildcard bins cv_cmpgeu_sci_b      =    {INSTR_CV_CMPGEU_SCI_B}; \
 wildcard bins cv_cmpltu_h          =    {INSTR_CV_CMPLTU_H}; \
 wildcard bins cv_cmpltu_sc_h       =    {INSTR_CV_CMPLTU_SC_H}; \
 wildcard bins cv_cmpltu_sci_h      =    {INSTR_CV_CMPLTU_SCI_H}; \
 wildcard bins cv_cmpltu_b          =    {INSTR_CV_CMPLTU_B}; \
 wildcard bins cv_cmpltu_sc_b       =    {INSTR_CV_CMPLTU_SC_B}; \
 wildcard bins cv_cmpltu_sci_b      =    {INSTR_CV_CMPLTU_SCI_B}; \
 wildcard bins cv_cmpleu_h          =    {INSTR_CV_CMPLEU_H}; \
 wildcard bins cv_cmpleu_sc_h       =    {INSTR_CV_CMPLEU_SC_H}; \
 wildcard bins cv_cmpleu_sci_h      =    {INSTR_CV_CMPLEU_SCI_H}; \
 wildcard bins cv_cmpleu_b          =    {INSTR_CV_CMPLEU_B}; \
 wildcard bins cv_cmpleu_sc_b       =    {INSTR_CV_CMPLEU_SC_B}; \
 wildcard bins cv_cmpleu_sci_b      =    {INSTR_CV_CMPLEU_SCI_B}; \
 wildcard bins cv_cplxmul_r         =    {INSTR_CV_CPLXMUL_R}; \
 wildcard bins cv_cplxmul_r_div2    =    {INSTR_CV_CPLXMUL_R_DIV2}; \
 wildcard bins cv_cplxmul_r_div4    =    {INSTR_CV_CPLXMUL_R_DIV4}; \
 wildcard bins cv_cplxmul_r_div8    =    {INSTR_CV_CPLXMUL_R_DIV8}; \
 wildcard bins cv_cplxmul_i         =    {INSTR_CV_CPLXMUL_I}; \
 wildcard bins cv_cplxmul_i_div2    =    {INSTR_CV_CPLXMUL_I_DIV2}; \
 wildcard bins cv_cplxmul_i_div4    =    {INSTR_CV_CPLXMUL_I_DIV4}; \
 wildcard bins cv_cplxmul_i_div8    =    {INSTR_CV_CPLXMUL_I_DIV8}; \
 wildcard bins cv_cplxconj          =    {INSTR_CV_CPLXCONJ}; \
 wildcard bins cv_subrotmj          =    {INSTR_CV_SUBROTMJ}; \
 wildcard bins cv_subrotmj_div2     =    {INSTR_CV_SUBROTMJ_DIV2}; \
 wildcard bins cv_subrotmj_div4     =    {INSTR_CV_SUBROTMJ_DIV4}; \
 wildcard bins cv_subrotmj_div8     =    {INSTR_CV_SUBROTMJ_DIV8}; \
 wildcard bins cv_add_div2          =    {INSTR_CV_ADD_DIV2}; \
 wildcard bins cv_add_div4          =    {INSTR_CV_ADD_DIV4}; \
 wildcard bins cv_add_div8          =    {INSTR_CV_ADD_DIV8}; \
 wildcard bins cv_sub_div2          =    {INSTR_CV_SUB_DIV2}; \
 wildcard bins cv_sub_div4          =    {INSTR_CV_SUB_DIV4}; \
 wildcard bins cv_sub_div8          =    {INSTR_CV_SUB_DIV8};

`endif // __UVME_CV32E40P_MACROS_SV__
