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

`define RV32F_INSTR_WITH_NO_FS3 \
 TB_INS_FMADD,TB_INS_FMSUB,TB_INS_FNMSUB,TB_INS_FNMADD

`define RV32_INSTR_WITH_NO_RS2 \
 TB_OPCODE_LUI,TB_OPCODE_AUIPC,TB_OPCODE_JAL,TB_OPCODE_JALR,TB_OPCODE_LOAD,TB_OPCODE_OPIMM,TB_OPCODE_FENCE,TB_OPCODE_SYSTEM

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
 wildcard bins fmvxs      =    {TB_INS_FMVXS}; \
 wildcard bins feqs       =    {TB_INS_FEQS}; \
 wildcard bins flts       =    {TB_INS_FLTS}; \
 wildcard bins fles       =    {TB_INS_FLES}; \
 wildcard bins fclass     =    {TB_INS_FCLASS}; \
 wildcard bins fcvtsw     =    {TB_INS_FCVTSW}; \
 wildcard bins fcvtswu    =    {TB_INS_FCVTSWU}; \
 wildcard bins fmvsw      =    {TB_INS_FMVSX}; \
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
 wildcard bins fmvxs      =    {TB_INS_FMVXS}; \
 wildcard bins feqs       =    {TB_INS_FEQS}; \
 wildcard bins flts       =    {TB_INS_FLTS}; \
 wildcard bins fles       =    {TB_INS_FLES}; \
 wildcard bins fclass     =    {TB_INS_FCLASS}; \
 wildcard bins fcvtsw     =    {TB_INS_FCVTSW}; \
 wildcard bins fcvtswu    =    {TB_INS_FCVTSWU}; \
 wildcard bins fmvsw      =    {TB_INS_FMVSX}; \
 wildcard bins fmadd      =    {TB_INS_FMADD}; \
 wildcard bins fmsub      =    {TB_INS_FMSUB}; \
 wildcard bins fnmsub     =    {TB_INS_FNMSUB}; \
 wildcard bins fnmadd     =    {TB_INS_FNMADD};

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
 bins apu_op_f2f        =    {APU_OP_F2F}; \
 bins apu_op_f2i        =    {APU_OP_F2I}; \
 bins apu_op_i2f        =    {APU_OP_I2F}; \
 bins apu_op_fmsub      =    {APU_OP_FMSUB}; \
 bins apu_op_fnmadd     =    {APU_OP_FNMADD}; \
 bins apu_op_fsub       =    {APU_OP_FSUB}; \
 bins apu_op_fsgnj_se   =    {APU_OP_FSGNJ_SE}; \
 bins apu_op_f2i_u      =    {APU_OP_F2I_U}; \
 bins apu_op_i2f_u      =    {APU_OP_I2F_U};

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


`endif // __UVME_CV32E40P_MACROS_SV__
