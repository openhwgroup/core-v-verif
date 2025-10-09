// Copyright (C) 2022 Thales DIS Design Services SAS
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
//
// Original Author: Zbigniew CHAMSKI <zbigniew.chamski@thalesgroup.com>

#ifndef _RISCV_CVXIF_H
#define _RISCV_CVXIF_H

#include "extension.h"

// R-type instruction format
struct cvxif_r_insn_t
{
  unsigned opcode : 7;
  unsigned rd : 5;
  unsigned funct3 : 3;
  unsigned rs1 : 5;
  unsigned rs2 : 5;
  unsigned funct7 : 7;
};

// R4-type instruction format
struct cvxif_r4_insn_t
{
  unsigned opcode : 7;
  unsigned rd : 5;
  unsigned funct3 : 3;
  unsigned rs1 : 5;
  unsigned rs2 : 5;
  unsigned funct2 : 2;
  unsigned rs3 : 5;
};

// I-type instruction format
struct cvxif_i_insn_t
{
  unsigned opcode : 7;
  unsigned rd : 5;
  unsigned funct3 : 3;
  unsigned rs1 : 5;
  unsigned imm : 12;
};

// S-type instruction format
struct cvxif_s_insn_t
{
  unsigned opcode : 7;
  unsigned imm_low : 5;
  unsigned funct3 : 3;
  unsigned rs1 : 5;
  unsigned rs2 : 5;
  unsigned imm_high : 7;
};

// CR (compressed R-type) instruction format
struct cvxif_cr_insn_t
{
  unsigned opcode: 2;
  unsigned rs2: 5;
  unsigned rd_rs1: 5;
  unsigned funct4: 4;
  unsigned ignored: 16;
};

union cvxif_insn_t
{
  cvxif_r_insn_t r_type;
  cvxif_r4_insn_t r4_type;
  cvxif_i_insn_t i_type;
  cvxif_s_insn_t s_type;
  cvxif_cr_insn_t cr_type;
  insn_t i;
};

enum Cop { C0 = 0, C1, C2, NOT_COMPRESSED };
enum Func2 {FUNC2_0 = 0};
enum Func3 {FUNC3_0 = 0, FUNC3_1, FUNC3_2, FUNC3_3};
enum Func4 {FUNC4_CNOP = 0xe, FUNC4_CADD = 0xf };
enum Func7 {CUS_ADD = 0, CUS_DOUBLE_RS1 = 1, CUS_DOUBLE_RS2 = 2, CUS_ADD_MULTI = 3, CUS_ADD_RS3_RTYPE = 4};
enum CustomOpcode {
  CUS_ADD_RS3_MADDRTYPE = 0x43,
  CUS_ADD_RS3_MSUB = 0x47,
  CUS_ADD_RS3_NMADD = 0x4f,
  CUS_ADD_RS3_NMSUB = 0x4b,
};

class cvxif_extn_t : public extension_t
{
 public:
  virtual bool do_writeback_p(insn_t insn);
  virtual reg_t custom0(insn_t insn);
  virtual reg_t custom1(insn_t insn);
  virtual reg_t custom2(insn_t insn);
  virtual reg_t custom3(insn_t insn);
  virtual reg_t cvxif_cus_add_rs3_madd(insn_t insn) = 0;
  virtual reg_t cvxif_cus_add_rs3_msub(insn_t insn) = 0;
  virtual reg_t cvxif_cus_add_rs3_nmadd(insn_t insn) = 0;
  virtual reg_t cvxif_cus_add_rs3_nmsub(insn_t insn) = 0;
  virtual reg_t cvxif_cus_add_rs3_rtype(insn_t insn) = 0;
  virtual reg_t cvxif_cus_cnop(insn_t insn) = 0;
  virtual reg_t cvxif_cus_cadd(insn_t insn) = 0;
  std::vector<insn_desc_t> get_instructions();
  std::vector<disasm_insn_t*> get_disasms();
};

#endif
