/*
 * Copyright 2023 Dolphin Design
 * SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// This file contains all the macro defines that used in cv32e40p_float_instr_lib.sv

  // constraint for special pattern operands
  // note: DONOT insert " solve enable_special_operand_patterns before operand_``IDX``_pattern;\" at below code, it will limit the constraints (havent root caused)
  `define C_OPERAND_PATTERN(IDX) \
    constraint c_operand_``IDX``_pattern {\
      soft operand_``IDX``_pattern.size() == num_of_instr_per_stream;\
      foreach (operand_``IDX``_pattern[i]) {\
        if (enable_special_operand_patterns) {\
          soft operand_``IDX``_pattern[i] dist { IS_RAND := 8, IS_Q_NAN  := 4, IS_S_NAN              := 4, \
                                                 IS_POSITIVE_ZERO        := 4, IS_NEGATIVE_ZERO      := 4, \
                                                 IS_POSITIVE_INFINITY    := 4, IS_NEGATIVE_INFINITY  := 4, \
                                                 IS_POSITIVE_MAX         := 2, IS_NEGATIVE_MAX       := 2, \
                                                 IS_POSITIVE_MIN         := 2, IS_NEGATIVE_MIN       := 2, \
                                                 IS_POSITIVE_SUBNORMAL   := 4, IS_NEGATIVE_SUBNORMAL := 4 };\
        } else {\
          soft operand_``IDX``_pattern[i] == IS_RAND;\
        }\
      }\
    } 

  `define C_OPERAND(IDX) \
    constraint c_operand_``IDX {\
      sign_``IDX``.size()     == num_of_instr_per_stream;\
      exp_``IDX``.size()      == num_of_instr_per_stream;\
      mantissa_``IDX``.size() == num_of_instr_per_stream;\
      operand_``IDX``.size()  == num_of_instr_per_stream;\
      foreach (operand_``IDX``[i]) {\
        if (operand_``IDX``_pattern[i] == IS_POSITIVE_ZERO) {\
          sign_``IDX``[i] == 1'b0; exp_``IDX``[i] == 8'h00; mantissa_``IDX``[i] == 23'h0;\
        }\
        if (operand_``IDX``_pattern[i] == IS_NEGATIVE_ZERO) {\
          sign_``IDX``[i] == 1'b1; exp_``IDX``[i] == 8'h00; mantissa_``IDX``[i] == 23'h0;\
        }\
        if (operand_``IDX``_pattern[i] == IS_POSITIVE_INFINITY) {\
          sign_``IDX``[i] == 1'b0; exp_``IDX``[i] == 8'hFF; mantissa_``IDX``[i] == 23'h0;\
        }\
        if (operand_``IDX``_pattern[i] == IS_NEGATIVE_INFINITY) {\
          sign_``IDX``[i] == 1'b1; exp_``IDX``[i] == 8'hFF; mantissa_``IDX``[i] == 23'h0;\
        }\
        if (operand_``IDX``_pattern[i] == IS_POSITIVE_MAX) {\
          sign_``IDX``[i] == 1'b0; exp_``IDX``[i] == 8'hFE; mantissa_``IDX``[i][22:0] == 23'h7FFFFF;\
        }\
        if (operand_``IDX``_pattern[i] == IS_NEGATIVE_MAX) {\
          sign_``IDX``[i] == 1'b1; exp_``IDX``[i] == 8'hFE; mantissa_``IDX``[i][22:0] == 23'h7FFFFF;\
        }\
        if (operand_``IDX``_pattern[i] == IS_POSITIVE_MIN) {\
          sign_``IDX``[i] == 1'b0; exp_``IDX``[i] == 8'h00; mantissa_``IDX``[i][22:0] == 23'h1;\
        }\
        if (operand_``IDX``_pattern[i] == IS_NEGATIVE_MIN) {\
          sign_``IDX``[i] == 1'b1; exp_``IDX``[i] == 8'h00; mantissa_``IDX``[i][22:0] == 23'h1;\
        }\
        if (operand_``IDX``_pattern[i] == IS_POSITIVE_SUBNORMAL) {\
          sign_``IDX``[i] == 1'b0; exp_``IDX``[i] == 8'h00; mantissa_``IDX``[i][22:0] != 0;\
        }\
        if (operand_``IDX``_pattern[i] == IS_NEGATIVE_SUBNORMAL) {\
          sign_``IDX``[i] == 1'b1; exp_``IDX``[i] == 8'h00; mantissa_``IDX``[i][22:0] != 0;\
        }\
        if (operand_``IDX``_pattern[i] == IS_Q_NAN) {\
          sign_``IDX``[i] == 1'b1; exp_``IDX``[i] == 8'hFF; mantissa_``IDX``[i][22] == 1'b1;\
        }\
        if (operand_``IDX``_pattern[i] == IS_S_NAN) {\
          sign_``IDX``[i] == 1'b1; exp_``IDX``[i] == 8'hFF; mantissa_``IDX``[i][22] == 1'b0; mantissa_``IDX``[i][21:0] != 0;\
        }\
        operand_``IDX[i] == {sign_``IDX``[i], exp_``IDX``[i], mantissa_``IDX``[i]};\
        solve operand_``IDX``_pattern[i] before sign_``IDX``[i];\
        solve sign_``IDX``[i] before operand_``IDX[i];\
        solve exp_``IDX``[i] before operand_``IDX[i];\
        solve mantissa_``IDX``[i] before operand_``IDX[i];\
      }\
    }

  // Overhead instruction to set fpr with specific value
  `define SET_FPR_VALUE(FRD,IMM) \
    begin\
      riscv_instr                 m_instr;\
      riscv_pseudo_instr          p_instr;\
      riscv_floating_point_instr  f_instr;\
      p_instr = riscv_pseudo_instr::type_id::create("p_instr");\
      `DV_CHECK_RANDOMIZE_WITH_FATAL(p_instr,\
        pseudo_instr_name == LI;\
        rd  == T2;\
      );\
      p_instr.imm = ``IMM``;\
      p_instr.update_imm_str();\
      instr_list.push_back(p_instr);\
      m_instr = new riscv_instr::get_rand_instr(.include_instr({FMV_W_X}));\
      `DV_CHECK_FATAL($cast(f_instr, m_instr), "Cast to instr_f failed!");\
      override_instr(\
        .f_instr  (f_instr),\
        .fd       (``FRD``),\
        .rs1      (T2)\
      );\
      instr_list.push_back(f_instr);\
      instr_list[$].comment = {instr_list[$].comment, $sformatf(`" [SET REG TO 32'h%8h] `", ``IMM``)};\
    end

  // Overhead instructions to override fp instr operands with specific operand patterns
  `define MANIPULATE_FPR_OPERANDS(FPR,OPERAND) \
    if (instr.has_``FPR && ``OPERAND``_pattern != IS_RAND) begin\
      riscv_instr                 m_instr;\
      riscv_pseudo_instr          p_instr;\
      riscv_floating_point_instr  f_instr;\
      p_instr = riscv_pseudo_instr::type_id::create("p_instr");\
      `DV_CHECK_RANDOMIZE_WITH_FATAL(p_instr,\
        pseudo_instr_name == LI;\
        rd  == local::imm_rd;\
      );\
      p_instr.imm = ``OPERAND``;\
      p_instr.update_imm_str();\
      instr_list.push_back(p_instr);\
      instr_list[$].comment = {instr_list[$].comment, $sformatf(`" [``OPERAND`` - %s - 32'h%8h] `", ``OPERAND``_pattern.name(), ``OPERAND``)};\
      m_instr = new riscv_instr::get_rand_instr(.include_instr({FMV_W_X}));\
      `DV_CHECK_FATAL($cast(f_instr, m_instr), "Cast to instr_f failed!");\
      override_instr(\
        .f_instr  (f_instr),\
        .fd       (instr.``FPR``),\
        .rs1      (imm_rd)\
      );\
      instr_list.push_back(f_instr);\
      instr_list[$].comment = {instr_list[$].comment, $sformatf(`" [``OPERAND`` - %s] `", ``OPERAND``_pattern.name())};\
    end

  // Overhead instruction to set gpr with specific value
  `define SET_GPR_VALUE(RD,IMM) \
    begin\
      riscv_pseudo_instr          p_instr;\
      p_instr = riscv_pseudo_instr::type_id::create("p_instr");\
      `DV_CHECK_RANDOMIZE_WITH_FATAL(p_instr,\
        pseudo_instr_name == LI;\
        rd  == ``RD``;\
      );\
      p_instr.imm = ``IMM``;\
      p_instr.update_imm_str();\
      instr_list.push_back(p_instr);\
      instr_list[$].comment = {instr_list[$].comment, $sformatf(`" [SET REG TO 32'h%8h] `", ``IMM``)};\
    end

  // Overhead instructions to override zfinx fp instr operands with specific operand patterns
  `define MANIPULATE_GPR_OPERANDS(GPR,OPERAND) \
    if (instr.has_``GPR && ``OPERAND``_pattern != IS_RAND) begin\
      riscv_pseudo_instr          m_instr;\
      m_instr = riscv_pseudo_instr::type_id::create("m_instr");\
      `DV_CHECK_RANDOMIZE_WITH_FATAL(m_instr,\
        pseudo_instr_name == LI;\
        rd  == local::instr.``GPR``;\
      );\
      m_instr.imm = ``OPERAND``;\
      m_instr.update_imm_str();\
      instr_list.push_back(m_instr);\
      instr_list[$].comment = {instr_list[$].comment, $sformatf(`" [``OPERAND`` - %s - 32'h%8h] `", ``OPERAND``_pattern.name(), ``OPERAND``)};\
    end

  // 22 always exclude list within fp stream
  `define   EXCLUDE_INSTR_LIST      {JAL, JALR, BEQ, BNE, BLT, BGE, BLTU, BGEU, ECALL, EBREAK, \
                                     DRET, MRET, URET, SRET, WFI, C_EBREAK, C_BEQZ, C_BNEZ, C_J, C_JAL, \
                                     C_JR, C_JALR}

  // refer Table 6-1 user manual
  `define   RV32I_INT_COMP_INSTR_LIST   {ADD, ADDI, SUB, LUI, AUIPC, SLL, SLLI, SRL, SRLI, SRA, SRAI, \
                                         XOR, XORI, OR, ORI, AND, ANDI} /* with deterministic 1 cycle defined */
  `define   RV32M_MULH_INSTR_LIST       {MULH, MULHSU, MULHU} /* with deterministic 5 cycles defined */

