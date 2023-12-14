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
// This file holds the ISA decoder, and its subfunctions
// -------------------------------------------------------------------

`ifndef __ISA_DECODER__
`define __ISA_DECODER__


  // ---------------------------------------------------------------------------
  // Stack_adj for zcmp instructions
  // ---------------------------------------------------------------------------
  function automatic int get_stack_adj( rlist_t rlist, logic[5:4] spimm);
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


  // ---------------------------------------------------------------------------
  // Non-trivial immediate decoder
  // ---------------------------------------------------------------------------
  function automatic logic [20:1] get_sort_j_imm(instr_t instr);
    get_sort_j_imm = {
      instr.uncompressed.format.j.imm[31],
      instr.uncompressed.format.j.imm[21:12],
      instr.uncompressed.format.j.imm[22],
      instr.uncompressed.format.j.imm[30:23]
    };
  endfunction : get_sort_j_imm

  function automatic logic [11:0] get_sort_s_imm(instr_t instr);
    get_sort_s_imm = {
      instr.uncompressed.format.s.imm_h,
      instr.uncompressed.format.s.imm_l
    };
  endfunction : get_sort_s_imm

  function automatic logic [12:1] get_sort_b_imm(instr_t instr);
    get_sort_b_imm = {
      instr.uncompressed.format.b.imm_h[31],
      instr.uncompressed.format.b.imm_l[7],
      instr.uncompressed.format.b.imm_h[30:25],
      instr.uncompressed.format.b.imm_l[11:8]
    };
  endfunction : get_sort_b_imm

  function automatic logic [5:0] get_sort_ci_imm_lwsp(instr_t instr);
    get_sort_ci_imm_lwsp = {
      instr.compressed.format.ci.imm_6_2[3:2],
      instr.compressed.format.ci.imm_12,
      instr.compressed.format.ci.imm_6_2[6:4]
    };
  endfunction : get_sort_ci_imm_lwsp

  function automatic logic [5:0] get_sort_ci_imm_addi16sp(instr_t instr);
    get_sort_ci_imm_addi16sp = {
      instr.compressed.format.ci.imm_12,
      instr.compressed.format.ci.imm_6_2[4:3],
      instr.compressed.format.ci.imm_6_2[5],
      instr.compressed.format.ci.imm_6_2[2],
      instr.compressed.format.ci.imm_6_2[6]
    };
  endfunction : get_sort_ci_imm_addi16sp

  function automatic logic [7:0] get_sort_cb_imm_not_sequential(instr_t instr);
    get_sort_cb_imm_not_sequential = {
      instr.compressed.format.cb.offset_12_10[12],
      instr.compressed.format.cb.offset_6_2[6:5],
      instr.compressed.format.cb.offset_6_2[2],
      instr.compressed.format.cb.offset_12_10[11:10],
      instr.compressed.format.cb.offset_6_2[4:3]
    };
  endfunction : get_sort_cb_imm_not_sequential

  function automatic logic [10:0] get_sort_cj_imm(instr_t instr);
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

  function automatic logic [4:0] get_sort_cl_imm(instr_t instr);
      get_sort_cl_imm = {
        instr.compressed.format.cl.imm_6_5[5],
        instr.compressed.format.cl.imm_12_10,
        instr.compressed.format.cl.imm_6_5[6]
      };
  endfunction : get_sort_cl_imm

  function automatic logic [4:0] get_sort_cs_imm(instr_t instr);
      get_sort_cs_imm = {
        instr.compressed.format.cs.imm_6_5[5],
        instr.compressed.format.cs.imm_12_10,
        instr.compressed.format.cs.imm_6_5[6]
      };
  endfunction : get_sort_cs_imm

  function automatic logic [7:0] get_sort_ciw_imm(instr_t instr);
    get_sort_ciw_imm = {
      instr.compressed.format.ciw.imm[10:7],
      instr.compressed.format.ciw.imm[12:11],
      instr.compressed.format.ciw.imm[6],
      instr.compressed.format.ciw.imm[5]
      };
  endfunction : get_sort_ciw_imm

  function automatic gpr_t get_gpr_from_gpr_rvc(gpr_rvc_t gpr);
    gpr_t uncompressed_gpr;

    casex (gpr.gpr)
      C_X8:    uncompressed_gpr.gpr = X8;
      C_X9:    uncompressed_gpr.gpr = X9;
      C_X10:   uncompressed_gpr.gpr = X10;
      C_X11:   uncompressed_gpr.gpr = X11;
      C_X12:   uncompressed_gpr.gpr = X12;
      C_X13:   uncompressed_gpr.gpr = X13;
      C_X14:   uncompressed_gpr.gpr = X14;
      C_X15:   uncompressed_gpr.gpr = X15;
      default: uncompressed_gpr.gpr = X0; // Function used wrong if we ever end up here
    endcase

    return uncompressed_gpr;
  endfunction : get_gpr_from_gpr_rvc

  function automatic gpr_t get_gpr_from_gpr_rvc_sreg(gpr_rvc_sreg_t gpr);
    gpr_t uncompressed_gpr;

    casex (gpr.gpr)
      CS_X8:    uncompressed_gpr.gpr = X8;
      CS_X9:    uncompressed_gpr.gpr = X9;
      CS_X18:   uncompressed_gpr.gpr = X18;
      CS_X19:   uncompressed_gpr.gpr = X19;
      CS_X20:   uncompressed_gpr.gpr = X20;
      CS_X21:   uncompressed_gpr.gpr = X21;
      CS_X22:   uncompressed_gpr.gpr = X22;
      CS_X23:   uncompressed_gpr.gpr = X23;
      default: uncompressed_gpr.gpr = X0; // Function used wrong if we ever end up here
    endcase

    return uncompressed_gpr;
  endfunction : get_gpr_from_gpr_rvc_sreg

  // ---------------------------------------------------------------------------
  // Find the value of immediate
  // ---------------------------------------------------------------------------
  function automatic int get_imm_value_i(logic[11:0] imm);
    if(imm[11] == 1) begin
      get_imm_value_i = {20'hfffff, imm};
    end else begin
      get_imm_value_i = {20'b0, imm};
    end
  endfunction : get_imm_value_i

  function automatic int get_imm_value_j(logic[20:1] imm);
    if(imm[20] == 1) begin
      get_imm_value_j = {11'h7ff, imm, 1'b0};
    end else begin
      get_imm_value_j = {11'b0, imm, 1'b0};
    end
  endfunction : get_imm_value_j

  function automatic int get_imm_value_b(logic[12:1] imm);
    if(imm[12] == 1) begin
      get_imm_value_b = {19'h7ffff, imm, 1'b0};
    end else begin
      get_imm_value_b = {19'b0, imm, 1'b0};
    end
  endfunction : get_imm_value_b

  function automatic int get_imm_value_ci(logic[5:0] imm);
    if(imm[5] == 1) begin
      get_imm_value_ci = {26'h3ffffff, imm};
    end else begin
      get_imm_value_ci = {26'b0, imm};
    end
  endfunction : get_imm_value_ci

  function automatic int get_imm_value_ci_lui(logic[17:12] imm);
    if(imm[17] == 1) begin
      get_imm_value_ci_lui = {14'h3fff, imm, 12'b0};
    end else begin
      get_imm_value_ci_lui = {14'b0, imm, 12'b0};
    end
  endfunction : get_imm_value_ci_lui

  function automatic int get_imm_value_ci_addi16sp(logic[9:4] imm);
    if(imm[9] == 1) begin
      get_imm_value_ci_addi16sp = {22'h3fffff, imm, 4'b0};
    end else begin
      get_imm_value_ci_addi16sp = {22'b0, imm, 4'b0};
    end
  endfunction : get_imm_value_ci_addi16sp

  function automatic int get_imm_value_cb(logic[8:1] imm);
    if(imm[8] == 1) begin
      get_imm_value_cb = {23'h7fffff, imm, 1'b0};
    end else begin
      get_imm_value_cb = {22'b0, imm, 1'b0};
    end
  endfunction : get_imm_value_cb

  function automatic int get_imm_value_cj(logic[11:1] imm);
    if(imm[11] == 1) begin
      get_imm_value_cj = {20'hfffff, imm, 1'b0};
    end else begin
      get_imm_value_cj = {20'b0, imm, 1'b0};
    end
  endfunction : get_imm_value_cj


  // Get the correspopnding name of the hint instruction
  function automatic hint_name_e get_hint_name(instr_name_e name);
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
  function automatic logic check_if_hint(instr_name_e name, instr_format_e format, instr_t instr);
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


  function automatic logic[11:0] read_s_imm(logic[31:0] instr);
    automatic logic [11:0] imm;
    imm = {instr[31:25], instr[11:7]};
    return imm;
  endfunction : read_s_imm


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
    end

    casex (format)
      I_TYPE: begin
        if (asm.instr inside { FENCE_I, ECALL, EBREAK, MRET, DRET, WFI, WFE }) begin
          asm.rd.valid              = 0;
          asm.rs1.valid             = 0;
          asm.rs2.valid             = 0;
          asm.imm.valid             = 0;
        end else if (asm.instr inside { FENCE }) begin
          asm.imm.imm_raw           = instr.uncompressed.format.i.imm;
          asm.imm.imm_raw_sorted    = instr.uncompressed.format.i.imm;
          asm.imm.imm_type          = IMM;
          asm.imm.width             = 12;
          asm.imm.sign_ext          = 1;
          asm.imm.imm_value         = get_imm_value_i(instr.uncompressed.format.i.imm);
          asm.imm.valid             = 1;
        end else if (asm.instr inside { CSRRW, CSRRS, CSRRC }) begin
          asm.rd.gpr                = instr.uncompressed.format.i.rd.gpr;
          asm.rs1.gpr               = instr.uncompressed.format.i.rs1.gpr;
          asm.csr.address           = instr.uncompressed.format.i.imm;
          asm.rd.valid              = 1;
          asm.rs1.valid             = 1;
          asm.csr.valid             = 1;
        end else if (asm.instr inside { CSRRWI, CSRRSI, CSRRCI }) begin
          asm.rd.gpr                = instr.uncompressed.format.i.rd.gpr;
          asm.imm.imm_raw           = instr.uncompressed.format.i.rs1;
          asm.imm.imm_raw_sorted    = instr.uncompressed.format.i.rs1;
          asm.imm.imm_type          = UIMM;
          asm.imm.width             = 5;
          asm.imm.imm_value         = instr.uncompressed.format.i.rs1;
          asm.csr.address           = instr.uncompressed.format.i.imm;
          asm.rd.valid              = 1;
          asm.imm.valid             = 1;
          asm.csr.valid             = 1;
        end else if (asm.instr inside { RORI, BEXTI, BCLRI, BINVI, BSETI, SLLI, SRLI, SRAI }) begin
          asm.rd.gpr                = instr.uncompressed.format.i.rd.gpr;
          asm.rs1.gpr               = instr.uncompressed.format.i.rs1.gpr;
          asm.imm.imm_raw           = instr.uncompressed.format.i.imm.shamt;
          asm.imm.imm_raw_sorted    = instr.uncompressed.format.i.imm.shamt;
          asm.imm.imm_type          = SHAMT;
          asm.imm.width             = 5;
          asm.imm.imm_value         = instr.uncompressed.format.i.imm.shamt;
          asm.rd.valid              = 1;
          asm.rs1.valid             = 1;
          asm.imm.valid             = 1;
        end else begin
          asm.rd.gpr                = instr.uncompressed.format.i.rd.gpr;
          asm.rs1.gpr               = instr.uncompressed.format.i.rs1.gpr;
          asm.imm.imm_raw           = instr.uncompressed.format.i.imm;
          asm.imm.imm_raw_sorted    = instr.uncompressed.format.i.imm;
          asm.imm.imm_type          = IMM;
          asm.imm.width             = 12;
          asm.imm.sign_ext          = 1;
          asm.imm.imm_value         = get_imm_value_i(instr.uncompressed.format.i.imm);
          asm.rd.valid              = 1;
          asm.rs1.valid             = 1;
          asm.imm.valid             = 1;
        end
      end
      J_TYPE: begin
        asm.rd.gpr                  = instr.uncompressed.format.j.rd.gpr;
        asm.imm.imm_raw             = instr.uncompressed.format.j.imm;
        asm.imm.imm_raw_sorted      = get_sort_j_imm(instr);
        asm.imm.imm_type            = OFFSET;
        asm.imm.width               = 20;
        asm.imm.sign_ext            = 1;
        asm.imm.imm_value           = get_imm_value_j(get_sort_j_imm(instr));
        asm.rd.valid                = 1;
        asm.imm.valid               = 1;
      end
      S_TYPE: begin
        asm.rs1.gpr                 = instr.uncompressed.format.s.rs1.gpr;
        asm.rs2.gpr                 = instr.uncompressed.format.s.rs2.gpr;
        asm.imm.imm_raw             = get_sort_s_imm(instr);
        asm.imm.imm_raw_sorted      = get_sort_s_imm(instr);
        asm.imm.imm_type            = IMM;
        asm.imm.width               = 12;
        asm.imm.sign_ext            = 1;
        asm.imm.imm_value           = get_imm_value_i(get_sort_s_imm(instr));
        asm.rs1.valid               = 1;
        asm.rs2.valid               = 1;
        asm.imm.valid               = 1;
      end
      R_TYPE: begin
        if ( asm.instr inside { LR_W, SC_W, AMOSWAP_W, AMOADD_W, AMOXOR_W, AMOAND_W, AMOOR_W, AMOMIN_W, AMOMAX_W, AMOMINU_W, AMOMAXU_W } ) begin
          asm.rd.gpr                = instr.uncompressed.format.r.rd.gpr;
          asm.rs1.gpr               = instr.uncompressed.format.r.rs1.gpr;
          asm.rs2.gpr               = instr.uncompressed.format.r.rs2.gpr;
          asm.atomic.aq             = instr.uncompressed.format.r.funct7[26];
          asm.atomic.rl             = instr.uncompressed.format.r.funct7[25];
          asm.rd.valid              = 1;
          asm.rs1.valid             = 1;
          asm.rs2.valid             = 1;
          asm.atomic.valid          = 1;
        end else begin
          asm.rd.gpr                = instr.uncompressed.format.r.rd.gpr;
          asm.rs1.gpr               = instr.uncompressed.format.r.rs1.gpr;
          asm.rs2.gpr               = instr.uncompressed.format.r.rs2.gpr;
          asm.rd.valid              = 1;
          asm.rs1.valid             = 1;
          asm.rs2.valid             = 1;
        end
      end
      R4_TYPE: begin
        asm.rd.gpr                  = instr.uncompressed.format.r4.rd.gpr;
        asm.rs1.gpr                 = instr.uncompressed.format.r4.rs1.gpr;
        asm.rs2.gpr                 = instr.uncompressed.format.r4.rs2.gpr;
        asm.rs3.gpr                 = instr.uncompressed.format.r4.rs3.gpr;
        asm.rd.valid                = 1;
        asm.rs1.valid               = 1;
        asm.rs2.valid               = 1;
        asm.rs3.valid               = 1;
      end
      B_TYPE: begin
        asm.rs1.gpr                 = instr.uncompressed.format.b.rs1.gpr;
        asm.rs2.gpr                 = instr.uncompressed.format.b.rs2.gpr;
        asm.imm.imm_raw             = {instr.uncompressed.format.b.imm_h, instr.uncompressed.format.b.imm_l};
        asm.imm.imm_raw_sorted      = get_sort_b_imm(instr);
        asm.imm.imm_type            = IMM;
        asm.imm.width               = 12;
        asm.imm.sign_ext            = 1;
        asm.imm.imm_value           = get_imm_value_b(get_sort_b_imm(instr));
        asm.rs1.valid               = 1;
        asm.rs2.valid               = 1;
        asm.imm.valid               = 1;
      end
      U_TYPE: begin
        asm.rd.gpr                  = instr.uncompressed.format.u.rd.gpr;
        asm.imm.imm_raw             = instr.uncompressed.format.u.imm;
        asm.imm.imm_raw_sorted      = instr.uncompressed.format.u.imm;
        asm.imm.imm_type            = IMM;
        asm.imm.width               = 20;
        asm.imm.imm_value           = { instr.uncompressed.format.u.imm, 12'b0000_0000_0000 };
        asm.rd.valid                = 1;
        asm.imm.valid               = 1;
      end
      // Compressed
      CR_TYPE: begin
        if (name inside { C_EBREAK }) begin
          asm.rd.valid              = 0;
          asm.rs1.valid             = 0;
          asm.rs2.valid             = 0;
          asm.rs3.valid             = 0;
          asm.imm.valid             = 0;
        end else if (name inside { C_MV }) begin
          asm.rd.gpr                = instr.compressed.format.cr.rd_rs1.gpr;
          asm.rs1.gpr               = instr.compressed.format.cr.rd_rs1.gpr;
          asm.rs2.gpr               = instr.compressed.format.cr.rs2.gpr;
          asm.rd.valid              = 1;
          asm.rs2.valid             = 1;
          asm.rs1.valid             = 1;
        end else if (name inside { C_ADD }) begin
          asm.rd.gpr                = instr.compressed.format.cr.rd_rs1.gpr;
          asm.rs1.gpr               = instr.compressed.format.cr.rd_rs1.gpr;
          asm.rs2.gpr               = instr.compressed.format.cr.rs2.gpr;
          asm.rd.valid              = 1;
          asm.rs1.valid             = 1;
          asm.rs2.valid             = 1;
        end else if (name inside { C_JR, C_JALR }) begin
          asm.rs1.gpr               = instr.compressed.format.cr.rd_rs1.gpr;
          asm.rs2.gpr               = instr.compressed.format.cr.rs2.gpr;
          asm.rs1.valid             = 1;
          asm.rs2.valid             = 1;
        end
      end
      CI_TYPE: begin
        if (name inside { C_NOP, C_ADDI }) begin
          asm.rd.gpr                = instr.compressed.format.ci.rd_rs1.gpr;
          asm.rs1.gpr               = instr.compressed.format.ci.rd_rs1.gpr;
          asm.imm.imm_raw           = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_raw_sorted    = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_type          = IMM;
          asm.imm.width             = 6;
          asm.imm.sign_ext          = 1;
          asm.imm.imm_value         = get_imm_value_ci({ instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 });
          asm.rd.valid              = 1;
          asm.rs1.valid             = 1;
          asm.imm.valid             = 1;
        end else if (name          == C_LI) begin
          asm.rd.gpr                = instr.compressed.format.ci.rd_rs1.gpr;
          asm.imm.imm_raw           = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_raw_sorted    = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_type          = IMM;
          asm.imm.width             = 6;
          asm.imm.sign_ext          = 1;
          asm.imm.imm_value         = get_imm_value_ci({ instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 });
          asm.rd.valid              = 1;
          asm.imm.valid             = 1;
        end else if (name          == C_LUI) begin
          asm.rd.gpr                = instr.compressed.format.ci.rd_rs1.gpr;
          asm.imm.imm_raw           = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_raw_sorted    = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_type          = NZIMM;
          asm.imm.width             = 6;
          asm.imm.sign_ext          = 1;
          asm.imm.imm_value         = get_imm_value_ci_lui({ instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 });
          asm.rd.valid              = 1;
          asm.imm.valid             = 1;
        end else if (name inside { C_LWSP }) begin
          asm.rd.gpr                = instr.compressed.format.ci.rd_rs1.gpr;
          asm.imm.imm_raw           = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_raw_sorted    = get_sort_ci_imm_lwsp(instr);
          asm.imm.imm_type          = OFFSET;
          asm.imm.width             = 6;
          asm.imm.imm_value         = {24'b0, get_sort_ci_imm_lwsp(instr), 2'b0};
          asm.rd.valid              = 1;
          asm.imm.valid             = 1;
        end else if (name inside { C_ADDI16SP }) begin
          asm.rs1.gpr               = instr.compressed.format.ci.rd_rs1.gpr;
          asm.rd.gpr                = instr.compressed.format.ci.rd_rs1.gpr;
          asm.imm.imm_raw           = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_raw_sorted    = get_sort_ci_imm_addi16sp(instr);
          asm.imm.imm_type          = NZIMM;
          asm.imm.width             = 6;
          asm.imm.sign_ext          = 1;
          asm.imm.imm_value         = get_imm_value_ci_addi16sp(get_sort_ci_imm_addi16sp(instr));
          asm.rs1.valid             = 1;
          asm.rd.valid              = 1;
          asm.imm.valid             = 1;
        end else if (name inside { C_SLLI }) begin
          asm.rs1.gpr               = instr.compressed.format.ci.rd_rs1.gpr;
          asm.rd.gpr                = instr.compressed.format.ci.rd_rs1.gpr;
          asm.imm.imm_raw           = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_raw_sorted    = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.imm.imm_type          = SHAMT;
          asm.imm.width             = 6;
          asm.imm.imm_value         = { instr.compressed.format.ci.imm_12, instr.compressed.format.ci.imm_6_2 };
          asm.rs1.valid             = 1;
          asm.rd.valid              = 1;
          asm.imm.valid             = 1;
        end
      end
      CSS_TYPE: begin
        asm.rs2.gpr                 = instr.compressed.format.css.rs2.gpr;
        asm.imm.imm_raw             = instr.compressed.format.css.imm;
        asm.imm.imm_raw_sorted      = { instr.compressed.format.css.imm[9:7], instr.compressed.format.css.imm[12:10] };
        asm.imm.imm_type            = OFFSET;
        asm.imm.width               = 6;
        asm.imm.imm_value           = { 24'b0, instr.compressed.format.css.imm[9:7], instr.compressed.format.css.imm[12:10], 2'b0 };
        asm.rs2.valid               = 1;
        asm.imm.valid               = 1;
      end
      CIW_TYPE: begin
        asm.rd.gpr                  = get_gpr_from_gpr_rvc(instr.compressed.format.ciw.rd.gpr);
        asm.rd.gpr_rvc              = instr.compressed.format.ciw.rd.gpr;
        asm.imm.imm_raw             = instr.compressed.format.ciw.imm;
        asm.imm.imm_raw_sorted      = get_sort_ciw_imm(instr);
        asm.imm.imm_type            = NZUIMM;
        asm.imm.width               = 8;
        asm.imm.imm_value           = { 22'b0, get_sort_ciw_imm(instr), 2'b0 };
        asm.imm.valid               = 1;
        asm.rd.valid                = 1;
        asm.rd.valid_gpr_rvc        = 1;
      end
      CL_TYPE: begin
        asm.rd.gpr                  = get_gpr_from_gpr_rvc(instr.compressed.format.cl.rd.gpr);
        asm.rd.gpr_rvc              = instr.compressed.format.cl.rd.gpr;
        asm.rs1.gpr                 = get_gpr_from_gpr_rvc(instr.compressed.format.cl.rs1.gpr);
        asm.rs1.gpr_rvc             = instr.compressed.format.cl.rs1.gpr;
        asm.imm.imm_raw             = { instr.compressed.format.cl.imm_12_10, instr.compressed.format.cl.imm_6_5 };
        asm.imm.imm_raw_sorted      = get_sort_cl_imm(instr);
        asm.imm.imm_type            = OFFSET;
        asm.imm.width               = 5;
        asm.imm.imm_value           = { 25'b0, get_sort_cl_imm(instr), 2'b0 };
        asm.rd.valid                = 1;
        asm.rd.valid_gpr_rvc        = 1;
        asm.rs1.valid               = 1;
        asm.rs1.valid_gpr_rvc       = 1;
        asm.imm.valid               = 1;
      end
      CS_TYPE: begin
        asm.rs2.gpr                 = get_gpr_from_gpr_rvc(instr.compressed.format.cs.rs2.gpr);
        asm.rs2.gpr_rvc             = instr.compressed.format.cs.rs2.gpr;
        asm.rs1.gpr                 = get_gpr_from_gpr_rvc(instr.compressed.format.cs.rs1.gpr);
        asm.rs1.gpr_rvc             = instr.compressed.format.cs.rs1.gpr;
        asm.imm.imm_raw             = { instr.compressed.format.cs.imm_12_10, instr.compressed.format.cs.imm_6_5 };
        asm.imm.imm_raw_sorted      = get_sort_cs_imm(instr);
        asm.imm.imm_type            = OFFSET;
        asm.imm.width               = 5;
        asm.imm.imm_value           = { 25'b0, get_sort_cs_imm(instr), 2'b0 };
        asm.rs2.valid               = 1;
        asm.rs2.valid_gpr_rvc       = 1;
        asm.rs1.valid               = 1;
        asm.rs1.valid_gpr_rvc       = 1;
        asm.imm.valid               = 1;
      end
      CA_TYPE: begin
        asm.rd.gpr                  = get_gpr_from_gpr_rvc(instr.compressed.format.ca.rd_rs1.gpr);
        asm.rd.gpr_rvc              = instr.compressed.format.ca.rd_rs1.gpr;
        asm.rs1.gpr                 = get_gpr_from_gpr_rvc(instr.compressed.format.ca.rd_rs1.gpr);
        asm.rs1.gpr_rvc             = instr.compressed.format.ca.rd_rs1.gpr;
        asm.rs2.gpr                 = get_gpr_from_gpr_rvc(instr.compressed.format.ca.rs2.gpr);
        asm.rs2.gpr_rvc             = instr.compressed.format.ca.rs2.gpr;
        asm.rd.valid                = 1;
        asm.rd.valid_gpr_rvc        = 1;
        asm.rs1.valid               = 1;
        asm.rs1.valid_gpr_rvc       = 1;
        asm.rs2.valid               = 1;
        asm.rs2.valid_gpr_rvc       = 1;
      end
      CB_TYPE: begin
        if (name inside { C_SRLI, C_SRAI }) begin
          asm.rd.gpr                = get_gpr_from_gpr_rvc(instr.compressed.format.cb.rd_rs1.gpr);
          asm.rd.gpr_rvc            = instr.compressed.format.cb.rd_rs1.gpr;
          asm.rs1.gpr               = get_gpr_from_gpr_rvc(instr.compressed.format.cb.rd_rs1.gpr);
          asm.rs1.gpr_rvc           = instr.compressed.format.cb.rd_rs1.gpr;
          asm.imm.imm_raw           = { instr.compressed.format.cb.offset_12_10[12], instr.compressed.format.cb.offset_6_2 };
          asm.imm.imm_raw_sorted    = { instr.compressed.format.cb.offset_12_10[12], instr.compressed.format.cb.offset_6_2 };
          asm.imm.imm_type          = SHAMT;
          asm.imm.width             = 6;
          asm.imm.imm_value         = { instr.compressed.format.cb.offset_12_10[12], instr.compressed.format.cb.offset_6_2 };
          asm.rd.valid              = 1;
          asm.rd.valid_gpr_rvc      = 1;
          asm.rs1.valid             = 1;
          asm.rs1.valid_gpr_rvc     = 1;
          asm.imm.valid             = 1;
        end else if (name inside { C_BEQZ, C_BNEZ }) begin
          asm.rs1.gpr               = get_gpr_from_gpr_rvc(instr.compressed.format.cb.rd_rs1.gpr);
          asm.rs1.gpr_rvc           = instr.compressed.format.cb.rd_rs1.gpr;
          asm.imm.imm_raw           = { instr.compressed.format.cb.offset_12_10, instr.compressed.format.cb.offset_6_2 };
          asm.imm.imm_raw_sorted    = get_sort_cb_imm_not_sequential(instr);
          asm.imm.imm_type          = OFFSET;
          asm.imm.width             = 8;
          asm.imm.sign_ext          = 1;
          asm.imm.imm_value         = get_imm_value_cb(get_sort_cb_imm_not_sequential(instr));
          asm.rs1.valid             = 1;
          asm.rs1.valid_gpr_rvc     = 1;
          asm.imm.valid             = 1;
        end else if (name inside { C_ANDI }) begin
          asm.rd.gpr                = get_gpr_from_gpr_rvc(instr.compressed.format.cb.rd_rs1.gpr);
          asm.rd.gpr_rvc            = instr.compressed.format.cb.rd_rs1.gpr;
          asm.rs1.gpr               = get_gpr_from_gpr_rvc(instr.compressed.format.cb.rd_rs1.gpr);
          asm.rs1.gpr_rvc           = instr.compressed.format.cb.rd_rs1.gpr;
          asm.imm.imm_raw           = { instr.compressed.format.cb.offset_12_10[12], instr.compressed.format.cb.offset_6_2 };
          asm.imm.imm_raw_sorted    = { instr.compressed.format.cb.offset_12_10[12], instr.compressed.format.cb.offset_6_2 };
          asm.imm.imm_type          = IMM;
          asm.imm.width             = 6;
          asm.imm.sign_ext          = 1;
          asm.imm.imm_value         = get_imm_value_cb({ instr.compressed.format.cb.offset_12_10[12], instr.compressed.format.cb.offset_6_2 });
          asm.rd.valid              = 1;
          asm.rd.valid_gpr_rvc      = 1;
          asm.rs1.valid             = 1;
          asm.rs1.valid_gpr_rvc     = 1;
          asm.imm.valid             = 1;
        end
      end
      CJ_TYPE: begin
        asm.imm.imm_raw             = instr.compressed.format.cj.imm;
        asm.imm.imm_raw_sorted      = get_sort_cj_imm(instr);
        asm.imm.imm_type            = OFFSET;
        asm.imm.width               = 11;
        asm.imm.sign_ext            = 1;
        asm.imm.imm_value           = get_imm_value_cj(get_sort_cj_imm(instr));
        asm.imm.valid               = 1;
      end
      CLB_TYPE: begin
        asm.imm.imm_raw             = instr.compressed.format.clb.uimm;
        asm.imm.imm_raw_sorted      = { instr.compressed.format.clb.uimm[5], instr.compressed.format.clb.uimm[6] };
        asm.imm.imm_type            = UIMM;
        asm.imm.width               = 2;
        asm.imm.imm_value           = { instr.compressed.format.clb.uimm[5], instr.compressed.format.clb.uimm[6] };
        asm.rs1.gpr                 = get_gpr_from_gpr_rvc(instr.compressed.format.clb.rs1.gpr);
        asm.rs1.gpr_rvc             = instr.compressed.format.clb.rs1.gpr;
        asm.rd.gpr                  = get_gpr_from_gpr_rvc(instr.compressed.format.clb.rd.gpr);
        asm.rd.gpr_rvc              = instr.compressed.format.clb.rd.gpr;
        asm.rs1.valid               = 1;
        asm.rs1.valid_gpr_rvc       = 1;
        asm.rd.valid                = 1;
        asm.rd.valid_gpr_rvc        = 1;
        asm.imm.valid               = 1;
      end
      CSB_TYPE: begin
        asm.imm.imm_raw             = instr.compressed.format.csb.uimm;
        asm.imm.imm_raw_sorted      = { instr.compressed.format.csb.uimm[5], instr.compressed.format.csb.uimm[6] };
        asm.imm.imm_type            = UIMM;
        asm.imm.width               = 2;
        asm.imm.imm_value           = { instr.compressed.format.csb.uimm[5], instr.compressed.format.csb.uimm[6] };
        asm.rs1.gpr                 = get_gpr_from_gpr_rvc(instr.compressed.format.csb.rs1.gpr);
        asm.rs1.gpr_rvc             = instr.compressed.format.csb.rs1.gpr;
        asm.rs2.gpr                 = get_gpr_from_gpr_rvc(instr.compressed.format.csb.rs2.gpr);
        asm.rs2.gpr_rvc             = instr.compressed.format.csb.rs2.gpr;
        asm.rs1.valid               = 1;
        asm.rs1.valid_gpr_rvc       = 1;
        asm.rs2.valid               = 1;
        asm.rs2.valid_gpr_rvc       = 1;
        asm.imm.valid               = 1;
      end
      CLH_TYPE: begin
        asm.imm.imm_raw             = instr.compressed.format.clh.uimm;
        asm.imm.imm_raw_sorted      = instr.compressed.format.clh.uimm;
        asm.imm.imm_type            = UIMM;
        asm.imm.width               = 1;
        asm.imm.imm_value           = { 30'b0, instr.compressed.format.clh.uimm };
        asm.rs1.gpr                 = get_gpr_from_gpr_rvc(instr.compressed.format.clh.rs1.gpr);
        asm.rs1.gpr_rvc             = instr.compressed.format.clh.rs1.gpr;
        asm.rd.gpr                  = get_gpr_from_gpr_rvc(instr.compressed.format.clh.rd.gpr);
        asm.rd.gpr_rvc              = instr.compressed.format.clh.rd.gpr;
        asm.rs1.valid               = 1;
        asm.rs1.valid_gpr_rvc       = 1;
        asm.rd.valid                = 1;
        asm.rd.valid_gpr_rvc        = 1;
        asm.imm.valid               = 1;
      end
      CSH_TYPE: begin
        asm.imm.imm_raw             = instr.compressed.format.csh.uimm;
        asm.imm.imm_raw_sorted      = instr.compressed.format.csh.uimm;
        asm.imm.imm_type            = UIMM;
        asm.imm.width               = 1;
        asm.imm.imm_value           = {30'b0, instr.compressed.format.csh.uimm, 1'b0};
        asm.rs1.gpr                 = get_gpr_from_gpr_rvc(instr.compressed.format.csh.rs1.gpr);
        asm.rs1.gpr_rvc             = instr.compressed.format.csh.rs1.gpr;
        asm.rs2.gpr                 = get_gpr_from_gpr_rvc(instr.compressed.format.csh.rs2.gpr);
        asm.rs2.gpr_rvc             = instr.compressed.format.csh.rs2.gpr;
        asm.rs1.valid               = 1;
        asm.rs1.valid_gpr_rvc       = 1;
        asm.rs2.valid               = 1;
        asm.rs2.valid_gpr_rvc       = 1;
        asm.imm.valid               = 1;
      end
      CU_TYPE: begin
        asm.rs1.gpr                 = get_gpr_from_gpr_rvc(instr.compressed.format.cu.rd_rs1.gpr);
        asm.rs1.gpr_rvc             = instr.compressed.format.cu.rd_rs1.gpr;
        asm.rd.gpr                  = get_gpr_from_gpr_rvc(instr.compressed.format.cu.rd_rs1.gpr);
        asm.rd.gpr_rvc              = instr.compressed.format.cu.rd_rs1.gpr;
        asm.rs1.valid               = 1;
        asm.rs1.valid_gpr_rvc       = 1;
        asm.rd.valid                = 1;
        asm.rd.valid_gpr_rvc        = 1;
      end
      CMMV_TYPE: begin
        asm.rs1.gpr                 = get_gpr_from_gpr_rvc_sreg(instr.compressed.format.cmmv.r1s.gpr);
        asm.rs1.gpr_rvc_sreg        = instr.compressed.format.cmmv.r1s.gpr;
        asm.rs2.gpr                 = get_gpr_from_gpr_rvc_sreg(instr.compressed.format.cmmv.r2s.gpr);
        asm.rs2.gpr_rvc_sreg        = instr.compressed.format.cmmv.r2s.gpr;
        asm.rs1.valid               = 1;
        asm.rs1.valid_gpr_rvc_sreg  = 1;
        asm.rs2.valid               = 1;
        asm.rs2.valid_gpr_rvc_sreg  = 1;
      end
      CMJT_TYPE: begin
        asm.imm.imm_raw             = instr.compressed.format.cmjt.index;
        asm.imm.imm_raw_sorted      = instr.compressed.format.cmjt.index;
        asm.imm.imm_type            = INDEX;
        asm.imm.width               = 1;
        asm.imm.imm_value           = instr.compressed.format.cmjt.index;
        asm.imm.valid               = 1;
      end
      CMPP_TYPE: begin
        asm.imm.imm_raw             = instr.compressed.format.cmpp.spimm;
        asm.imm.imm_raw_sorted      = instr.compressed.format.cmpp.spimm;
        asm.imm.imm_type            = SPIMM;
        asm.imm.width               = 1;
        asm.rlist.rlist             = instr.compressed.format.cmpp.urlist;
        asm.stack_adj.stack_adj     = get_stack_adj(instr.compressed.format.cmpp.urlist, instr.compressed.format.cmpp.spimm);
        asm.imm.valid               = 1;
        asm.rs1.gpr                 = instr.compressed.format.csh.rs1.gpr;
        asm.rs2.gpr                 = instr.compressed.format.csh.rs2.gpr;
        asm.rs1.valid               = 1;
        asm.rs2.valid               = 1;
        asm.rlist.valid             = 1;
        asm.stack_adj.valid         = 1;
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

      (   (instr.uncompressed.opcode              == MISC_MEM)
       && (instr.uncompressed.format.i.funct3     == 3'b0)) :
        asm = build_asm(FENCE, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == MISC_MEM)
       && (instr.uncompressed.format.i.funct3     == 3'b001)) :
        asm = build_asm(FENCE_I, I_TYPE, instr);

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

	    //A
      (   (instr.uncompressed.opcode                 == AMO)
       && (instr.uncompressed.format.r.funct3        == FUNCT3_A_W)
       && (instr.uncompressed.format.r.rs2           == X0)
       && (instr.uncompressed.format.r.funct7[31:27] == FUNCT5_LR_W)) :
        asm = build_asm(LR_W, R_TYPE, instr);

      (   (instr.uncompressed.opcode                 == AMO)
       && (instr.uncompressed.format.r.funct3        == FUNCT3_A_W)
       && (instr.uncompressed.format.r.funct7[31:27] == FUNCT5_SC_W)) :
        asm = build_asm(SC_W, R_TYPE, instr);

      (   (instr.uncompressed.opcode                 == AMO)
       && (instr.uncompressed.format.r.funct3        == FUNCT3_A_W)
       && (instr.uncompressed.format.r.funct7[31:27] == FUNCT5_AMOSWAP_W)) :
        asm = build_asm(AMOSWAP_W, R_TYPE, instr);

      (   (instr.uncompressed.opcode                 == AMO)
       && (instr.uncompressed.format.r.funct3        == FUNCT3_A_W)
       && (instr.uncompressed.format.r.funct7[31:27] == FUNCT5_AMOADD_W)) :
        asm = build_asm(AMOADD_W, R_TYPE, instr);

      (   (instr.uncompressed.opcode                 == AMO)
       && (instr.uncompressed.format.r.funct3        == FUNCT3_A_W)
       && (instr.uncompressed.format.r.funct7[31:27] == FUNCT5_AMOXOR_W)) :
        asm = build_asm(AMOXOR_W, R_TYPE, instr);

      (   (instr.uncompressed.opcode                 == AMO)
       && (instr.uncompressed.format.r.funct3        == FUNCT3_A_W)
       && (instr.uncompressed.format.r.funct7[31:27] == FUNCT5_AMOAND_W)) :
        asm = build_asm(AMOAND_W, R_TYPE, instr);

      (   (instr.uncompressed.opcode                 == AMO)
       && (instr.uncompressed.format.r.funct3        == FUNCT3_A_W)
       && (instr.uncompressed.format.r.funct7[31:27] == FUNCT5_AMOOR_W)) :
        asm = build_asm(AMOOR_W, R_TYPE, instr);

      (   (instr.uncompressed.opcode                 == AMO)
       && (instr.uncompressed.format.r.funct3        == FUNCT3_A_W)
       && (instr.uncompressed.format.r.funct7[31:27] == FUNCT5_AMOMIN_W)) :
        asm = build_asm(AMOMIN_W, R_TYPE, instr);

      (   (instr.uncompressed.opcode                 == AMO)
       && (instr.uncompressed.format.r.funct3        == FUNCT3_A_W)
       && (instr.uncompressed.format.r.funct7[31:27] == FUNCT5_AMOMAX_W)) :
        asm = build_asm(AMOMAX_W, R_TYPE, instr);

      (   (instr.uncompressed.opcode                 == AMO)
       && (instr.uncompressed.format.r.funct3        == FUNCT3_A_W)
       && (instr.uncompressed.format.r.funct7[31:27] == FUNCT5_AMOMINU_W)) :
        asm = build_asm(AMOMINU_W, R_TYPE, instr);

      (   (instr.uncompressed.opcode                 == AMO)
       && (instr.uncompressed.format.r.funct3        == FUNCT3_A_W)
       && (instr.uncompressed.format.r.funct7[31:27] == FUNCT5_AMOMAXU_W)) :
        asm = build_asm(AMOMAXU_W, R_TYPE, instr);

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
       && (instr.uncompressed.format.i.funct3     == FUNCT3_ORC_B)
       && (instr.uncompressed.format.i.imm        == 12'b0010_1000_0111)) :
        asm = build_asm(ORC_B, I_TYPE, instr);

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
        asm = build_asm(SEXT_B, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP_IMM)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_SEXT)
       && (instr.uncompressed.format.i.imm        == 12'b0110_0000_0101)) :
        asm = build_asm(SEXT_H, I_TYPE, instr);

      (   (instr.uncompressed.opcode              == OP)
       && (instr.uncompressed.format.i.funct3     == FUNCT3_ZEXT_H)
       && (instr.uncompressed.format.i.imm        == 12'b0000_1000_0000)) :
        asm = build_asm(ZEXT_H, I_TYPE, instr);

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
       && (instr.compressed.format.ci.rd_rs1.gpr          != X0)
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
       && (instr.compressed.format.cu.funct5              == FUNCT5_C_ZEXT_B)
       && (instr.compressed.format.cu.funct6              == 6'b100111)) :
        asm = build_asm(C_ZEXT_B, CU_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cu.funct5              == FUNCT5_C_SEXT_B)
       && (instr.compressed.format.cu.funct6              == 6'b100111)) :
        asm = build_asm(C_SEXT_B, CU_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cu.funct5              == FUNCT5_C_ZEXT_H)
       && (instr.compressed.format.cu.funct6              == 6'b100111)) :
        asm = build_asm(C_ZEXT_H, CU_TYPE, instr);

      (   (instr.compressed.opcode                        == C1)
       && (instr.compressed.format.cu.funct5              == FUNCT5_C_SEXT_H)
       && (instr.compressed.format.cu.funct6              == 6'b100111)) :
        asm = build_asm(C_SEXT_H, CU_TYPE, instr);

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
  // FIXME: is this a redundant declaration of match_instr?
`ifndef QUESTA_VSIM
  function automatic match_instr(instr_t instr, instr_name_e instr_type);
    match_instr = (decode_instr(instr).instr == instr_type);
  endfunction : match_instr
`endif // QUESTA_VSIM


//endpackage

`endif // __ISA_DECODER__

