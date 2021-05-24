// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
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
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


covergroup cg_rtype(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_rd: coverpoint instr.rd;
endgroup : cg_rtype


covergroup cg_itype(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;
  cp_immi: coverpoint instr.immi;
endgroup : cg_itype


covergroup cg_stype(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_imms: coverpoint instr.imms;
endgroup : cg_stype


covergroup cg_btype(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_immb: coverpoint instr.immb;
endgroup : cg_btype


covergroup cg_utype(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rd: coverpoint instr.rd;
  cp_immu: coverpoint instr.immu;
endgroup : cg_utype


covergroup cg_jtype(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rd: coverpoint instr.rd;
  cp_immj: coverpoint instr.immj;
endgroup : cg_jtype


covergroup cg_cr(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_rdrs1: coverpoint instr.c_rdrs1;
  cp_c_rs2: coverpoint instr.c_rs2;
endgroup : cg_cr


covergroup cg_ci(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_immi: coverpoint instr.c_immi;
  cp_c_rdrs1: coverpoint instr.c_rdrs1;
endgroup : cg_ci


covergroup cg_css(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_immss: coverpoint instr.c_immss;
  cp_c_rs2: coverpoint instr.c_rs2;
endgroup : cg_css


covergroup cg_ciw(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_immiw: coverpoint instr.c_immiw;
  cp_c_rdp: coverpoint instr.c_rdp;
endgroup : cg_ciw


covergroup cg_cl(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_imml: coverpoint instr.c_imml;
  cp_c_rs1p: coverpoint instr.c_rs1p;
  cp_c_rdp: coverpoint instr.c_rdp;
endgroup : cg_cl


covergroup cg_cs(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_imms: coverpoint instr.c_imms;
  cp_c_rs1p: coverpoint instr.c_rs1p;
  cp_c_rs2p: coverpoint instr.c_rs2p;
endgroup : cg_cs


covergroup cg_ca(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_rdprs1p: coverpoint instr.c_rdprs1p;
  cp_c_rs2p: coverpoint instr.c_rs2p;
endgroup : cg_ca


covergroup cg_cb(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_immb: coverpoint instr.c_immb;
  cp_c_rs1p: coverpoint instr.c_rs1p;
endgroup : cg_cb


covergroup cg_cj(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_immj: coverpoint instr.c_immj;
endgroup : cg_cj


class uvma_isacov_cov_model_c extends uvm_component;

  `uvm_component_utils(uvma_isacov_cov_model_c)

  // Objects
  uvma_isacov_cfg_c cfg;

  // Covergroups
  //32I:
  cg_rtype slli_cg;  // TODO own cg?
  cg_rtype srli_cg;  // TODO own cg?
  cg_rtype srai_cg;  // TODO own cg?
  cg_rtype add_cg;
  cg_rtype sub_cg;
  cg_rtype sll_cg;
  cg_rtype slt_cg;
  cg_rtype sltu_cg;
  cg_rtype xor_cg;
  cg_rtype srl_cg;
  cg_rtype sra_cg;
  cg_rtype or_cg;
  cg_rtype and_cg;
  cg_itype jalr_cg;
  cg_itype lb_cg;
  cg_itype lh_cg;
  cg_itype lw_cg;
  cg_itype lbu_cg;
  cg_itype lhu_cg;
  cg_itype addi_cg;
  cg_itype slti_cg;
  cg_itype sltiu_cg;
  cg_itype xori_cg;
  cg_itype ori_cg;
  cg_itype andi_cg;
  cg_itype fence_cg;  // TODO own cg?
  cg_itype ecall_cg;  // TODO own cg?
  cg_itype ebreak_cg;  // TODO own cg?
  cg_stype sb_cg;
  cg_stype sh_cg;
  cg_stype sw_cg;
  cg_btype beq_cg;
  cg_btype bne_cg;
  cg_btype blt_cg;
  cg_btype bge_cg;
  cg_btype bltu_cg;
  cg_btype bgeu_cg;
  cg_utype lui_cg;
  cg_utype auipc_cg;
  cg_jtype jal_cg;
  //32M:
  cg_rtype mul_cg;
  cg_rtype mulh_cg;
  cg_rtype mulhsu_cg;
  cg_rtype mulhu_cg;
  cg_rtype div_cg;
  cg_rtype divu_cg;
  cg_rtype rem_cg;
  cg_rtype remu_cg;
  //32C:
  cg_ciw c_addi4spn_cg;
  cg_cl c_lw_cg;
  cg_cs c_sw_cg;
  cg_ci c_addi_cg;
  cg_cj c_jal_cg;
  cg_ci c_li_cg;
  cg_ci c_addi16sp_cg;
  cg_ci c_lui_cg;  // TODO need "cg_ci_lui" specialization?
  cg_cb c_srli_cg;
  cg_cb c_srai_cg;
  cg_cb c_andi_cg;
  cg_ca c_sub_cg;
  cg_ca c_xor_cg;
  cg_ca c_or_cg;
  cg_ca c_and_cg;
  cg_cj c_j_cg;
  cg_cb c_beqz_cg;
  cg_cb c_bnez_cg;
  cg_ci c_slli_cg;
  cg_ci c_lwsp_cg;
  cg_cr c_jr_cg;
  cg_cr c_mv_cg;
  cg_cr c_ebreak_cg;  // TODO should have own cg?
  cg_cr c_jalr_cg;
  cg_cr c_add_cg;
  cg_css c_swsp_cg;
  //Zicsr:
  cg_itype csrrw_cg;  // TODO define type for named "csr" imm
  cg_itype csrrs_cg;
  cg_itype csrrc_cg;
  cg_itype csrrwi_cg;
  cg_itype csrrsi_cg;
  cg_itype csrrci_cg;
  //Zifence_i:
  cg_itype fence_i_cg;  // TODO own cg? (not itype)

  // TLM
  uvm_tlm_analysis_fifo #(uvma_isacov_mon_trn_c) mon_trn_fifo;

  extern function new(string name = "uvma_isacov_cov_model", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern function void sample (uvma_isacov_instr_c instr);

endclass : uvma_isacov_cov_model_c


function uvma_isacov_cov_model_c::new(string name = "uvma_isacov_cov_model", uvm_component parent = null);

  super.new(name, parent);

endfunction : new


function void uvma_isacov_cov_model_c::build_phase(uvm_phase phase);

  super.build_phase(phase);

  void'(uvm_config_db#(uvma_isacov_cfg_c)::get(this, "", "cfg", cfg));
  if (!cfg) begin
    `uvm_fatal("CFG", "Configuration handle is null")
  end

  if (cfg.enabled && cfg.cov_model_enabled) begin
    if (cfg.ext_i_enabled) begin
      lui_cg    = new("lui_cg");
      auipc_cg  = new("auipc_cg");
      jal_cg    = new("jal_cg");
      jalr_cg   = new("jalr_cg");

      beq_cg    = new("beq_cg");
      bne_cg    = new("bne_cg");
      blt_cg    = new("blt_cg");
      bge_cg    = new("bge_cg");
      bltu_cg   = new("bltu_cg");
      bgeu_cg   = new("bgeu_cg");

      lb_cg     = new("lb_cg");
      lh_cg     = new("lh_cg");
      lw_cg     = new("lw_cg");
      lbu_cg    = new("lbu_cg");
      lhu_cg    = new("lhu_cg");
      sb_cg     = new("sb_cg");
      sh_cg     = new("sh_cg");
      sw_cg     = new("sw_cg");

      addi_cg   = new("addi_cg");
      slti_cg   = new("slti_cg");
      sltiu_cg  = new("sltiu_cg");
      xori_cg   = new("xori_cg");
      ori_cg    = new("ori_cg");
      andi_cg   = new("andi_cg");
      slli_cg   = new("slli_cg");
      srli_cg   = new("srli_cg");
      srai_cg   = new("srai_cg");

      add_cg    = new("add_cg");
      sub_cg    = new("sub_cg");
      sll_cg    = new("sll_cg");
      slt_cg    = new("slt_cg");
      sltu_cg   = new("sltu_cg");
      xor_cg    = new("xor_cg");
      srl_cg    = new("srl_cg");
      sra_cg    = new("sra_cg");
      or_cg     = new("or_cg");
      and_cg    = new("and_cg");

      fence_cg  = new("fence_cg");
      ecall_cg  = new("ecall_cg");
      ebreak_cg = new("ebreak_cg");
    end
    if (cfg.ext_m_enabled) begin
      mul_cg    = new("mul_cg");
      mulh_cg   = new("mulh_cg");
      mulhsu_cg = new("mulhsu_cg");
      mulhu_cg  = new("mulhu_cg");
      div_cg    = new("div_cg");
      divu_cg   = new("divu_cg");
      rem_cg    = new("rem_cg");
      remu_cg   = new("remu_cg");
    end
    if (cfg.ext_c_enabled) begin
      c_addi4spn_cg = new("c_addi4spn_cg");
      c_lw_cg       = new("c_lw_cg");
      c_sw_cg       = new("c_sw_cg");

      c_addi_cg     = new("c_addi_cg");
      c_jal_cg      = new("c_jal_cg");
      c_li_cg       = new("c_li_cg");
      c_addi16sp_cg = new("c_addi16sp_cg");
      c_lui_cg      = new("c_lui_cg");
      c_srli_cg     = new("c_srli_cg");
      c_srai_cg     = new("c_srai_cg");
      c_andi_cg     = new("c_andi_cg");
      c_sub_cg      = new("c_sub_cg");
      c_xor_cg      = new("c_xor_cg");
      c_or_cg       = new("c_or_cg");
      c_and_cg      = new("c_and_cg");
      c_j_cg        = new("c_j_cg");
      c_beqz_cg     = new("c_beqz_cg");
      c_bnez_cg     = new("c_bnez_cg");

      c_slli_cg     = new("c_slli_cg");
      c_lwsp_cg     = new("c_lwsp_cg");
      c_jr_cg       = new("c_jr_cg");
      c_mv_cg       = new("c_mv_cg");
      c_ebreak_cg   = new("c_ebreak_cg");
      c_jalr_cg     = new("c_jalr_cg");
      c_add_cg      = new("c_add_cg");
      c_swsp_cg     = new("c_swsp_cg");
    end
    if (cfg.ext_zicsr_enabled) begin
      csrrw_cg  = new("csrrw_cg");
      csrrs_cg  = new("csrrs_cg");
      csrrc_cg  = new("csrrc_cg");
      csrrwi_cg = new("csrrwi_cg");
      csrrsi_cg = new("csrrsi_cg");
      csrrci_cg = new("csrrci_cg");
    end
    if (cfg.ext_zifencei_enabled) begin
      fence_i_cg = new("fence_i_cg");
    end
  end

  mon_trn_fifo = new("mon_trn_fifo", this);

endfunction : build_phase


task uvma_isacov_cov_model_c::run_phase(uvm_phase phase);

  super.run_phase(phase);
  
  forever begin
    uvma_isacov_mon_trn_c mon_trn;

    mon_trn_fifo.get(mon_trn);
    if (cfg.enabled && cfg.cov_model_enabled) begin
      sample (mon_trn.instr);
    end
  end

endtask : run_phase


function void uvma_isacov_cov_model_c::sample (uvma_isacov_instr_c instr);

  logic have_sampled = 0;

  if (!have_sampled && cfg.ext_i_enabled) begin
    have_sampled = 1;
    case (instr.name)
      LUI:   lui_cg.sample(instr);
      AUIPC: auipc_cg.sample(instr);
      JAL:   jal_cg.sample(instr);
      JALR:  jalr_cg.sample(instr);

      BEQ:  beq_cg.sample(instr);
      BNE:  bne_cg.sample(instr);
      BLT:  blt_cg.sample(instr);
      BGE:  bge_cg.sample(instr);
      BLTU: bltu_cg.sample(instr);
      BGEU: bgeu_cg.sample(instr);

      LB:  lb_cg.sample(instr);
      LH:  lh_cg.sample(instr);
      LW:  lw_cg.sample(instr);
      LBU: lbu_cg.sample(instr);
      LHU: lhu_cg.sample(instr);
      SB:  sb_cg.sample(instr);
      SH:  sh_cg.sample(instr);
      SW:  sw_cg.sample(instr);

      ADDI:  addi_cg.sample(instr);
      SLTI:  slti_cg.sample(instr);
      SLTIU: sltiu_cg.sample(instr);
      XORI:  xori_cg.sample(instr);
      ORI:   ori_cg.sample(instr);
      ANDI:  andi_cg.sample(instr);
      SLLI:  slli_cg.sample(instr);
      SRLI:  srli_cg.sample(instr);
      SRAI:  srai_cg.sample(instr);

      ADD:  add_cg.sample(instr);
      SUB:  sub_cg.sample(instr);
      SLL:  sll_cg.sample(instr);
      SLT:  slt_cg.sample(instr);
      SLTU: sltu_cg.sample(instr);
      XOR:  xor_cg.sample(instr);
      SRL:  srl_cg.sample(instr);
      SRA:  sra_cg.sample(instr);
      OR:   or_cg.sample(instr);
      AND:  and_cg.sample(instr);

      FENCE:  fence_cg.sample(instr);
      ECALL:  ecall_cg.sample(instr);
      EBREAK: ebreak_cg.sample(instr);

      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && cfg.ext_m_enabled) begin
    have_sampled = 1;
    case (instr.name)
      MUL:     mul_cg.sample(instr);
      MULH:    mulh_cg.sample(instr);
      MULHSU:  mulhsu_cg.sample(instr);
      MULHU:   mulhu_cg.sample(instr);
      DIV:     div_cg.sample(instr);
      DIVU:    divu_cg.sample(instr);
      REM:     rem_cg.sample(instr);
      REMU:    remu_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && cfg.ext_c_enabled) begin
    have_sampled = 1;
    case (instr.name)
      C_ADDI4SPN: c_addi4spn_cg.sample(instr);
      C_LW:       c_lw_cg.sample(instr);
      C_SW:       c_sw_cg.sample(instr);

      C_ADDI:     c_addi_cg.sample(instr);
      C_JAL:      c_jal_cg.sample(instr);
      C_LI:       c_li_cg.sample(instr);
      C_ADDI16SP: c_addi16sp_cg.sample(instr);
      C_LUI:      c_lui_cg.sample(instr);
      C_SRLI:     c_srli_cg.sample(instr);
      C_SRAI:     c_srai_cg.sample(instr);
      C_ANDI:     c_andi_cg.sample(instr);
      C_SUB:      c_sub_cg.sample(instr);
      C_XOR:      c_xor_cg.sample(instr);
      C_OR:       c_or_cg.sample(instr);
      C_AND:      c_and_cg.sample(instr);
      C_J:        c_j_cg.sample(instr);
      C_BEQZ:     c_beqz_cg.sample(instr);
      C_BNEZ:     c_bnez_cg.sample(instr);

      C_SLLI:   c_slli_cg.sample(instr);
      C_LWSP:   c_lwsp_cg.sample(instr);
      C_JR:     c_jr_cg.sample(instr);
      C_MV:     c_mv_cg.sample(instr);
      C_EBREAK: c_ebreak_cg.sample(instr);
      C_JALR:   c_jalr_cg.sample(instr);
      C_ADD:    c_add_cg.sample(instr);
      C_SWSP:   c_swsp_cg.sample(instr);

      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && cfg.ext_zicsr_enabled) begin
    have_sampled = 1;
    case (instr.name)
      CSRRW:   csrrw_cg.sample(instr);
      CSRRS:   csrrs_cg.sample(instr);
      CSRRC:   csrrc_cg.sample(instr);
      CSRRWI:  csrrwi_cg.sample(instr);
      CSRRSI:  csrrsi_cg.sample(instr);
      CSRRCI:  csrrci_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && cfg.ext_zifencei_enabled) begin
    have_sampled = 1;
    case (instr.name)
      FENCE_I: fence_i_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled) begin
    $display("TODO error if no match found");
  end

endfunction
