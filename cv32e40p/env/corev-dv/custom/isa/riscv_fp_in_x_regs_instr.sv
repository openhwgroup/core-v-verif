/*
 * Copyright 2023 Dolphin Design
 * SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 */

class riscv_fp_in_x_regs_instr extends riscv_instr;

  // adds rs3 integer registers for fp in x instructions that needs this
  rand riscv_reg_t rs3;
  rand f_rounding_mode_t rm;
  rand bit use_rounding_mode_from_instr;

  bit              has_rs1 = 1'b1;
  bit              has_rs2 = 1'b1;
  bit              has_rs3 = 1'b0;
  bit              has_rd  = 1'b1;

  `uvm_object_utils(riscv_fp_in_x_regs_instr)
  `uvm_object_new

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    case (format)
      I_FORMAT:
        if (instr_name inside {FCVT_W_S, FCVT_WU_S, FCVT_L_S, FCVT_LU_S, FCVT_L_D, FCVT_LU_D,
                                        FCVT_W_D, FCVT_WU_D}) begin
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs1.name());
        end else if (instr_name inside {FCVT_S_W, FCVT_S_WU,
                                        FCVT_S_L, FCVT_D_L, FCVT_S_LU, FCVT_D_W,
                                        FCVT_D_LU, FCVT_D_WU}) begin
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs1.name());
        end else begin
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs1.name());
        end
      R_FORMAT:
        if (category == COMPARE) begin
          asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), rs1.name(), rs2.name());
        end else if (instr_name inside {FCLASS_S, FCLASS_D}) begin
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs1.name());
        end else begin
          asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), rs1.name(), rs2.name());
        end
      R4_FORMAT:
        asm_str = $sformatf("%0s%0s, %0s, %0s, %0s", asm_str, rd.name(), rs1.name(),
                                                     rs2.name(), rs3.name());
      CL_FORMAT:
        asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rd.name(), get_imm(), rs1.name());
      CS_FORMAT:
        asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rs2.name(), get_imm(), rs1.name());
      default:
        `uvm_fatal(`gfn, $sformatf("Unsupported floating point format: %0s", format.name()))
    endcase
    if ((category == ARITHMETIC) && use_rounding_mode_from_instr &&
        !(instr_name inside {FMIN_S, FMAX_S, FMIN_D, FMAX_D, FCLASS_S, FCLASS_D,
                             FCVT_D_S, FCVT_D_W, FCVT_D_WU,
                             FSGNJ_S, FSGNJN_S, FSGNJX_S, FSGNJ_D, FSGNJN_D, FSGNJX_D})) begin
      if (rm != DYN) asm_str = {asm_str, ", ", rm.name()};
    end
    if(comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction

  virtual function void do_copy(uvm_object rhs);
    riscv_fp_in_x_regs_instr rhs_;
    super.copy(rhs);
    assert($cast(rhs_, rhs));
    this.rs3     = rhs_.rs3;
    this.rs2     = rhs_.rs2;
    this.rs1     = rhs_.rs1;
    this.rd      = rhs_.rd;
    this.has_rs3 = rhs_.has_rs3;
    this.has_rs2 = rhs_.has_rs2;
    this.has_rs1 = rhs_.has_rs1;
    this.has_rd  = rhs_.has_rd;
  endfunction : do_copy

  virtual function void set_rand_mode();
    case (format)
      I_FORMAT: begin
        has_rs2 = 1'b0;
      end
      R_FORMAT:
        if (instr_name inside {FCLASS_S, FCLASS_D}) begin
          has_rs2 = 1'b0;
        end
      R4_FORMAT: begin
        has_rs3 = 1'b1;
      end
      default: `uvm_info(`gfn, $sformatf("Unsupported format %0s", format.name()), UVM_LOW)
    endcase
  endfunction

  function void pre_randomize();
    super.pre_randomize();
    rs3.rand_mode(has_rs3);
  endfunction

  // coverage related functons
  virtual function void update_src_regs(string operands[$]);
    if(category inside {LOAD, CSR}) begin
      super.update_src_regs(operands);
      return;
    end
    case(format)
      I_FORMAT: begin
        // TODO ovpsim has an extra operand rte as below
        // fcvt.d.s rs1,fs4,rte
        //`DV_CHECK_FATAL(operands.size() == 2)
        if (has_rs1) begin
          rs1 = get_gpr(operands[1]);
          rs1_value = get_gpr_state(operands[1]);
        end else if (has_rs1) begin
          rs1 = get_gpr(operands[1]);
          rs1_value = get_gpr_state(operands[1]);
        end
      end
      S_FORMAT: begin
        `DV_CHECK_FATAL(operands.size() == 3)
        // FSW rs2 is fp
        rs2 = get_gpr(operands[0]);
        rs2_value = get_gpr_state(operands[0]);
        rs1 = get_gpr(operands[1]);
        rs1_value = get_gpr_state(operands[1]);
        get_val(operands[2], imm);
      end
      R_FORMAT: begin
        // convert Pseudoinstructions for ovpsim
        // fmv.s rd, rs -> fsgnj.s rd, rs, rs
        if (operands.size() == 2 && instr_name inside {FSGNJ_S, FSGNJX_S, FSGNJN_S, FSGNJ_D,
                                                       FSGNJX_D, FSGNJN_D}) begin
          operands.push_back(operands[$]);
        end

        if (has_rs2 || category == CSR) begin
          `DV_CHECK_FATAL(operands.size() == 3)
        end else begin
          `DV_CHECK_FATAL(operands.size() == 2)
        end
        if(category != CSR) begin
          rs1 = get_gpr(operands[1]);
          rs1_value = get_gpr_state(operands[1]);
          if (has_rs2) begin
            rs2 = get_gpr(operands[2]);
            rs2_value = get_gpr_state(operands[2]);
          end
        end
      end
      R4_FORMAT: begin
        `DV_CHECK_FATAL(operands.size() == 4)
        rs1 = get_gpr(operands[1]);
        rs1_value = get_gpr_state(operands[1]);
        rs2 = get_gpr(operands[2]);
        rs2_value = get_gpr_state(operands[2]);
        rs3 = get_gpr(operands[3]);
        rs3_value = get_gpr_state(operands[3]);
      end
      default: `uvm_fatal(`gfn, $sformatf("Unsupported format %0s", format))
    endcase
  endfunction : update_src_regs

  virtual function void update_dst_regs(string reg_name, string val_str);
    get_val(val_str, gpr_state[reg_name], .hex(1));
    if (has_rd) begin
      rd = get_gpr(reg_name);
      rd_value = get_gpr_state(reg_name);
    end else if (has_rd) begin
      rd = get_gpr(reg_name);
      rd_value = get_gpr_state(reg_name);
    end
  endfunction : update_dst_regs

  virtual function riscv_reg_t get_gpr(input string str);
    str = str.toupper();
    if (!uvm_enum_wrapper#(riscv_reg_t)::from_name(str, get_gpr)) begin
      `uvm_fatal(`gfn, $sformatf("Cannot convert %0s to GPR", str))
    end
  endfunction : get_gpr

  virtual function void pre_sample();
    super.pre_sample();

    // for single precision sign bit is bit 31, upper 32 bits are all 1s
    // for double precision, it's 63
    if (group inside {RV32ZFINX}) begin
      rs1_sign = get_fp_operand_sign(rs1_value, 31);
      rs2_sign = get_fp_operand_sign(rs2_value, 31);
      rs3_sign = get_fp_operand_sign(rs3_value, 31);
      rd_sign = get_fp_operand_sign(rd_value, 31);
    end else if (instr_name == FCVT_S_D) begin
      rs1_sign = get_fp_operand_sign(rs1_value, 63);
      rd_sign = get_fp_operand_sign(rd_value, 31);
    end else if (instr_name == FCVT_D_S) begin
      rs1_sign = get_fp_operand_sign(rs1_value, 31);
      rd_sign = get_fp_operand_sign(rd_value, 63);
    end else begin
      rs1_sign = get_fp_operand_sign(rs1_value, 63);
      rs2_sign = get_fp_operand_sign(rs2_value, 63);
      rs3_sign = get_fp_operand_sign(rs3_value, 63);
      rd_sign = get_fp_operand_sign(rd_value, 63);
    end
  endfunction : pre_sample

  virtual function operand_sign_e get_fp_operand_sign(bit [XLEN-1:0] value, int idx);
    if (value[idx]) begin
      return NEGATIVE;
    end else begin
      return POSITIVE;
    end
  endfunction

  virtual function void check_hazard_condition(riscv_instr pre_instr);
    riscv_fp_in_x_regs_instr pre_fp_instr;
    super.check_hazard_condition(pre_instr);
    if ($cast(pre_fp_instr, pre_instr) && pre_fp_instr.has_rd) begin
      if ((has_rs1 && (rs1 == pre_fp_instr.rd)) || (has_rs2 && (rs2 == pre_fp_instr.rd))
          || (has_rs3 && (rs3 == pre_fp_instr.rd))) begin
        gpr_hazard = RAW_HAZARD;
      end else if (has_rd && (rd == pre_fp_instr.rd)) begin
        gpr_hazard = WAW_HAZARD;
      end else if (has_rd && ((pre_fp_instr.has_rs1 && (pre_fp_instr.rs1 == rd)) ||
                              (pre_fp_instr.has_rs2 && (pre_fp_instr.rs2 == rd)) ||
                              (pre_fp_instr.has_rs3 && (pre_fp_instr.rs3 == rd)))) begin
        gpr_hazard = WAR_HAZARD;
      end else begin
        gpr_hazard = NO_HAZARD;
      end
    end
  endfunction
endclass
