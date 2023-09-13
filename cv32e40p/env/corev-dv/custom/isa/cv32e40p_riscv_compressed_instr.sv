/*
 * Copyright 2020 Google LLC
 * Copyright 2023 OpenHW Group
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

class cv32e40p_riscv_compressed_instr extends riscv_compressed_instr;

  rand riscv_fpr_t fs2;
  rand riscv_fpr_t fd;

  bit has_fs2 = 1'b0;
  bit has_fd  = 1'b0;

  constraint rvc_csr_c {
    //  Registers specified by the three-bit rs1’, rs2’, and rd’
    if (format inside {CIW_FORMAT, CL_FORMAT, CS_FORMAT, CB_FORMAT, CA_FORMAT}) {
      if (has_rs1) {
        rs1 inside {[S0:A5]};
      }
      if (has_rs2) {
        rs2 inside {[S0:A5]};
      }
      if (has_rd) {
        rd inside {[S0:A5]};
      }
      if (has_fs2) {
        fs2 inside {[FS0:FA5]};
      }
      if (has_fd) {
        fd inside {[FS0:FA5]};
      }
    }
    // C_ADDI16SP is only valid when rd == SP
    if (instr_name == C_ADDI16SP) {
      rd  == SP;
    }
    if (instr_name inside {C_JR, C_JALR}) {
      rs2 == ZERO;
      rs1 != ZERO;
    }
  }

  `uvm_object_utils(cv32e40p_riscv_compressed_instr)

  function new(string name = "");
    super.new(name);
    fs2 = FS0;
    fd  = FS0;
  endfunction : new

  virtual function void set_imm_len();
    super.set_imm_len();
    if (instr_name inside {C_FSW, C_FLW, C_FLWSP, C_FSWSP}) begin
      imm_align = 2;
    end
  endfunction : set_imm_len

  virtual function void do_copy(uvm_object rhs);
    cv32e40p_riscv_compressed_instr rhs_;
    super.copy(rhs);
    assert($cast(rhs_, rhs));
    this.fs2        = rhs_.fs2;
    this.fd         = rhs_.fd;
    this.has_fs2    = rhs_.has_fs2;
    this.has_fd     = rhs_.has_fd;
  endfunction : do_copy

  virtual function void set_rand_mode();
    case (format) inside
      CR_FORMAT : begin
        if (category == JUMP) begin
          has_rd = 1'b0;
        end else begin
          has_rs1 = 1'b0;
        end
        has_imm = 1'b0;
      end
      CSS_FORMAT : begin
        has_rs1 = 1'b0;
        has_rd  = 1'b0;
        if (instr_name == C_FSWSP) has_fs2 = 1'b1;
      end
      CL_FORMAT: begin
        has_rs2 = 1'b0;
        if (instr_name == C_FLW) has_fd = 1'b1;
      end
      CS_FORMAT : begin
        has_rd = 1'b0;
        if (instr_name == C_FSW) has_fs2 = 1'b1;
      end
      CA_FORMAT: begin
        has_rs1 = 1'b0;
        has_imm = 1'b0;
      end
      CI_FORMAT, CIW_FORMAT: begin
        has_rs1 = 1'b0;
        has_rs2 = 1'b0;
        if (instr_name == C_FLWSP) has_fd = 1'b1;
      end
      CJ_FORMAT: begin
        has_rs1 = 1'b0;
        has_rs2 = 1'b0;
        has_rd  = 1'b0;
      end
      CB_FORMAT: begin
        if (instr_name != C_ANDI) has_rd = 1'b0;
        has_rs2 = 1'b0;
      end
    endcase
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);

    // workaround: ensure all floating compressed have random fd and fs within a stream
    if (instr_name inside {C_FSW, C_FLW}) begin
      std::randomize(fs2) with { fs2 inside {[FS0:FA5]}; };
    end
    if (instr_name inside {C_FSW, C_FLW, C_FSWSP, C_FLWSP}) begin
      std::randomize(fd) with { fd inside {[FS0:FA5]}; };
    end

    if (category != SYSTEM) begin
      case(format)
        CI_FORMAT, CIW_FORMAT:
          if (instr_name == C_NOP)
            asm_str = "c.nop";
          else if (instr_name == C_ADDI16SP)
            asm_str = $sformatf("%0ssp, %0s", asm_str, get_imm());
          else if (instr_name == C_ADDI4SPN)
            asm_str = $sformatf("%0s%0s, sp, %0s", asm_str, rd.name(), get_imm());
          else if (instr_name inside {C_LDSP, C_LWSP, C_LQSP})
            asm_str = $sformatf("%0s%0s, %0s(sp)", asm_str, rd.name(), get_imm());
          else if (instr_name == C_FLWSP)
            asm_str = $sformatf("%0s%0s, %0s(sp)", asm_str, fd.name(), get_imm());
          else
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), get_imm());
        CL_FORMAT:
            if (instr_name == C_FLW)
              asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fd.name(), get_imm(), rs1.name());
            else
              asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rd.name(), get_imm(), rs1.name());
        CS_FORMAT:
          if (category == STORE) begin
            if (instr_name == C_FSW)
              asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fs2.name(), get_imm(), rs1.name());
            else 
              asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rs2.name(), get_imm(), rs1.name());
          end
          else
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rs1.name(), rs2.name());
        CA_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs2.name());
        CB_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rs1.name(), get_imm());
        CSS_FORMAT:
          if (category == STORE) begin
            if (instr_name == C_FSWSP)
              asm_str = $sformatf("%0s%0s, %0s(sp)", asm_str, fs2.name(), get_imm());
            else
              asm_str = $sformatf("%0s%0s, %0s(sp)", asm_str, rs2.name(), get_imm());
          end
          else
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rs2.name(), get_imm());
        CR_FORMAT:
          if (instr_name inside {C_JR, C_JALR}) begin
            asm_str = $sformatf("%0s%0s", asm_str, rs1.name());
          end else begin
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs2.name());
          end
        CJ_FORMAT:
          asm_str = $sformatf("%0s%0s", asm_str, get_imm());
        default: `uvm_info(`gfn, $sformatf("Unsupported format %0s", format.name()), UVM_LOW)
      endcase
    end else begin
      // For EBREAK,C.EBREAK, making sure pc+4 is a valid instruction boundary
      // This is needed to resume execution from epc+4 after ebreak handling
      if (instr_name == C_EBREAK) begin
        asm_str = "c.ebreak;c.nop;";
      end
    end
    if (comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction : convert2asm

  // Convert the instruction to assembly code
  virtual function string convert2bin(string prefix = "");
    string binary;
    case (instr_name) inside
      C_ADDI4SPN:
        binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[9:6],
                                   imm[2], imm[3], get_c_gpr(rd), get_c_opcode()});
      C_LQ:
        binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[8],
                                   get_c_gpr(rs1), imm[7:6], get_c_gpr(rd), get_c_opcode()});
      C_FLD, C_LD:
        binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                   imm[7:6], get_c_gpr(rd), get_c_opcode()});
      C_LW:
        binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                   imm[2], imm[6], get_c_gpr(rd), get_c_opcode()});
      C_FLW:
        binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                   imm[2], imm[6], get_c_fpr(fd), get_c_opcode()});
      C_SQ:
        binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[8],
                                   get_c_gpr(rs1), imm[7:6], get_c_gpr(rs2), get_c_opcode()});
      C_FSD, C_SD:
        binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                   imm[7:6], get_c_gpr(rs2), get_c_opcode()});
      C_SW:
        binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                   imm[2], imm[6], get_c_gpr(rs2), get_c_opcode()});
      C_FSW:
        binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                   imm[2], imm[6], get_c_fpr(fs2), get_c_opcode()});
      C_NOP, C_ADDI, C_LI, C_ADDIW:
        binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:0], get_c_opcode()});
      C_JAL, C_J:
        binary = $sformatf("%4h", {get_func3(), imm[11], imm[4], imm[9:8],
                                   imm[10], imm[6], imm[7], imm[3:1], imm[5], get_c_opcode()});
      C_ADDI16SP:
        binary = $sformatf("%4h", {get_func3(), imm[9], 5'b00010,
                                   imm[4], imm[6], imm[8:7], imm[5], get_c_opcode()});
      C_LUI:
        binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:0], get_c_opcode()});
      C_SRLI:
        binary = $sformatf("%4h", {get_func3(), imm[5],
                                   2'b0, get_c_gpr(rd), imm[4:0], get_c_opcode()});
      C_SRLI64:
        binary = $sformatf("%4h", {get_func3(), 3'b0, get_c_gpr(rd), 5'b0, get_c_opcode()});
      C_SRAI:
        binary = $sformatf("%4h", {get_func3(), imm[5],
                                   2'b01, get_c_gpr(rd), imm[4:0], get_c_opcode()});
      C_SRAI64:
        binary = $sformatf("%4h", {get_func3(), 3'b001,
                                   get_c_gpr(rd), 5'b0, get_c_opcode()});
      C_ANDI:
        binary = $sformatf("%4h", {get_func3(), imm[5],
                                   2'b10, get_c_gpr(rd), imm[4:0], get_c_opcode()});
      C_SUB:
        binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                   2'b00, get_c_gpr(rs2), get_c_opcode()});
      C_XOR:
        binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                   2'b01, get_c_gpr(rs2), get_c_opcode()});
      C_OR:
        binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                   2'b10, get_c_gpr(rs2), get_c_opcode()});
      C_AND:
        binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                   2'b11, get_c_gpr(rs2), get_c_opcode()});
      C_SUBW:
        binary = $sformatf("%4h", {get_func3(), 3'b111, get_c_gpr(rd),
                                   2'b00, get_c_gpr(rs2), get_c_opcode()});
      C_ADDW:
        binary = $sformatf("%4h", {get_func3(), 3'b111, get_c_gpr(rd),
                                   2'b01, get_c_gpr(rs2), get_c_opcode()});
      C_BEQZ, C_BNEZ:
        binary = $sformatf("%4h", {get_func3(), imm[8], imm[4:3],
                                   get_c_gpr(rs1), imm[7:6], imm[2:1], imm[5], get_c_opcode()});
      C_SLLI:
        binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:0], get_c_opcode()});
      C_SLLI64:
        binary = $sformatf("%4h", {get_func3(), 1'b0, rd, 5'b0, get_c_opcode()});
      C_FLDSP, C_LDSP:
        binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:3], imm[8:6], get_c_opcode()});
      C_LQSP:
        binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4], imm[9:6], get_c_opcode()});
      C_LWSP:
        binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:2], imm[7:6], get_c_opcode()});
      C_FLWSP:
        binary = $sformatf("%4h", {get_func3(), imm[5], fd, imm[4:2], imm[7:6], get_c_opcode()});
      C_JR:
        binary = $sformatf("%4h", {get_func3(), 1'b0, rs1, 5'b0, get_c_opcode()});
      C_MV:
        binary = $sformatf("%4h", {get_func3(), 1'b0, rd, rs2, get_c_opcode()});
      C_EBREAK:
        binary = $sformatf("%4h", {get_func3(), 1'b1, 10'b0, get_c_opcode()});
      C_JALR:
        binary = $sformatf("%4h", {get_func3(), 1'b1, 10'b0, get_c_opcode()});
      C_ADD:
        binary = $sformatf("%4h", {get_func3(), 1'b1, rd, rs2, get_c_opcode()});
      C_FSDSP, C_SDSP:
        binary = $sformatf("%4h", {get_func3(), imm[5:3], imm[8:6], rs2, get_c_opcode()});
      C_SQSP:
        binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[9:6], rs2, get_c_opcode()});
      C_SWSP:
        binary = $sformatf("%4h", {get_func3(), imm[5:2], imm[7:6], rs2, get_c_opcode()});
      C_FSWSP:
        binary = $sformatf("%4h", {get_func3(), imm[5:2], imm[7:6], fs2, get_c_opcode()});
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
    return {prefix, binary};
  endfunction : convert2bin

  // Get RVFC register name for CL, CS format
  function bit [2:0] get_c_fpr(riscv_fpr_t fpr);
    return fpr[2:0];
  endfunction

endclass : cv32e40p_riscv_compressed_instr
