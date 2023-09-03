/*
 * Copyright 2020 Google LLC
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
 *
 *
 * Copyright 2023 OpenHW Group
 * Copyright 2023 Dolphin Design
 *
 * SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 */

class cv32e40p_riscv_compressed_instr extends riscv_compressed_instr;

  rand riscv_fpr_t fs1;
  rand riscv_fpr_t fs2;
  rand riscv_fpr_t fd;
  rand bit[4:0]  reg_idx_fs2; //FIXME : dd-vaibhavjain
  rand bit[4:0]  reg_idx_fd; //FIXME : dd-vaibhavjain

  //FIXME: dd-vaibhavjain. Remove after toolchain fix
  constraint rv32fc_reg_idx_temp_c {
    if (instr_name == C_FLW) {
      reg_idx_fd inside {[8:15]};
    }
    if (instr_name == C_FSW) {
      reg_idx_fs2 inside {[8:15]};
    }
  }

  constraint rvc_csr_c {
    //  Registers specified by the three-bit rs1’, rs2’, and rd’
    if (format inside {CIW_FORMAT, CL_FORMAT, CS_FORMAT, CB_FORMAT, CA_FORMAT}) {
      if (has_rs1) {
        rs1 inside {[S0:A5]};
        fs1 inside {[S0:A5]};
      }
      if (has_rs2) {
        rs2 inside {[S0:A5]};
        fs2 inside {[S0:A5]};
      }
      if (has_rd) {
        rd inside {[S0:A5]};
        fd inside {[S0:A5]};
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
    fs1 = FS0;
    fs2 = FS0;
    fd  = FS0;
  endfunction : new

  virtual function void set_imm_len();
    if (format inside {CI_FORMAT, CSS_FORMAT}) begin
      imm_len = 6;
    end else if (format inside {CL_FORMAT, CS_FORMAT}) begin
      imm_len = 5;
    end else if (format inside {CJ_FORMAT}) begin
      imm_len = 11;
    end else if (format inside {CB_FORMAT}) begin
      if (instr_name == C_ANDI) begin
        imm_len = 6;
      end else begin
        imm_len = 7;
      end
    end else if (format inside {CB_FORMAT, CIW_FORMAT}) begin
      imm_len = 8;
    end
    if (instr_name inside {C_SQ, C_LQ, C_LQSP, C_SQSP, C_ADDI16SP}) begin
      imm_align = 4;
    end else if (instr_name inside {C_SD, C_LD, C_LDSP, C_SDSP}) begin
      imm_align = 3;
    end else if (instr_name inside {C_SW, C_LW, C_LWSP, C_SWSP, C_ADDI4SPN, C_FSW, C_FLW, C_FLWSP, C_FSWSP}) begin
      imm_align = 2;
    end else if (instr_name inside {C_LUI}) begin
      imm_align = 12;
    end else if (instr_name inside {C_J, C_JAL, C_BNEZ, C_BEQZ}) begin
      imm_align = 1;
    end
  endfunction : set_imm_len

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);

    std::randomize(reg_idx_fs2) with { if (instr_name == C_FSW) {
                                         reg_idx_fs2 inside {[8:15]};
                                       }
                                     };  //FIXME : dd-vaibhavjain

    std::randomize(reg_idx_fd) with { if (instr_name == C_FLW) {
                                        reg_idx_fd inside {[8:15]};
                                      }
                                    };  //FIXME : dd-vaibhavjain


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
          else if (instr_name inside {C_FLWSP})
            //asm_str = $sformatf("%0s%0s, %0s(sp)", asm_str, fd.name(), get_imm());
            asm_str = $sformatf("%0s f%0d, %0s(sp)", asm_str, reg_idx_fd, get_imm());  //FIXME : dd-vaibhavjain. revert temp wrd after toolchain fix
          else
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), get_imm());
        CL_FORMAT:
          if (instr_name == C_FLW)
            //asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fd.name(), get_imm(), rs1.name());
            asm_str = $sformatf("%0s f%0d, %0s(%0s)", asm_str, reg_idx_fd, get_imm(), rs1.name());  //FIXME : dd-vaibhavjain. revert temp wrd after toolchain fix
          else
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rd.name(), get_imm(), rs1.name());
        CS_FORMAT:
          if (category == STORE)
            if (instr_name == C_FSW)
              //asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fs2.name(), get_imm(), rs1.name());
              asm_str = $sformatf("%0s f%0d, %0s(%0s)", asm_str, reg_idx_fs2, get_imm(), rs1.name());  //FIXME : dd-vaibhavjain. revert temp wrd after toolchain fix
            else
              asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rs2.name(), get_imm(), rs1.name());
          else
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rs1.name(), rs2.name());
        CA_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs2.name());
        CB_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rs1.name(), get_imm());
        CSS_FORMAT:
          if (category == STORE)
            if (instr_name == C_FSWSP)
              //asm_str = $sformatf("%0s%0s, %0s(sp)", asm_str, fs2.name(), get_imm());
              asm_str = $sformatf("%0s f%0d, %0s(sp)", asm_str, reg_idx_fs2, get_imm()); //FIXME : dd-vaibhavjain. revert temp wrd after toolchain fix
            else
              asm_str = $sformatf("%0s%0s, %0s(sp)", asm_str, rs2.name(), get_imm());
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
 
endclass : cv32e40p_riscv_compressed_instr
