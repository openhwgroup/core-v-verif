/*
 * Copyright 2018 Google LLC
 * Copyright 2020 OpenHW Group
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

//------------------------------------------------------------------------------
// CORE-V illegal instruction
//     Extends privileged registers for CORE-V core platform extensions
//
// The base test Uses the factory to replace riscv_illegal_instr_reg with corev_illegal_instr
//   - Adds CV32E40P CSRs to ensure illegal instructions do not target proper instructions
//      - NOTE: This is caused by riscv-dv for CV32E40P v1.0.0 using an older riscv-dv that
//              was out of date with respect to debug spec (i.e. missed some CSRs).
//              This should be undone upon upgrading riscv-dv version.
//------------------------------------------------------------------------------

class cv32e40p_illegal_instr extends riscv_illegal_instr;

  // override Default legal opcode for RV32C instructions
  bit [2:0]  legal_c00_opcode[$] = '{3'b000,
                                     3'b010,
                                     3'b011,
                                     3'b110,
                                     3'b111};
  bit [2:0]  legal_c10_opcode[$] = '{3'b000,
                                     3'b010,
                                     3'b011,
                                     3'b100,
                                     3'b110,
                                     3'b111};

  // replicate constraint here to enable constraint takes effect with local variables from this class
  // when we use factory override to this class
  constraint illegal_compressed_op_c {
    if (exception == kIllegalCompressedOpcode) {
      c_op != 2'b01;
      if (legal_c00_opcode.size() == 8) {
        c_op != 2'b00;
      } else {
        !(c_msb inside {legal_c00_opcode});
      }
      if (legal_c10_opcode.size() == 8) {
        c_op != 2'b10;
      } else {
        !(c_msb inside {legal_c10_opcode});
      }
    }
  }

  constraint missing_csr_debug_regs_c {
    instr_bin[31:20] != 'h7A4; // TINFO
    instr_bin[31:20] != 'h7A5; // TCONTROL
    instr_bin[31:20] != 'h7A8; // MCONTEXT
    instr_bin[31:20] != 'h7AA; // SCONTEXT    
  }

  constraint reserved_when_rv32FC_c {
    if (riscv_instr_pkg::RV32FC inside {riscv_instr_pkg::supported_isa}) {
      if (exception == kReservedCompressedInstr) {
        reserved_c != kReservedLdsp;
      }
    }
  }

  `uvm_object_utils(cv32e40p_illegal_instr);

  function new(string name="");
    super.new(name);
  endfunction

  function void cv32e40p_init(riscv_instr_gen_config cfg);
    this.cfg = cfg;
    if (riscv_instr_pkg::RV32FC inside {riscv_instr_pkg::supported_isa}) begin
      if (!(3'b011 inside {legal_c00_opcode})) legal_c00_opcode = {legal_c00_opcode, 3'b011};
      if (!(3'b111 inside {legal_c00_opcode})) legal_c00_opcode = {legal_c00_opcode, 3'b111};
      if (!(3'b011 inside {legal_c10_opcode})) legal_c00_opcode = {legal_c10_opcode, 3'b011};
      if (!(3'b111 inside {legal_c10_opcode})) legal_c00_opcode = {legal_c10_opcode, 3'b111};
    end
    if (riscv_instr_pkg::RV32ZFINX inside {riscv_instr_pkg::supported_isa}) begin
      legal_opcode = {legal_opcode, 7'b1000011, 7'b1000111, 7'b1001011,
                                    7'b1001111, 7'b1010011};
    end
    if (riscv_instr_pkg::RV32X inside {riscv_instr_pkg::supported_isa}) begin
      legal_opcode = {legal_opcode, 7'b0001011, 7'b0101011, 7'b1011011,
                                    7'b1111011};
    end
  endfunction

endclass : cv32e40p_illegal_instr
