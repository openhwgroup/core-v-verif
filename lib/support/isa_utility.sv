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
// This file holds functions related to the ISA decoder
// -------------------------------------------------------------------

`ifndef __ISA_UTILITY__
`define __ISA_UTILITY__

  `include "isa_support.sv"
  `include "isa_constants.sv"

  // -------------------------------------------------------------------
  // Functions
  // -------------------------------------------------------------------
/*
  function automatic logic dummy_hint_rd(asm_t asm);
  endfunction : dummy_hint_rd

  function automatic logic dummy_hint_rs1(asm_t asm);
  endfunction : dummy_hint_rs1

  function automatic logic dummy_hint_rs2(asm_t asm);
  endfunction : dummy_hint_rs2

  function automatic logic dummy_hint_branch_imm(asm_t asm);
  endfunction : dummy_hint_branch_imm
*/
  function automatic logic is_csr_read_spec_f(asm_t asm);
    if (asm.instr inside { CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI }) begin
      case (asm.instr)
        CSRRW, CSRRWI : is_csr_read_spec_f  = asm.rd.gpr ? 1'b1 : 1'b0;
        CSRRS, CSRRC  : is_csr_read_spec_f  = 1'b1;
        CSRRSI, CSRRCI: is_csr_read_spec_f  = 1'b1;
        // Should never be here
        default       : is_csr_read_spec_f  = 1'b0;
      endcase
    end else begin
      is_csr_read_spec_f = 1'b0;
    end
  endfunction : is_csr_read_spec_f

  function logic is_csr_write_spec_f(asm_t asm);
    if (asm.instr inside { CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI }) begin
      case (asm.instr)
        CSRRW, CSRRWI : is_csr_write_spec_f = 1'b1;
        CSRRS, CSRRC  : is_csr_write_spec_f = asm.rs1.gpr  ? 1'b1 : 1'b0;
        CSRRSI, CSRRCI: is_csr_write_spec_f = asm.imm.imm_value  ? 1'b1 : 1'b0;
        // Should never be here
        default       : is_csr_write_spec_f = 1'b0;
      endcase
    end else begin
      is_csr_write_spec_f = 1'b0;
    end
  endfunction : is_csr_write_spec_f

  // Short functions for recognising special functions

  function automatic logic[31:0] get_jvt_addr_f(
    logic [DEFAULT_XLEN-1:0] instr,
    logic [31:0] jvt
  );
    logic [ 9:2] field_index = instr[9:2];
    logic [31:6] field_base  = jvt[31:6];

    return ({field_base, 6'd 0} + (field_index << 2));
  endfunction : get_jvt_addr_f


`endif // __ISA_UTILITY__
