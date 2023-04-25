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


`ifndef __UVMT_CV32E40S_INSTR_FUNCTIONS__
`define __UVMT_CV32E40S_INSTR_FUNCTIONS__

/**
 * Encapsulates all functions used on instruction words
 */
  //package uvmt_cv32e40s_instr_pkg;
  // -------------------------------------------------------------------
  // Local param
  // -------------------------------------------------------------------
  //instruction masks

  localparam INSTR_MASK_FULL        = 32'h FFFF_FFFF;
  localparam INSTR_MASK_R_TYPE      = 32'h FE00_707F;
  localparam INSTR_MASK_I_S_B_TYPE  = 32'h 0000_707F;
  localparam INSTR_MASK_U_J_TYPE    = 32'h 0000_007F;
  localparam INSTR_MASK_CSRADDR     = 32'h FFF0_0000;
  localparam INSTR_MASK_CMPR        = 32'h 0000_E003;

  //instruction comparison values
  localparam INSTR_OPCODE_DRET      = 32'h 7B20_0073;
  localparam INSTR_OPCODE_MRET      = 32'h 3020_0073;
  localparam INSTR_OPCODE_URET      = 32'h 0020_0073;
  localparam INSTR_OPCODE_WFI       = 32'h 1050_0073;
  localparam INSTR_OPCODE_WFE       = 32'h 8C00_0073;
  localparam INSTR_OPCODE_EBREAK    = 32'h 0010_0073;
  localparam INSTR_OPCODE_C_EBREAK  = 32'h 0000_9002;
  localparam INSTR_OPCODE_ECALL     = 32'h 0000_0073;
  localparam INSTR_OPCODE_CSLLI     = 32'h 0000_0002;

  localparam INSTR_OPCODE_CSRRW     = 32'h 0000_1073;
  localparam INSTR_OPCODE_CSRRS     = 32'h 0000_2073;
  localparam INSTR_OPCODE_CSRRC     = 32'h 0000_3073;
  localparam INSTR_OPCODE_CSRRWI    = 32'h 0000_5073;
  localparam INSTR_OPCODE_CSRRSI    = 32'h 0000_6073;
  localparam INSTR_OPCODE_CSRRCI    = 32'h 0000_7073;

  localparam INSTR_MASK_PUSHPOP   = 32'b 11111111_11111111_111_11111_0000_00_11;
  localparam INSTR_OPCODE_PUSH    = 32'b 00000000_00000000_101_11000_0000_00_10;
  localparam INSTR_OPCODE_POP     = 32'b 00000000_00000000_101_11010_0000_00_10;
  localparam INSTR_OPCODE_POPRET  = 32'b 00000000_00000000_101_11110_0000_00_10;
  localparam INSTR_OPCODE_POPRETZ = 32'b 00000000_00000000_101_11100_0000_00_10;

  localparam INSTR_MASK_TABLEJUMP   = 32'b 11111111_11111111_111_111_00000000_11;
  localparam INSTR_OPCODE_TABLEJUMP = 32'b 00000000_00000000_101_000_00000000_10;

  localparam INSTR_MASK_FENCE    = 32'b 00000000000000000_111_00000_1111111;
  localparam INSTR_OPCODE_FENCE  = 32'b 00000000000000000_000_00000_0001111;
  localparam INSTR_MASK_FENCEI   = 32'b 00000000000000000_111_00000_1111111;
  localparam INSTR_OPCODE_FENCEI = 32'b 00000000000000000_001_00000_0001111;

  //positions
  localparam int INSTR_CSRADDR_POS  = 20;
  localparam DEFAULT_XLEN = 32;

  // -------------------------------------------------------------------
  // Functions
  // -------------------------------------------------------------------

  function automatic logic [4:0] rs1_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return instr[19:15];
  endfunction : rs1_f

  function automatic logic [4:0] rs2_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return instr[24:20];
  endfunction : rs2_f

  function automatic logic [4:0] rd_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return instr[11:7];
  endfunction : rd_f

  function automatic logic [6:0] opcode_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return instr[6:0];
  endfunction : opcode_f

  function automatic logic [2:0] funct3_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return instr[14:12];
  endfunction : funct3_f

  function automatic logic [6:0] funct7_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return instr[31:25];
  endfunction : funct7_f

  function automatic logic [12:0] branch_imm_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return ({instr[31], instr[7], instr[30:25], instr[11:8], 1'b0});
  endfunction : branch_imm_f


  // Check if instruction is of a certain type, without verifying the instr word is valid
  // Usage: instr_mask sets the parts of the instruction you want to compare,
  //        instr_ref is the reference to match
  function automatic logic match_instr_raw_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [ DEFAULT_XLEN-1:0] instr_ref,
    logic [ DEFAULT_XLEN-1:0] instr_mask
  );

  return ((instr & instr_mask) == instr_ref);

  endfunction : match_instr_raw_f

// Match instr types
  function automatic logic match_instr_r_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [ DEFAULT_XLEN-1:0] instr_ref
  );
    return match_instr_raw_f(instr, instr_ref, INSTR_MASK_R_TYPE);
  endfunction : match_instr_r_f

  function automatic logic match_instr_r_var_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [6:0] funct7,
    logic [2:0] funct3,
    logic [6:0] opcode
  );
  return match_instr_r_f(instr, {funct7, 10'b0, funct3, 5'b0, opcode});
  endfunction : match_instr_r_var_f

  function automatic logic match_instr_isb_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [ DEFAULT_XLEN-1:0] instr_ref
  );

    return match_instr_raw_f(instr, instr_ref, INSTR_MASK_I_S_B_TYPE);
  endfunction : match_instr_isb_f

  function automatic logic match_instr_isb_var_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [2:0] funct3,
    logic [6:0] opcode
  );
    return match_instr_isb_f(instr, {17'b0, funct3, 5'b0, opcode});
  endfunction : match_instr_isb_var_f

  function automatic logic match_instr_uj_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [ DEFAULT_XLEN-1:0] instr_ref
  );
    return  match_instr_raw_f(instr, instr_ref, INSTR_MASK_U_J_TYPE);
  endfunction : match_instr_uj_f

  function automatic logic match_instr_uj_var_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [6:0] opcode
  );
    return  match_instr_uj_f(instr, {25'b0, opcode});
  endfunction : match_instr_uj_var_f

  function automatic logic [6:0] cslli_shamt_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return  {instr[12], instr[6:2]};
  endfunction : cslli_shamt_f


  // Match CSR functions
  // These instruction are used to check for csr activity.
  // All instructions has the input csr_addr. Setting this limits the query to
  // that single address, leaving the input as 0 returns any csr activity.
  function automatic logic is_csr_instr_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [11:0] csr_addr = 0
  );
    if (csr_addr == 0) begin //not specified
      return  match_instr_isb_f(instr, INSTR_OPCODE_CSRRW)  ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRS)  ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRC)  ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRWI) ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRSI) ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRCI);
    end else begin
      return  match_instr_raw_f(instr, 32'h0 | (csr_addr << INSTR_CSRADDR_POS), INSTR_MASK_CSRADDR) &&
              ( match_instr_isb_f(instr, INSTR_OPCODE_CSRRW)  ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRS)  ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRC)  ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRWI) ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRSI) ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRCI));
    end
  endfunction : is_csr_instr_f

  // NOTE!  This instruction differs from the strict definition of "reading a CSR"
  //        in the RISCV-spec, as it returns true only if the read value is actually
  //        stored somewhere.
  function automatic logic is_csr_read_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [ 4:0] rd_addr,
    logic [11:0] csr_addr = 0
  );
    if (rd_addr != 0) begin
      return is_csr_instr_f(instr, csr_addr);
    end else begin // rd is X0, not a read instruction
      return 0;
    end
  endfunction

  // NOTE!  This instruction differs from the strict definition of "writing a CSR"
  //        in the RISCV-spec, as it returns true only if the csr is actually
  //        written.
  function automatic logic is_csr_write_f(
    logic [ DEFAULT_XLEN-1:0] instr,
    logic [ 4:0] rs1_addr,
    logic [11:0] csr_addr = 0
  );
    if (csr_addr == 0) begin //not specified
      return  ( (rs1_addr != 0) && match_instr_isb_f(instr, INSTR_OPCODE_CSRRW))  ||
              ( (rs1_addr != 0) && match_instr_isb_f(instr, INSTR_OPCODE_CSRRS))  ||
              ( (rs1_addr != 0) && match_instr_isb_f(instr, INSTR_OPCODE_CSRRC))  ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRWI) ||
              //TODO:MT add set and clear with immediate nonzero
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRSI) ||
              match_instr_isb_f(instr, INSTR_OPCODE_CSRRCI);
    end else begin
      return  match_instr_raw_f(instr, 32'h0 | (csr_addr << INSTR_CSRADDR_POS), INSTR_MASK_CSRADDR) &&
              ( ( (rs1_addr != 0) && match_instr_isb_f(instr, INSTR_OPCODE_CSRRW))  ||
                ( (rs1_addr != 0) && match_instr_isb_f(instr, INSTR_OPCODE_CSRRS))  ||
                ( (rs1_addr != 0) && match_instr_isb_f(instr, INSTR_OPCODE_CSRRC))  ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRWI) ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRSI) ||
                match_instr_isb_f(instr, INSTR_OPCODE_CSRRCI));
    end
  endfunction


  // Short functions for recognising special functions

  function automatic logic is_dret_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_DRET, INSTR_MASK_FULL);
  endfunction : is_dret_f

  function automatic logic is_mret_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_MRET, INSTR_MASK_FULL);
  endfunction : is_mret_f

  function automatic logic is_uret_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_URET, INSTR_MASK_FULL);
  endfunction : is_uret_f

  function automatic logic is_wfi_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_WFI, INSTR_MASK_FULL);
  endfunction : is_wfi_f

  function automatic logic is_wfe_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_WFE, INSTR_MASK_FULL);
  endfunction : is_wfe_f

  function automatic logic is_ebreak_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_EBREAK, INSTR_MASK_FULL) || match_instr_raw_f(instr, INSTR_OPCODE_C_EBREAK, INSTR_MASK_FULL);
  endfunction : is_ebreak_f

  function automatic logic is_ebreak_compr_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_C_EBREAK, INSTR_MASK_FULL);
  endfunction : is_ebreak_compr_f

  function automatic logic is_ebreak_noncompr_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_EBREAK, INSTR_MASK_FULL);
  endfunction : is_ebreak_noncompr_f

  function automatic logic is_ecall_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_ECALL, INSTR_MASK_FULL);
  endfunction : is_ecall_f

  function logic is_cslli_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return match_instr_raw_f(instr, INSTR_OPCODE_CSLLI, INSTR_MASK_CMPR);
  endfunction : is_cslli_f

  function automatic logic is_pushpop_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return  match_instr_raw_f(instr, INSTR_OPCODE_PUSH,    INSTR_MASK_PUSHPOP)  ||
            match_instr_raw_f(instr, INSTR_OPCODE_POP,     INSTR_MASK_PUSHPOP)  ||
            match_instr_raw_f(instr, INSTR_OPCODE_POPRET,  INSTR_MASK_PUSHPOP)  ||
            match_instr_raw_f(instr, INSTR_OPCODE_POPRETZ, INSTR_MASK_PUSHPOP);
  endfunction : is_pushpop_f

  function automatic logic is_tablejump_raw_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return  match_instr_raw_f(instr, INSTR_OPCODE_TABLEJUMP, INSTR_MASK_TABLEJUMP);
  endfunction : is_tablejump_raw_f

  function automatic logic is_fencefencei_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return  match_instr_raw_f(instr, INSTR_OPCODE_FENCE,  INSTR_MASK_FENCE)  ||
            match_instr_raw_f(instr, INSTR_OPCODE_FENCEI, INSTR_MASK_FENCEI);
  endfunction : is_fencefencei_f

  function automatic logic is_compressed_f(
    logic [ DEFAULT_XLEN-1:0] instr
  );
    return (instr[1:0] != 2'b11);
  endfunction : is_compressed_f

//endpackage

`endif // __UVMT_CV32E40S_INSTR_FUNCTIONS__

