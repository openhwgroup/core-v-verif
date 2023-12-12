/*
 * Copyright 2022 Silicon Laboratories Inc.
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

//-----------------------------------------------------------------------------------------
//
// CV32E40S random table jump instruction stream
//
//-----------------------------------------------------------------------------------------
class corev_zcmt_base_stream extends riscv_directed_instr_stream;

  const int unsigned JVT_ALIGNMENT_BITS_CONST = 6;

  `uvm_object_utils(corev_zcmt_base_stream)

  rand int num_table_entries;
  rand int num_mixed_instr;

  function new(string name = "");
    super.new(name);
  endfunction : new

  extern function void generate_jump_table_instr(int entries);
  extern function void add_mixed_instr(int instr_cnt);
  extern function void post_randomize();

  constraint num_table_entries_cnstr {
    num_table_entries inside {[1:255]};
  }

  constraint num_mixed_c {
    num_mixed_instr inside {[1:50]};
  }

endclass : corev_zcmt_base_stream

// -----------------------------------------------------------------------------

function void corev_zcmt_base_stream::generate_jump_table_instr(int entries);
  riscv_instr instr;
  riscv_compressed_instr compr_instr;
  riscv_csr_instr csr_instr;
  riscv_pseudo_instr pseudo_instr;
  corev_directive_instr raw_instr;
  riscv_reg_t saved_rdrs1;
  automatic int unsigned instr_loc = 0;

  // Backup RA to preserve state
  compr_instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_PUSH})));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(compr_instr,
    instr_name == CM_PUSH;
    spimm == 2'h0; // No additional stack adjust
    rlist == 4'h4; // RA only
    , "Failed randomizing CM.PUSH"
  )
  insert_instr(compr_instr, instr_loc++);

  // Load address of jump-table (jvt)
  pseudo_instr = riscv_pseudo_instr::type_id::create("la_instr");
  `DV_CHECK_RANDOMIZE_WITH_FATAL(pseudo_instr,
    pseudo_instr_name == LA;
    !(rd inside {cfg.reserved_regs, ZERO});
    , "Failed randomizing LA"
  )
  pseudo_instr.atomic = 1'b1;
  pseudo_instr.imm_str = $sformatf("jt_%0d", get_inst_id());
  saved_rdrs1 = pseudo_instr.rd;
  insert_instr(riscv_instr'(pseudo_instr), instr_loc++);

  // Store table address to jvt
  csr_instr = riscv_csr_instr::type_id::create("csr_instr");
  // TODO randomize possible?
  csr_instr.instr_name = CSRRW;
  csr_instr.format     = R_FORMAT;
  csr_instr.rd         = ZERO;
  csr_instr.csr        = 12'h17;
  csr_instr.rs1        = saved_rdrs1;
  csr_instr.atomic     = 1'b1;
  csr_instr.write_csr  = 1'b1;
  insert_instr(riscv_instr'(csr_instr), instr_loc++);

  // Create random table jump instruction
  instr = riscv_instr::get_rand_instr(.include_instr({CM_JT, CM_JALT}));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name inside {CM_JT, CM_JALT};
    , "Failed generating return instruction"
  )
  insert_instr(instr, instr_loc++);

  // Create unique table label & alignment as required
  raw_instr = corev_directive_instr::type_id::create("instr");
  raw_instr.directive = $sformatf(".global jt_%0d", get_inst_id());
  raw_instr.atomic = 1'b1;
  raw_instr.has_label = 1'b0;
  insert_instr(raw_instr, instr_loc++);
  raw_instr = corev_directive_instr::type_id::create("instr");
  raw_instr.directive = $sformatf(".align %0d", JVT_ALIGNMENT_BITS_CONST);
  raw_instr.atomic = 1'b1;
  raw_instr.has_label = 1'b0;
  insert_instr(raw_instr, instr_loc++);

  // Create pointers to the final target instruction and label
  // the first table entry with the global symbol defined above
  for (int i = 0; i < entries; i++) begin
    raw_instr = corev_directive_instr::type_id::create("instr");
    raw_instr.directive = $sformatf(".long . + %0d", (entries - i)*4);
    raw_instr.has_label = 1'b1;
    raw_instr.label = i == 0 ? $sformatf("jt_%0d", get_inst_id()) : "";
    raw_instr.atomic = 1'b1;
    insert_instr(raw_instr, instr_loc++);
  end

  // Point RA to the last instruction in the sequence to
  // control instruction sequence completion
  pseudo_instr = riscv_pseudo_instr::type_id::create("la_instr");
  `DV_CHECK_RANDOMIZE_WITH_FATAL(pseudo_instr,
    pseudo_instr_name == LA;
    rd                == RA;
    , "Failed randomizing LA"
  )
  pseudo_instr.atomic = 1'b1;
  pseudo_instr.imm_str = $sformatf("end_jvt_%0d", get_inst_id());
  insert_instr(riscv_instr'(pseudo_instr), instr_loc++);

  // Return to regular flow
  instr = riscv_instr::get_rand_instr(.include_instr({JALR}));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name == JALR;
    rd   == ZERO;
    rs1  == RA;
    imm  == 0;
    , "Failed generating return instruction"
  )
  insert_instr(instr, instr_loc++);

  // Insert random end of sequence target instruction (no flow change) as it is
  // unsafe to return to the instruction after the last in sequence
  instr = riscv_instr::get_rand_instr(.include_category({SHIFT, ARITHMETIC, LOGICAL, COMPARE, SYNCH}));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    (category inside {SHIFT, ARITHMETIC, LOGICAL, COMPARE, SYNCH});
      // Note: Several of the constraints could be relaxed, but it turns really complicated
    has_rd == 1 -> !(rd inside {cfg.reserved_regs});
    has_rd == 0 && has_rs1 -> !(rs1 inside {cfg.reserved_regs});
    , "failed to randomize dummy instruction"
  )
  instr.has_label = 1'b1;
  instr.label = $sformatf("end_jvt_%0d", get_inst_id());
  insert_instr(instr, instr_loc++);

  // restore ra after return
  compr_instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_POP})));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(compr_instr,
    instr_name == CM_POP;
    spimm      == 2'h0;
    rlist      == 4'h4;
    , "Failed randomizing CM.PUSH"
  )

  insert_instr(compr_instr, instr_loc++);

endfunction : generate_jump_table_instr

// -----------------------------------------------------------------------------

function void corev_zcmt_base_stream::post_randomize();

  generate_jump_table_instr(256);

  // Add random instructions into the instruction stream,
  // but not into sequences of instructions defined as atomic.
  add_mixed_instr(num_mixed_instr);

  // Clear empty labels; prevents asm compilation failure with
  // lines starting with : without a preceding label.
  foreach(instr_list[i]) begin
    if (instr_list[i].label == "") begin
      instr_list[i].has_label = 1'b0;
    end
    instr_list[i].atomic    = 1'b1;
  end

  instr_list[0].comment = $sformatf("Start %0s", get_name());
  instr_list[$].comment = $sformatf("End %0s", get_name());

endfunction : post_randomize

// -----------------------------------------------------------------------------

function void corev_zcmt_base_stream::add_mixed_instr(int instr_cnt);
  riscv_instr instr;
  setup_allowed_instr(.no_branch(1), .no_load_store(1));
  for (int i = 0; i < instr_cnt; i++) begin
    instr = riscv_instr::type_id::create("instr");
    randomize_instr(instr);
    // Don't want to tamper with RA as that breaks the
    // intended sequence flow
    // TODO constrain somehow rather than rerandomize
    while (instr.rd == RA) begin
      randomize_instr(instr);
    end
    insert_instr(instr);
  end
endfunction : add_mixed_instr

// -----------------------------------------------------------------------------
