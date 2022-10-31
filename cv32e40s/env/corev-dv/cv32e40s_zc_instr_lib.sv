 /*
 * Copyright 2020 OpenHW Group
 * Copyright 2022 Silicon Labs, Inc.
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

virtual class corev_zcmt_cmjt_base_stream extends riscv_directed_instr_stream;

  `uvm_object_utils(corev_zcmt_cmjt_base_stream)
  `uvm_object_new

  function new(string name = "");
    super.new(name);
  endfunction : new

  extern function void setup_jvt(bit[7:0] num_entries, riscv_reg_t location);
  extern function riscv_reg_t get_valid_table_location();
  extern function void gen_jvt_entry(bit[7:0] entry_number);

endclass : corev_zcmt_cmjt_base_stream

function void corev_zcmt_cmjt_base_stream::setup_jvt(bit[7:0] num_entries, riscv_reg_t location);
  riscv_instr instr;
  instr = riscv_instr::get_rand_instr(.include_instr({LUI}));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name == LUI;
    rd         == addr_reg;
    imm        == addr[31:12];
    , "Failed randomizing LUI"
  )
  instr.comment = $sformatf("start setup_jvt (num_entries: %0d, location: %08x)");
  insert_instr(instr, 0);
endfunction : setup_jvt

function riscv_reg_t corev_zcmt_cmjt_base_stream::get_valid_table_location();
endfunction : get_valid_table_location

function void corev_zcmt_cmjt_base_stream::gen_jvt_entry(bit[7:0] entry_number);
endfunction : gen_jvt_entry
