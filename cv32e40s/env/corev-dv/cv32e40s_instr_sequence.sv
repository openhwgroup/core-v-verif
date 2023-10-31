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
// CV32E40S instruction sequence, this override prevents hint/illegal instructions from
// overwriting atomic instruction sequences.
//
// TODO: Ideally we would like to only do this for the important instructions in the zcmt
// sequences, but as these instuctions are inserted into the instruction list the
// necessary information to identify these instructions are lost.
//
//-----------------------------------------------------------------------------------------
class cv32e40s_instr_sequence extends riscv_instr_sequence;
  `uvm_object_utils(cv32e40s_instr_sequence)

  function new (string name = "");
    super.new(name);
  endfunction : new

  virtual function void generate_instr_stream(bit no_label = 1'b0);
    string prefix, str;
    int i;
    insert_illegal_hint_instr();
    instr_string_list = {};
    for(i = 0; i < instr_stream.instr_list.size(); i++) begin
      if(i == 0) begin
        if (no_label) begin
          prefix = format_string(" ", LABEL_STR_LEN);
        end else begin
          prefix = format_string($sformatf("%0s:", label_name), LABEL_STR_LEN);
        end
        instr_stream.instr_list[i].has_label = 1'b1;
      end else begin
        if(instr_stream.instr_list[i].has_label) begin
          prefix = format_string($sformatf("%0s:", instr_stream.instr_list[i].label),
                   LABEL_STR_LEN);
        end else begin
          prefix = format_string(" ", LABEL_STR_LEN);
        end
      end
      str = {prefix, instr_stream.instr_list[i].convert2asm()};
      instr_string_list.push_back(str);
    end
    // If PMP is supported, need to align <main> to a 4-byte boundary.
    // TODO(udi) - this might interfere with multi-hart programs,
    //             may need to specifically match hart0.
    if (riscv_instr_pkg::support_pmp && !uvm_re_match(uvm_glob_to_re("*main*"), label_name)) begin
      instr_string_list.push_front(".align 2");
    end
    prefix = format_string($sformatf("%0d:", i), LABEL_STR_LEN);
    if(!is_main_program) begin
      generate_return_routine(prefix);
    end
  endfunction

  function void insert_illegal_hint_instr();
    int bin_instr_cnt;
    int idx;
    string str;
    corev_directive_instr raw_instr;
    illegal_instr.init(cfg);
    bin_instr_cnt = instr_cnt * cfg.illegal_instr_ratio / 1000;
    raw_instr = corev_directive_instr::type_id::create("instr");

    if (bin_instr_cnt >= 0) begin
      `uvm_info(`gfn, $sformatf("Injecting %0d illegal instructions, ratio %0d/100",
                      bin_instr_cnt, cfg.illegal_instr_ratio), UVM_LOW)
      repeat (bin_instr_cnt) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(illegal_instr,
                                       exception != kHintInstr;)
        raw_instr.directive = $sformatf(".4byte 0x%s # %0s",
                       illegal_instr.get_bin_str(), illegal_instr.comment);
        raw_instr.has_label = 1'b0;
        idx = $urandom_range(0, instr_stream.instr_list.size() - 1);
        // Inserting instructions within atomic sequences causes
        // issues with things such as jump tables etc. that depend
        // on absolute addressing.
        while (instr_stream.instr_list[idx].atomic) begin
          idx = $urandom_range(0, instr_stream.instr_list.size() - 1);
        end
        //instr_stream.insert(idx, str);
        instr_stream.insert_instr(raw_instr, idx);
      end
    end
    bin_instr_cnt = instr_cnt * cfg.hint_instr_ratio / 1000;
    if (bin_instr_cnt >= 0) begin
      `uvm_info(`gfn, $sformatf("Injecting %0d HINT instructions, ratio %0d/100",
                      bin_instr_cnt, cfg.illegal_instr_ratio), UVM_LOW)
      repeat (bin_instr_cnt) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(illegal_instr,
                                       exception == kHintInstr;)
        raw_instr.directive = $sformatf(".2byte 0x%s # %0s",
                       illegal_instr.get_bin_str(), illegal_instr.comment);
        raw_instr.has_label = 1'b0;
        idx = $urandom_range(0, instr_stream.instr_list.size() - 1);
        // Inserting instructions within atomic sequences causes
        // issues with things such as jump tables etc. that depend
        // on absolute addressing
        while (instr_stream.instr_list[idx].atomic) begin
          idx = $urandom_range(0, instr_stream.instr_list.size() - 1);
        end
        instr_stream.insert_instr(raw_instr, idx);
      end
    end
  endfunction

endclass : cv32e40s_instr_sequence
