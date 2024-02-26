/*
 * Copyright 2018 Google LLC
 * Copyright 2023 Dolphin Design
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
// CV32E40P RISC-V instruction sequence
//
// This class extends class riscv_instr_sequence of RISCV-DV Instruction generator
// The class intends to override parent class methods wherever needed for cv32e40p
// specific implementation.
// Overriden Methods - 
//   -- post_process_instr()
//   -- generate_instr_stream()
//-----------------------------------------------------------------------------------------

class cv32e40p_instr_sequence extends riscv_instr_sequence;

  cv32e40p_instr_gen_config    cv32e40p_cfg;
  cv32e40p_illegal_instr       cv32_illegal_instr;        // Illegal instruction generator

  `uvm_object_utils(cv32e40p_instr_sequence)

  function new (string name = "");
    super.new(name);
    if(!uvm_config_db#(cv32e40p_instr_gen_config)::get(null, "*", "cv32e40p_instr_cfg", cv32e40p_cfg)) begin
      `uvm_fatal(get_full_name(), "Cannot get cv32e40p_instr_gen_config")
    end
    cv32_illegal_instr = cv32e40p_illegal_instr::type_id::create("cv32_illegal_instr");
  endfunction

  //Function: cv32e40p_instr_sequence::post_process_instr()
  //Override parent class post_process_instr() inside cv32e40p_instr_sequence
  //Keeping same code as parent class post_process_intr() with additions -
  //--logic to check for hwloop stream related labels
  //--logic for PULP IMM_BRANCH
  virtual function void post_process_instr();
    int             i;
    int             label_idx;
    int             branch_cnt;
    int unsigned    branch_idx[];
    int             branch_target[int] = '{default: 0};
    string          temp_label_str;
    bit             label_is_pulp_hwloop_body_label = 0; // variable to indicate if given instr's Label is for HWLOOP
    

    // Insert directed instructions, it's randomly mixed with the random instruction stream.
    foreach (directed_instr[i]) begin
      instr_stream.insert_instr_stream(directed_instr[i].instr_list);
    end
    // Assign an index for all instructions, these indexes won't change even a new instruction
    // is injected in the post process.
    foreach (instr_stream.instr_list[i]) begin
      instr_stream.instr_list[i].idx = label_idx;

      //Determine if the label is for HWLOOP body.
      //If label is HWLOOP label then keep label for the given instruction
      //in post_process_instr(). Using label_is_pulp_hwloop_body_label.
      label_is_pulp_hwloop_body_label = 0;
      if(instr_stream.instr_list[i].has_label) begin

        temp_label_str=instr_stream.instr_list[i].label;
        label_is_pulp_hwloop_body_label = check_str_pattern_match(temp_label_str, "hwloop");

        if(label_is_pulp_hwloop_body_label) begin
          `uvm_info("cv32e40p_inst_sequence",
                     $sformatf("Print HWLOOP label instr - instr_stream.instr_list[%0d] %0s =  %0s ",
                     i,instr_stream.instr_list[i].convert2asm(),instr_stream.instr_list[i].label),
                     UVM_DEBUG)
        end

      end

      if (instr_stream.instr_list[i].has_label && !instr_stream.instr_list[i].atomic && !label_is_pulp_hwloop_body_label) begin
        if ((illegal_instr_pct > 0) && (instr_stream.instr_list[i].is_illegal_instr == 0)) begin
          // The illegal instruction generator always increase PC by 4 when resume execution, need
          // to make sure PC + 4 is at the correct instruction boundary.
          if (instr_stream.instr_list[i].is_compressed) begin
            if (i < instr_stream.instr_list.size()-1) begin
              if (instr_stream.instr_list[i+1].is_compressed) begin
                instr_stream.instr_list[i].is_illegal_instr =
                                       ($urandom_range(0, 100) < illegal_instr_pct);
              end
            end
          end else begin
            instr_stream.instr_list[i].is_illegal_instr =
                                       ($urandom_range(0, 100) < illegal_instr_pct);
          end
        end
        if ((hint_instr_pct > 0) && (instr_stream.instr_list[i].is_illegal_instr == 0)) begin
          if (instr_stream.instr_list[i].is_compressed) begin
            instr_stream.instr_list[i].is_hint_instr =
                                       ($urandom_range(0, 100) < hint_instr_pct);
          end
        end
        instr_stream.instr_list[i].label = $sformatf("%0d", label_idx);
        instr_stream.instr_list[i].is_local_numeric_label = 1'b1;
        label_idx++;
      end
    end
    // Generate branch target
    branch_idx = new[30];
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(branch_idx,
                                       foreach(branch_idx[i]) {
                                         branch_idx[i] inside {[1:cfg.max_branch_step]};
                                       })
    while(i < instr_stream.instr_list.size()) begin
      if((
        (instr_stream.instr_list[i].category == BRANCH) || 
        (instr_stream.instr_list[i].category == BRANCH_IMM)
        ) &&
        (!instr_stream.instr_list[i].branch_assigned) &&
        (!instr_stream.instr_list[i].is_illegal_instr)) begin
        // Post process the branch instructions to give a valid local label
        // Here we only allow forward branch to avoid unexpected infinite loop
        // The loop structure will be inserted with a separate routine using
        // reserved loop registers
        int branch_target_label;
        int branch_byte_offset;
        branch_target_label = instr_stream.instr_list[i].idx + branch_idx[branch_cnt];
        if (branch_target_label >= label_idx) begin : BRANCH_EXCEED_MAX_LABEL_IDX
          branch_target_label = label_idx-1;
        end
        branch_cnt++;
        if (branch_cnt == branch_idx.size()) begin : RESET_BRANCH_SETTING
          branch_cnt = 0;
          branch_idx.shuffle();
        end
        `uvm_info(get_full_name(),
                  $sformatf("Processing branch instruction[%0d]:%0s # %0d -> %0d",
                  i, instr_stream.instr_list[i].convert2asm(),
                  instr_stream.instr_list[i].idx, branch_target_label), UVM_HIGH)

        if (instr_stream.instr_list[i].category == BRANCH_IMM) begin
          instr_stream.instr_list[i].imm_str = $sformatf("%0d, %0df", $signed(instr_stream.instr_list[i].imm[16:12]), branch_target_label);
        end else begin
          instr_stream.instr_list[i].imm_str = $sformatf("%0df", branch_target_label); // <num>f
        end

        // Below calculation is only needed for generating the instruction stream in binary format
        for (int j = i + 1; j < instr_stream.instr_list.size(); j++) begin
          branch_byte_offset = (instr_stream.instr_list[j-1].is_compressed) ?
                               branch_byte_offset + 2 : branch_byte_offset + 4;
          if (instr_stream.instr_list[j].label == $sformatf("%0d", branch_target_label)) begin
            if (instr_stream.instr_list[i].category == BRANCH_IMM) begin
              instr_stream.instr_list[i].imm[11:0] = branch_byte_offset;
            end else begin
              instr_stream.instr_list[i].imm = branch_byte_offset;
            end
            break;
          end else if (j == instr_stream.instr_list.size() - 1) begin
            `uvm_fatal(`gfn, $sformatf("Cannot find target label : %0d", branch_target_label))
          end
        end
        instr_stream.instr_list[i].branch_assigned = 1'b1;
        branch_target[branch_target_label] = 1;
      end
      // Remove the local label which is not used as branch target
      if(instr_stream.instr_list[i].has_label &&
         instr_stream.instr_list[i].is_local_numeric_label) begin
        int idx = instr_stream.instr_list[i].label.atoi();
        if(!branch_target[idx]) begin
          instr_stream.instr_list[i].has_label = 1'b0;
        end
      end
      i++;
    end // while
    `uvm_info(get_full_name(), "Finished post-processing instructions", UVM_HIGH)
  endfunction

  //Function: cv32e40p_instr_sequence::generate_instr_stream()
  //Override parent class generate_instr_stream() inside cv32e40p_instr_sequence
  //Keeping same code as parent class post_process_intr() with additions -
  //--logic to check for hwloop stream related labels
  virtual function void generate_instr_stream(bit no_label = 1'b0);
    string  prefix, str;
    int     i;
    int     format_str_len;
    bit     label_is_pulp_hwloop_body_label = 0; // variable to indicate if given instr's label is for HWLOOP
    bit     insert_hwloop_start_directives = 0; // variable to indicate whether assembler directives are needed before hwloop starts
    bit     insert_hwloop_end_directives = 0; // variable to indicate whether assembler directives are needed after hwloop ends
    bit     insert_hwloop_align_directive = 0; // variable to indicate whether .align directive is needed before hwloop setup instr
    string  temp_str;

    instr_string_list = {};
    format_str_len = LABEL_STR_LEN;
    for(i = 0; i < instr_stream.instr_list.size(); i++) begin
      label_is_pulp_hwloop_body_label = 0;
      insert_hwloop_start_directives = 0;
      insert_hwloop_end_directives = 0;
      insert_hwloop_align_directive = 0;

      if(i == 0) begin
        if (no_label) begin
          prefix = format_string(" ", format_str_len);
        end else begin
          prefix = format_string($sformatf("%0s:", label_name), format_str_len);
        end
        instr_stream.instr_list[i].has_label = 1'b1;
      end else begin
        if(instr_stream.instr_list[i].has_label) begin : HAS_LABEL
          //check if it is hwloop label
          label_is_pulp_hwloop_body_label = check_str_pattern_match(instr_stream.instr_list[i].label, "hwloop");
          if(!label_is_pulp_hwloop_body_label) begin
            prefix = format_string($sformatf("%0s:", instr_stream.instr_list[i].label),format_str_len);
          end
          else begin
            insert_hwloop_start_directives = ((check_str_pattern_match(instr_stream.instr_list[i].label, "hwloop1_nested_start")) |
                                              (check_str_pattern_match(instr_stream.instr_list[i].label, "hwloop1_start")) |
                                              (check_str_pattern_match(instr_stream.instr_list[i].label, "hwloop0_start")));

            insert_hwloop_end_directives = ((check_str_pattern_match(instr_stream.instr_list[i].label, "hwloop1_nested_end")) |
                                            (check_str_pattern_match(instr_stream.instr_list[i].label, "hwloop1_end")) |
                                            (check_str_pattern_match(instr_stream.instr_list[i].label, "hwloop0_end")));

            insert_hwloop_align_directive = check_str_pattern_match(instr_stream.instr_list[i].label, "align_hwloop");

            if(insert_hwloop_align_directive) begin
              prefix = format_string(" ", format_str_len);
              //dont insert directives for cv_setup instr at current index: i,as the directives for these cases are handled in else block
              if(!((instr_stream.instr_list[i].instr_name == CV_SETUP) || (instr_stream.instr_list[i].instr_name == CV_SETUPI))) begin
                str = {prefix,".align 2"};
                instr_string_list.push_back(str);
              end
              instr_stream.instr_list[i].has_label = 0; //remove temp label
              instr_stream.instr_list[i].label = ""; //remove temp label
            end
            else begin
              if(insert_hwloop_start_directives) begin
                //check for cv_setup instr at index: i-1 , the directives need to be inserted before cv_setup/cv_setupi
                if((instr_stream.instr_list[i-1].instr_name == CV_SETUP) || (instr_stream.instr_list[i-1].instr_name == CV_SETUPI)) begin
                    temp_str = instr_string_list.pop_back(); // temporarily remove cv_setup/cv_setupi to insert directives
                end
                prefix = format_string(" ", format_str_len);
                str = {prefix,".align 2"};
                instr_string_list.push_back(str);
                str = {prefix,".option norvc"};
                instr_string_list.push_back(str);
                if((instr_stream.instr_list[i-1].instr_name == CV_SETUP) || (instr_stream.instr_list[i-1].instr_name == CV_SETUPI)) begin
                  instr_string_list.push_back(temp_str);  // insert back cv_setup/cv_setupi
                end
                format_str_len = HWLOOP_LABEL_STR_LEN;
              end
              if(insert_hwloop_end_directives) begin
                prefix = format_string(" ", format_str_len);
                str = {prefix,".option rvc"};
                instr_string_list.push_back(str);
              end
              prefix = format_string($sformatf("%0s:", instr_stream.instr_list[i].label), format_str_len);
            end
            insert_hwloop_align_directive = 0;
            if(insert_hwloop_end_directives) begin
              format_str_len = LABEL_STR_LEN;
            end
          end
          str = {prefix, instr_stream.instr_list[i].convert2asm()};
        end // HAS_LABEL
        else if (instr_stream.instr_list[i].is_illegal_instr) begin : IS_ILLEGAL_INSTR
          // insert illegal insn in directed stream
          cv32_illegal_instr.init(cfg);
          cv32_illegal_instr.cv32e40p_init(cfg); // Init legal_opcode for cv32e40p
          `DV_CHECK_RANDOMIZE_WITH_FATAL(cv32_illegal_instr, exception != kHintInstr;)
          str = {indent, $sformatf(".4byte 0x%s # %0s", cv32_illegal_instr.get_bin_str(), cv32_illegal_instr.comment)};
        end // IS_ILLEGAL_INSTR
        else begin
          prefix = format_string(" ", format_str_len);
          str = {prefix, instr_stream.instr_list[i].convert2asm()};
        end
      end // i != 0

      // str = {prefix, instr_stream.instr_list[i].convert2asm()};
      instr_string_list.push_back(str);

    end // instr_stream.instr_list.size

    // If PMP is supported, need to align <main> to a 4-byte boundary.
    if (riscv_instr_pkg::support_pmp && !uvm_re_match(uvm_glob_to_re("*main*"), label_name)) begin
      instr_string_list.push_front(".align 2");
    end
    cv32e40p_insert_illegal_hint_instr();
    prefix = format_string($sformatf("%0d:", i), LABEL_STR_LEN);
    if(!is_main_program) begin
      generate_return_routine(prefix);
    end
  endfunction

  // Similar to base class insert_illegal_hint_instr function
  // Added cv32_illegal_instr.cv32e40p_init() to include cv32e40p
  // specific legal opcodes
  function void cv32e40p_insert_illegal_hint_instr();
    int bin_instr_cnt;
    int idx;
    string str;
    cv32_illegal_instr.init(cfg);
    cv32_illegal_instr.cv32e40p_init(cfg); // Init legal_opcode for cv32e40p
    bin_instr_cnt = instr_cnt * cfg.illegal_instr_ratio / 1000;
    if (bin_instr_cnt >= 0) begin
      `uvm_info(`gfn, $sformatf("Injecting %0d illegal instructions, ratio %0d/100",
                      bin_instr_cnt, cfg.illegal_instr_ratio), UVM_LOW)
      repeat (bin_instr_cnt) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(cv32_illegal_instr,
                                       exception != kHintInstr;)
        str = {indent, $sformatf(".4byte 0x%s # %0s",
                       cv32_illegal_instr.get_bin_str(), cv32_illegal_instr.comment)};
               idx = $urandom_range(0, instr_string_list.size());
        instr_string_list.insert(idx, str);
      end
    end
    bin_instr_cnt = instr_cnt * cfg.hint_instr_ratio / 1000;
    if (bin_instr_cnt >= 0) begin
      `uvm_info(`gfn, $sformatf("Injecting %0d HINT instructions, ratio %0d/100",
                      bin_instr_cnt, cfg.illegal_instr_ratio), UVM_LOW)
      repeat (bin_instr_cnt) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(cv32_illegal_instr,
                                       exception == kHintInstr;)
        str = {indent, $sformatf(".2byte 0x%s # %0s",
                       cv32_illegal_instr.get_bin_str(), cv32_illegal_instr.comment)};
        idx = $urandom_range(0, instr_string_list.size());
        instr_string_list.insert(idx, str);
      end
    end
  endfunction

endclass
