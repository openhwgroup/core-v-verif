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
//-----------------------------------------------------------------------------------------

class cv32e40p_instr_sequence extends riscv_instr_sequence;

  bit label_is_pulp_hwloop_body_label = 0; // variable to indicate if given instr's Label is for HWLOOP

  `uvm_object_utils(cv32e40p_instr_sequence)

  function new (string name = "");
    super.new(name);
  endfunction

  //Function: cv32e40p_instr_sequence::post_process_instr()
  //Override parent class post_process_instr() inside cv32e40p_instr_sequence
  //Keeping same code as parent class post_process_intr() with additions -
  //--logic to check for hwloop stream related labels
  virtual function void post_process_instr();
    int             i;
    int             label_idx;
    int             branch_cnt;
    int unsigned    branch_idx[];
    int             branch_target[int] = '{default: 0};
    string          hwloop_label, temp_label;
    int             len1, len2;
    

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
        hwloop_label = "hwloop"; //Using this string for hwloop specific labels in random hwloop stream tests
        temp_label=instr_stream.instr_list[i].label;
        len1=hwloop_label.len();
        len2=temp_label.len();

        if(len1 < len2) begin
            for(int j = 0;j < len2-len1+1; j++) begin
                if(temp_label.substr(j,j+len1 -1) == hwloop_label) begin
                  label_is_pulp_hwloop_body_label = 1; // This var set indicates that this instr's label is for HWLOOP and must be kept
                  `uvm_info("cv32e40p_inst_sequence", $sformatf("Print HWLOOP label instr - instr_stream.instr_list[%0d] %0s =  %0s ",i,instr_stream.instr_list[i].convert2asm(),instr_stream.instr_list[i].label), UVM_DEBUG);
                  break;
                end
            end
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
      if((instr_stream.instr_list[i].category == BRANCH) &&
        (!instr_stream.instr_list[i].branch_assigned) &&
        (!instr_stream.instr_list[i].is_illegal_instr)) begin
        // Post process the branch instructions to give a valid local label
        // Here we only allow forward branch to avoid unexpected infinite loop
        // The loop structure will be inserted with a separate routine using
        // reserved loop registers
        int branch_target_label;
        int branch_byte_offset;
        branch_target_label = instr_stream.instr_list[i].idx + branch_idx[branch_cnt];
        if (branch_target_label >= label_idx) begin
          branch_target_label = label_idx-1;
        end
        branch_cnt++;
        if (branch_cnt == branch_idx.size()) begin
          branch_cnt = 0;
          branch_idx.shuffle();
        end
        `uvm_info(get_full_name(),
                  $sformatf("Processing branch instruction[%0d]:%0s # %0d -> %0d",
                  i, instr_stream.instr_list[i].convert2asm(),
                  instr_stream.instr_list[i].idx, branch_target_label), UVM_HIGH)
        instr_stream.instr_list[i].imm_str = $sformatf("%0df", branch_target_label);
        // Below calculation is only needed for generating the instruction stream in binary format
        for (int j = i + 1; j < instr_stream.instr_list.size(); j++) begin
          branch_byte_offset = (instr_stream.instr_list[j-1].is_compressed) ?
                               branch_byte_offset + 2 : branch_byte_offset + 4;
          if (instr_stream.instr_list[j].label == $sformatf("%0d", branch_target_label)) begin
            instr_stream.instr_list[i].imm = branch_byte_offset;
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
    end
    `uvm_info(get_full_name(), "Finished post-processing instructions", UVM_HIGH)
  endfunction


endclass
