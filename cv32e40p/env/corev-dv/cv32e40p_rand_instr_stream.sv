/*
 * Copyright 2018 Google LLC
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

// Base class for RISC-V instruction stream
// A instruction stream here is a  queue of RISC-V basic instructions.
// This class also provides some functions to manipulate the instruction stream, like insert a new
// instruction, mix two instruction streams etc.

class cv32e40p_rand_instr_stream extends riscv_rand_instr_stream;

  // below properties are for insert_instr_stream function
  protected int         idx_start[$];            
  protected int         idx_end[$];            
  protected int         idx_min = 0;            

  `uvm_object_utils(cv32e40p_rand_instr_stream)
  `uvm_object_new

  // overriding this function to modified the instructions placements so that directed streams should not overlap with each others
  virtual function void insert_instr_stream(riscv_instr new_instr[], int idx = -1, bit replace = 1'b0);

    int current_instr_cnt = instr_list.size();
    int new_instr_cnt = new_instr.size(); // e.g from directed stream

    if (replace) begin
      `uvm_fatal(`gfn, $sformatf("Function implementation is not ready for replace==1"))
    end

    if(current_instr_cnt == 0) begin
      instr_list = new_instr;
      return;
    end
    if(idx == -1) begin

      bit idx_search_done = 0;
      int rand_cnt = 0;

      idx = $urandom_range(0, current_instr_cnt-1);
      while (!instr_list[idx].atomic && !idx_search_done) begin
        int idx_e = 0;
        idx = $urandom_range(0, current_instr_cnt-1);
        idx_e = (idx + new_instr_cnt-1);

        if (idx_start.size() == 0) begin : SEARCH_IDX_FOR_NEW_INSTR
          idx_min = idx;
          idx_search_done = 1;
        end // SEARCH_IDX_FOR_NEW_INSTR
        else begin
          foreach (idx_start[i]) begin
            if (
              (idx          >= idx_start[i]   &&  idx           <= idx_end[i])  ||
              (idx_e        >= idx_start[i]   &&  idx_e         <= idx_end[i])  ||
              (idx_start[i] >= idx            &&  idx_start[i]  <= idx_e)       ||
              (idx_end[i]   >= idx            &&  idx_end[i]    <= idx_e)
            ) begin : DETECT_OVERLAP_IDX_FOR_NEW_INSTR
              break;
            end // DETECT_OVERLAP_IDX_FOR_NEW_INSTR
            else begin : NON_OVERLAP_IDX_FOR_NEW_INSTR
              if (i == (idx_start.size()-1)) begin
                idx_search_done = 1;
                break;
              end
            end // NON_OVERLAP_IDX_FOR_NEW_INSTR
          end // foreach
        end // SEARCH_IDX_FOR_NEW_INSTR

        if (idx_search_done) begin
          int idx_placement[$];
          if ((idx_start.size() == 0) || (idx_e < idx_min)) begin
            idx_min = idx;
            `uvm_info(`gfn, $sformatf("[DEBUG] - idx_min updated [%0d]", idx_min), UVM_DEBUG)
          end
          idx_start.push_back(idx);
          idx_end.push_back(idx_e);
          `uvm_info(`gfn, $sformatf("[DEBUG] - idx_start (before sort)       - %p", idx_start), UVM_DEBUG)
          `uvm_info(`gfn, $sformatf("[DEBUG] - idx_end   (before sort)       - %p", idx_end), UVM_DEBUG)
          idx_start.sort();
          idx_end.sort();
          `uvm_info(`gfn, $sformatf("[DEBUG] - idx_start (after sort)        - %p", idx_start), UVM_DEBUG)
          `uvm_info(`gfn, $sformatf("[DEBUG] - idx_end   (after sort)        - %p", idx_end), UVM_DEBUG)
          idx_placement = idx_start.find_first_index(x) with (x == idx);
          for (int i=idx_placement[0]+1; i<idx_start.size(); i++) begin
            idx_start[i] = idx_start[i]+new_instr_cnt;
            idx_end[i]   = idx_end[i]+new_instr_cnt;
            `uvm_info(`gfn, $sformatf("[DEBUG] - idx_start (update placement)  - %p", idx_start), UVM_DEBUG)
            `uvm_info(`gfn, $sformatf("[DEBUG] - idx_end   (update placement)  - %p", idx_end), UVM_DEBUG)
          end
        end // idx_search_done

        rand_cnt++;
        if (rand_cnt >= 100) begin
          `uvm_fatal(`gfn, $sformatf("rand_cnt hit limit %0d and not able to find space for instr placement. Please revise the stream", rand_cnt))
        end // rand_cnt

      end // while

      if (instr_list[idx].atomic) begin
        foreach (instr_list[i]) begin
          if (!instr_list[i].atomic) begin
            idx = i;
            break;
          end
        end
        if (instr_list[idx].atomic) begin
          `uvm_fatal(`gfn, $sformatf("Cannot inject the instruction"))
        end
      end // instr_list[idx].atomic

    end else if((idx > current_instr_cnt) || (idx < 0)) begin
      `uvm_error(`gfn, $sformatf("Cannot insert instr stream at idx %0d", idx))
    end // idx

    // When replace is 1, the original instruction at this index will be removed. The label of the
    // original instruction will be copied to the head of inserted instruction stream.
    if(replace) begin
      new_instr[0].label = instr_list[idx].label;
      new_instr[0].has_label = instr_list[idx].has_label;
      if (idx == 0) begin
        instr_list = {new_instr, instr_list[idx+1:current_instr_cnt-1]};
      end else begin
        instr_list = {instr_list[0:idx-1], new_instr, instr_list[idx+1:current_instr_cnt-1]};
      end
    end else begin
      if (idx == 0) begin
        instr_list = {new_instr, instr_list[idx:current_instr_cnt-1]};
      end else begin
        instr_list = {instr_list[0:idx-1], new_instr, instr_list[idx:current_instr_cnt-1]};
      end
    end
  endfunction

endclass

