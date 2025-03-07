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


 class cv32e40p_multi_page_load_store_instr_stream extends riscv_multi_page_load_store_instr_stream;
    rand int          has_taken_avail_comp_reg[];
    riscv_reg_t       s0_a5_avail_regs[];
    riscv_reg_t       s0_a5_avail_regs_q[$]; // a temp queue for using .find method

    constraint with_compress_instructions_c {
        has_taken_avail_comp_reg.size() == rs1_reg.size();
        foreach(rs1_reg[i]) {
            if (rs1_reg[i] inside {s0_a5_avail_regs}) {
                has_taken_avail_comp_reg[i] == 1;
            } else {
                has_taken_avail_comp_reg[i] == 0;
            }
        }
        // to make sure at least one is left for compress instructions
        // count the number of ones (= taken comp regs), and contraint it to be less than the number of avail regs
        if (cfg.disable_compressed_instr == 0) {
          has_taken_avail_comp_reg.sum() < s0_a5_avail_regs.size();
        }
    }

    `uvm_object_utils(cv32e40p_multi_page_load_store_instr_stream)
    `uvm_object_new

    function void pre_randomize();
      super.pre_randomize();
      s0_a5_avail_regs = {S0, S1, A0, A1, A2, A3, A4, A5};

      s0_a5_avail_regs_q = s0_a5_avail_regs.find() with (!(item inside {cfg.reserved_regs, reserved_rd}));
    
      // resize the dynamic array to the temp queue
      s0_a5_avail_regs = new[s0_a5_avail_regs_q.size()];

      // copy content of temp queue to the dynamic array
      for (int i = 0; i < s0_a5_avail_regs_q.size(); i++) begin
        s0_a5_avail_regs[i] = s0_a5_avail_regs_q[i];
      end
    endfunction
 endclass


 class cv32e40p_mem_region_stress_test extends riscv_mem_region_stress_test;
    rand int          has_taken_avail_comp_reg[];
    riscv_reg_t       s0_a5_avail_regs[];
    riscv_reg_t       s0_a5_avail_regs_q[$]; // a temp queue for using .find method

    constraint with_compress_instructions_c {
        has_taken_avail_comp_reg.size() == rs1_reg.size();
        foreach(rs1_reg[i]) {
            if (rs1_reg[i] inside {s0_a5_avail_regs}) {
                has_taken_avail_comp_reg[i] == 1;
            } else {
                has_taken_avail_comp_reg[i] == 0;
            }
        }
        // to make sure at least one is left for compress instructions
        // count the number of ones (= taken comp regs), and contraint it to be less than the number of avail regs
        if (cfg.disable_compressed_instr == 0) {
          has_taken_avail_comp_reg.sum() < s0_a5_avail_regs.size();
        }
    }


    `uvm_object_utils(cv32e40p_mem_region_stress_test)
    `uvm_object_new

    function void pre_randomize();
      super.pre_randomize();
      s0_a5_avail_regs = {S0, S1, A0, A1, A2, A3, A4, A5};

      s0_a5_avail_regs_q = s0_a5_avail_regs.find() with (!(item inside {cfg.reserved_regs, reserved_rd}));
    
      // resize the dynamic array to the temp queue
      s0_a5_avail_regs = new[s0_a5_avail_regs_q.size()];

      // copy content of temp queue to the dynamic array
      for (int i = 0; i < s0_a5_avail_regs_q.size(); i++) begin
        s0_a5_avail_regs[i] = s0_a5_avail_regs_q[i];
      end
    endfunction
 endclass
