/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
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

// Base class as an example

 class cv32e40p_base_instr_stream extends riscv_rand_instr_stream;
  `uvm_object_utils(cv32e40p_base_instr_stream)
  int unsigned num_of_avail_regs;

  function new(string name = "");
    super.new(name);
  endfunction

  function void pre_randomize();
    super.pre_randomize();
  endfunction

  virtual function void setup_allowed_instr(bit no_branch = 1'b0, bit no_load_store = 1'b1);
      allowed_instr = riscv_instr::basic_instr;
      if (no_branch == 0) begin
        allowed_instr = {allowed_instr, riscv_instr::instr_category[BRANCH],
                                        riscv_instr::instr_category[BRANCH_IMM]};
      end
      if (no_load_store == 0) begin
        allowed_instr = {allowed_instr, riscv_instr::instr_category[LOAD],
                                        riscv_instr::instr_category[STORE],
                                        riscv_instr::instr_category[POST_INC_LOAD],
                                        riscv_instr::instr_category[POST_INC_STORE]};
      end
      setup_instruction_dist(no_branch, no_load_store);
    endfunction

  function void setup_instruction_dist(bit no_branch = 1'b0, bit no_load_store = 1'b1);
  if (cfg.dist_control_mode) begin
      category_dist = cfg.category_dist;
      if (no_branch) begin
        category_dist[BRANCH] = 0;
        category_dist[BRANCH_IMM] = 0;
      end
      if (no_load_store) begin
        category_dist[LOAD] = 0;
        category_dist[STORE] = 0;
        category_dist[POST_INC_LOAD] = 0;
        category_dist[POST_INC_STORE] = 0;
      end
      `uvm_info(`gfn, $sformatf("setup_instruction_dist: %0d", category_dist.size()), UVM_LOW)
  end
  endfunction
endclass
