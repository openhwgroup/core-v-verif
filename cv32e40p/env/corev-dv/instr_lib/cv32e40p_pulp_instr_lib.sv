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

class cv32e40p_base_pulp_instr_stream extends cv32e40p_base_instr_stream;

  `uvm_object_utils(cv32e40p_base_pulp_instr_stream)

  function new(string name = "");
    super.new(name);
  endfunction

  function void pre_randomize();
    super.pre_randomize();
  endfunction

  virtual function void gen_xpulp_instr();
    riscv_instr instr;
    randomize_avail_regs();
    instr = cv32e40p_instr::get_xpulp_instr(allowed_instr);
    randomize_gpr(instr);
    instr_list.push_back(instr);
  endfunction

endclass


class cv32e40p_xpulp_sanity_stream_test extends cv32e40p_base_pulp_instr_stream;

  `uvm_object_utils(cv32e40p_xpulp_sanity_stream_test)

  function new(string name = "cv32e40p_xpulp_sanity_stream_test");
    super.new(name);
  endfunction : new

  function void post_randomize();
    riscv_instr_gen_config  cfg_handle;
    riscv_instr placeholder_ins = riscv_instr::type_id::create("dummy_ins");
    riscv_instr_name_t all_xpulp_instr[$] = {};

    uvm_config_db#(riscv_instr_gen_config)::get(null, "*", "instr_cfg", cfg_handle);
    placeholder_ins.create_instr_list(cfg_handle);

    all_xpulp_instr = placeholder_ins.instr_group[RV32X];

    foreach (all_xpulp_instr[i]) begin
      if (all_xpulp_instr[i] inside { CV_BEQIMM, CV_BNEIMM, CV_START, CV_STARTI, CV_END, CV_ENDI, CV_COUNT, CV_COUNTI, CV_SETUP, CV_SETUPI, CV_ELW } ) continue;
      allowed_instr = {all_xpulp_instr[i]};
      gen_xpulp_instr();
    end

    // add manually the last instructions
  endfunction : post_randomize

endclass : cv32e40p_xpulp_sanity_stream_test
