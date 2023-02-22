/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
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

class cv32e40p_rand_instr_stream extends riscv_rand_instr_stream;

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
