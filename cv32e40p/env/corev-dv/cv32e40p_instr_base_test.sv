/*
 * Copyright 2018 Google LLC
 * Copyright 2020 OpenHW Group
 * Copyright 2023 Dolphin Design
 * SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
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

//------------------------------------------------------------------------------
// CORE-V instruction generator base test:
//     - extension of the RISC-V instruction generator base test.
//
//------------------------------------------------------------------------------

class cv32e40p_instr_base_test extends corev_instr_base_test;

  cv32e40p_instr_gen_config cv32e40p_cfg;

  `uvm_component_utils(cv32e40p_instr_base_test)

  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    cv32e40p_cfg = cv32e40p_instr_gen_config::type_id::create("cv32e40p_cfg");
    uvm_config_db#(cv32e40p_instr_gen_config)::set(null, "*", "cv32e40p_instr_cfg", cv32e40p_cfg);
    override_gen_config();
    override_instr_type();
    override_instr_sequence();
    override_asm_program_gen();
    override_compressed_instr();
    override_illegal_instr();
    override_privil_reg();
    override_debug_rom_gen();
    override_instr_stream();
    override_load_store_lib();
    override_loop_instr();
    super.build_phase(phase);
  endfunction

  //Override randomize_cfg to randomize cv32e40p_instr_gen_config object
  virtual function void randomize_cfg();
    `DV_CHECK_RANDOMIZE_FATAL(cfg);

    `DV_CHECK_RANDOMIZE_FATAL(cv32e40p_cfg);
    `uvm_info(`gfn, $sformatf("cv32e40p_instr_gen_config is randomized:\n%0s",
                    cv32e40p_cfg.sprint()), UVM_LOW)

    cfg.copy(cv32e40p_cfg);

    `uvm_info(`gfn, $sformatf("riscv_instr_gen_config is randomized:\n%0s",
                    cfg.sprint()), UVM_LOW)
  endfunction

  virtual function void override_asm_program_gen();
    uvm_factory::get().set_type_override_by_type(corev_asm_program_gen::get_type(),
                                                 cv32e40p_asm_program_gen::get_type());
  endfunction

  virtual function void override_gen_config();
    uvm_factory::get().set_type_override_by_type(riscv_instr_gen_config::get_type(),
                                                 cv32e40p_instr_gen_config::get_type());
  endfunction

  virtual function void override_compressed_instr();
    uvm_factory::get().set_type_override_by_type(riscv_C_LUI_instr::get_type(),
                                                 cv32e40p_C_LUI_instr::get_type());
  endfunction

  virtual function void override_privil_reg();
    uvm_factory::get().set_type_override_by_type(riscv_privil_reg::get_type(),
                                                 cv32e40p_privil_reg::get_type());
  endfunction

  virtual function void override_illegal_instr();
    uvm_factory::get().set_type_override_by_type(riscv_illegal_instr::get_type(),
                                                 cv32e40p_illegal_instr::get_type());
  endfunction

  virtual function void override_debug_rom_gen();
    uvm_factory::get().set_type_override_by_type(riscv_debug_rom_gen::get_type(),
                                                 cv32e40p_debug_rom_gen::get_type());
  endfunction

  virtual function void override_instr_stream();
    int    test_override_riscv_instr_stream = 0;
    string test_override_fp_instr_stream = "default";
    if ($value$plusargs("test_override_riscv_instr_stream=%0d", test_override_riscv_instr_stream)) begin : TEST_OVERRIDE_RISCV_INSTR_STREAM
      unique case(test_override_riscv_instr_stream)
        1: begin
          uvm_factory::get().set_type_override_by_type(riscv_rand_instr_stream::get_type(), cv32e40p_rand_instr_stream::get_type());
        end
      endcase
    end // TEST_OVERRIDE_RISCV_INSTR_STREAM
  endfunction

  virtual function void override_instr_sequence();
    int test_override_riscv_instr_sequence = 0;
    if ($value$plusargs("test_override_riscv_instr_sequence=%0d", test_override_riscv_instr_sequence)) begin
      unique case(test_override_riscv_instr_sequence)
        1: begin
          uvm_factory::get().set_type_override_by_type(riscv_instr_sequence::get_type(), cv32e40p_instr_sequence::get_type());
        end
      endcase
    end
  endfunction

  virtual function void override_instr_type();
    int test_override_riscv_instr_type = 0;
    if ($value$plusargs("test_override_riscv_instr_type=%0d", test_override_riscv_instr_type)) begin
      unique case(test_override_riscv_instr_type)
        1: begin
          uvm_factory::get().set_type_override_by_type(riscv_instr::get_type(), cv32e40p_instr::get_type());
        end
      endcase
    end
  endfunction

  // to avoid stress tests to reserve all S0:A5 regs used by compressed instructions
  virtual function void override_load_store_lib();
    uvm_factory::get().set_type_override_by_type(riscv_multi_page_load_store_instr_stream::get_type(), cv32e40p_multi_page_load_store_instr_stream::get_type());
    uvm_factory::get().set_type_override_by_type(riscv_mem_region_stress_test::get_type(), cv32e40p_mem_region_stress_test::get_type());
  endfunction

  // to avoid loop tests to reserve all S0:A5 regs used by compressed instructions
  virtual function void override_loop_instr();
    uvm_factory::get().set_type_override_by_type(riscv_loop_instr::get_type(), cv32e40p_loop_instr::get_type());
  endfunction

  virtual function void apply_directed_instr();
  endfunction

endclass : cv32e40p_instr_base_test
