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

  `uvm_component_utils(cv32e40p_instr_base_test)

  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    override_asm_program_gen();
    override_gen_config();
    override_compressed_instr();
    override_illegal_instr();
    override_privil_reg();
    override_debug_rom_gen();
    override_instr_stream();
    super.build_phase(phase);
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
    int test_override_riscv_instr_stream = 0;
    int test_override_fp_instr_stream = 99;
    if ($value$plusargs("test_override_riscv_instr_stream=%0d", test_override_riscv_instr_stream)) begin : TEST_OVERRIDE_RISCV_INSTR_STREAM
      unique case(test_override_riscv_instr_stream)
        1: begin 
          uvm_factory::get().set_type_override_by_type(riscv_rand_instr_stream::get_type(), cv32e40p_rand_instr_stream::get_type()); 
        end
      endcase
    end // TEST_OVERRIDE_RISCV_INSTR_STREAM
    if ($value$plusargs("test_override_fp_instr_stream=%0d", test_override_fp_instr_stream)) begin : TEST_OVERRIDE_FP_INSTR_STREAM
      unique case(test_override_fp_instr_stream)
        0: begin 
           end
        1: begin
          `uvm_info(this.type_name, $sformatf("uvm_factory set_type_override_by_type to CV32E40P_FP_N_MIXED_INSTR_STREAM"), UVM_NONE);
          uvm_factory::get().set_type_override_by_type(cv32e40p_float_zfinx_base_instr_stream::get_type(),  cv32e40p_fp_n_mixed_instr_stream::get_type()); 
        end
        2: begin
          `uvm_info(this.type_name, $sformatf("uvm_factory set_type_override_by_type to CV32E40P_FP_N_MIXED_INSTR_W_EXCL_STREAM"), UVM_NONE);
          uvm_factory::get().set_type_override_by_type(cv32e40p_float_zfinx_base_instr_stream::get_type(),  cv32e40p_fp_n_mixed_instr_w_excl_stream::get_type()); 
        end
        3: begin
          `uvm_info(this.type_name, $sformatf("uvm_factory set_type_override_by_type to CV32E40P_FP_N_MIXED_INSTR_MORE_FDIV_FSQRT_STREAM"), UVM_NONE);
          uvm_factory::get().set_type_override_by_type(cv32e40p_float_zfinx_base_instr_stream::get_type(),  cv32e40p_fp_n_mixed_instr_more_fdiv_fsqrt_stream::get_type()); 
        end
        4: begin
          `uvm_info(this.type_name, $sformatf("uvm_factory set_type_override_by_type to CV32E40P_FP_W_SPECIAL_OPERANDS_INSTR_STREAM"), UVM_NONE);
          uvm_factory::get().set_type_override_by_type(cv32e40p_float_zfinx_base_instr_stream::get_type(),  cv32e40p_fp_w_special_operands_instr_stream::get_type()); 
        end
        5: begin
          `uvm_info(this.type_name, $sformatf("uvm_factory set_type_override_by_type to CV32E40P_FP_W_PREV_RD_AS_OPERAND_INSTR_STREAM"), UVM_NONE);
          uvm_factory::get().set_type_override_by_type(cv32e40p_float_zfinx_base_instr_stream::get_type(),  cv32e40p_fp_w_prev_rd_as_operand_instr_stream::get_type()); 
        end
        6: begin
          `uvm_info(this.type_name, $sformatf("uvm_factory set_type_override_by_type to CV32E40P_CONSTRAINT_MC_FP_INSTR_STREAM"), UVM_NONE);
          uvm_factory::get().set_type_override_by_type(cv32e40p_float_zfinx_base_instr_stream::get_type(),  cv32e40p_constraint_mc_fp_instr_stream::get_type()); 
        end
      endcase
    end // TEST_OVERRIDE_FP_INSTR_STREAM
  endfunction

  virtual function void apply_directed_instr();
  endfunction

endclass : cv32e40p_instr_base_test
