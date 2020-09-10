// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// 
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


`ifndef __UVME_CV32_MACHINE_REG_BLOCK_SV__
`define __UVME_CV32_MACHINE_REG_BLOCK_SV__


/**
 * Example machine-level register block based upon Moore.io's RISC-V CSR UVM
 * Library.
 */
class uvme_cv32_machine_reg_block_c extends uvml_ral_reg_block_c;
   
   // Sub-Blocks
   rand uvml_riscv_csr_machine_information_reg_block_c           #(32)  information      ;
   rand uvml_riscv_csr_machine_trap_setup_reg_block_c            #(32)  trap_setup       ;
   rand uvml_riscv_csr_machine_trap_handling_reg_block_c         #(32)  trap_handling    ;
   rand uvml_riscv_csr_machine_memory_protection_rv32_reg_block_c#(32)  memory_protection;
   rand uvml_riscv_csr_machine_counters_timers_rv32_reg_block_c         counters_timers  ;
   rand uvml_riscv_csr_machine_counter_setup_reg_block_c         #(32)  counter_setup    ;
   rand uvml_riscv_csr_machine_debug_trace_reg_block_c           #(32)  debug_trace      ;
   rand uvml_riscv_csr_machine_debug_mode_reg_block_c            #(32)  debug_mode       ;
   
   
   `uvm_object_utils_begin(uvme_cv32_machine_reg_block_c)
      `uvm_field_object(information      , UVM_DEFAULT)
      `uvm_field_object(trap_setup       , UVM_DEFAULT)
      `uvm_field_object(trap_handling    , UVM_DEFAULT)
      `uvm_field_object(memory_protection, UVM_DEFAULT)
      `uvm_field_object(counters_timers  , UVM_DEFAULT)
      `uvm_field_object(counter_setup    , UVM_DEFAULT)
      `uvm_field_object(debug_trace      , UVM_DEFAULT)
      `uvm_field_object(debug_mode       , UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32_machine_reg_block", int has_coverage=UVM_NO_COVERAGE);
   
   /**
    * Creates sub-block(s).
    */
   extern virtual function void create_blocks();
   
   /**
    * Creates default register map.
    */
   extern virtual function void create_reg_map();
   
endclass : uvme_cv32_machine_reg_block_c


function uvme_cv32_machine_reg_block_c::new(string name="uvme_cv32_machine_reg_block", int has_coverage=UVM_NO_COVERAGE);
   
   super.new(name, has_coverage);
   
endfunction : new


function void uvme_cv32_machine_reg_block_c::create_blocks();
   
   information = uvml_riscv_csr_machine_information_reg_block_c#(32)::type_id::create("information");
   information.configure(this);
   information.build();
   
   trap_setup = uvml_riscv_csr_machine_trap_setup_reg_block_c#(32)::type_id::create("trap_setup");
   trap_setup.configure(this);
   trap_setup.build();
   
   trap_handling = uvml_riscv_csr_machine_trap_handling_reg_block_c#(32)::type_id::create("trap_handling");
   trap_handling.configure(this);
   trap_handling.build();
   
   memory_protection = uvml_riscv_csr_machine_memory_protection_rv32_reg_block_c#(32)::type_id::create("memory_protection");
   memory_protection.configure(this);
   memory_protection.build();
   
   counters_timers = uvml_riscv_csr_machine_counters_timers_rv32_reg_block_c::type_id::create("counters_timers");
   counters_timers.configure(this);
   counters_timers.build();
   
   counter_setup = uvml_riscv_csr_machine_counter_setup_reg_block_c#(32)::type_id::create("counter_setup");
   counter_setup.configure(this);
   counter_setup.build();
   
   debug_trace = uvml_riscv_csr_machine_debug_trace_reg_block_c#(32)::type_id::create("debug_trace");
   debug_trace.configure(this);
   debug_trace.build();
   
   debug_mode = uvml_riscv_csr_machine_debug_mode_reg_block_c#(32)::type_id::create("debug_mode");
   debug_mode.configure(this);
   debug_mode.build();
   
endfunction : create_blocks


function void uvme_cv32_machine_reg_block_c::create_reg_map();
   
   default_map = create_map(
      .name     ("default_map"),
      .base_addr(base_address),
      .n_bytes  (4),
      .endian   (UVM_LITTLE_ENDIAN)
   );
   
endfunction : create_reg_map


`endif // __UVME_CV32_MACHINE_REG_BLOCK_SV__
