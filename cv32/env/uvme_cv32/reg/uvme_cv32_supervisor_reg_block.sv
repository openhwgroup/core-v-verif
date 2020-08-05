// 
// Copyright 2020 Datum Technology Corporation
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// 
// Licensed under the Solderpad Hardware License v 2.1 (the “License”); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/SHL-2.1/
// 
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
// 


`ifndef __UVME_CV32_SUPERVISOR_REG_BLOCK_SV__
`define __UVME_CV32_SUPERVISOR_REG_BLOCK_SV__


/**
 * Example supervisor-level register block based upon Moore.io's RISC-V CSR UVM
 * Library.
 */
class uvme_cv32_supervisor_reg_block_c extends uvml_ral_reg_block_c;
   
   // Sub-Blocks
   rand uvml_riscv_csr_supervisor_trap_setup_reg_block_c                #(32)  trap_setup                ;
   rand uvml_riscv_csr_supervisor_trap_handling_reg_block_c             #(32)  trap_handling             ;
   rand uvml_riscv_csr_supervisor_protection_and_translation_reg_block_c#(32)  protection_and_translation;
   
   
   `uvm_object_utils_begin(uvme_cv32_supervisor_reg_block_c)
      `uvm_field_object(trap_setup                , UVM_DEFAULT)
      `uvm_field_object(trap_handling             , UVM_DEFAULT)
      `uvm_field_object(protection_and_translation, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32_supervisor_reg_block", int has_coverage=UVM_NO_COVERAGE);
   
   /**
    * Creates sub-block(s).
    */
   extern virtual function void create_blocks();
   
   /**
    * Creates default register map.
    */
   extern virtual function void create_reg_map();
   
endclass : uvme_cv32_supervisor_reg_block_c


function uvme_cv32_supervisor_reg_block_c::new(string name="uvme_cv32_supervisor_reg_block", int has_coverage=UVM_NO_COVERAGE);
   
   super.new(name, has_coverage);
   
endfunction : new


function void uvme_cv32_supervisor_reg_block_c::create_blocks();
   
   trap_setup = uvml_riscv_csr_supervisor_trap_setup_reg_block_c#(32)::type_id::create("trap_setup");
   trap_setup.configure(this);
   trap_setup.build();
   
   trap_handling = uvml_riscv_csr_supervisor_trap_handling_reg_block_c#(32)::type_id::create("trap_handling");
   trap_handling.configure(this);
   trap_handling.build();
   
   protection_and_translation = uvml_riscv_csr_supervisor_protection_and_translation_reg_block_c#(32)::type_id::create("protection_and_translation");
   protection_and_translation.configure(this);
   protection_and_translation.build();
   
endfunction : create_blocks


function void uvme_cv32_supervisor_reg_block_c::create_reg_map();
   
   default_map = create_map(
      .name     ("default_map"),
      .base_addr(base_address),
      .n_bytes  (4),
      .endian   (UVM_LITTLE_ENDIAN)
   );
   
endfunction : create_reg_map


`endif // __UVME_CV32_SUPERVISOR_REG_BLOCK_SV__
