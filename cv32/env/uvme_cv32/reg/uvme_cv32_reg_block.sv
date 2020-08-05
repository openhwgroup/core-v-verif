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


`ifndef __UVME_CV32_REG_BLOCK_SV__
`define __UVME_CV32_REG_BLOCK_SV__


/**
 * Example top-level register block based upon Moore.io's RISC-V CSR UVML
 * Library.
 */
class uvme_cv32_reg_block_c extends uvml_ral_reg_block_c;
   
   // Sub-Blocks
   rand uvme_cv32_user_reg_block_c        user      ;
   rand uvme_cv32_supervisor_reg_block_c  supervisor;
   rand uvme_cv32_hypervisor_reg_block_c  hypervisor;
   rand uvme_cv32_machine_reg_block_c     machine   ;
   
   
   `uvm_object_utils_begin(uvme_cv32_reg_block_c)
      `uvm_field_object(user      , UVM_DEFAULT)
      `uvm_field_object(supervisor, UVM_DEFAULT)
      `uvm_field_object(hypervisor, UVM_DEFAULT)
      `uvm_field_object(machine   , UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32_reg_block", int has_coverage=UVM_NO_COVERAGE);
   
   /**
    * Creates sub-block(s).
    */
   extern virtual function void create_blocks();
   
   /**
    * Creates default register map.
    */
   extern virtual function void create_reg_map();
   
endclass : uvme_cv32_reg_block_c


function uvme_cv32_reg_block_c::new(string name="uvme_cv32_reg_block", int has_coverage=UVM_NO_COVERAGE);
   
   super.new(name, has_coverage);
   
endfunction : new


function void uvme_cv32_reg_block_c::create_blocks();
   
   user = uvme_cv32_ml_abc_reg_block_c::type_id::create("user");
   user.configure(this);
   user.build();
   
   supervisor = uvme_cv32_ml_abc_reg_block_c::type_id::create("supervisor");
   supervisor.configure(this);
   supervisor.build();
   
   hypervisor = uvme_cv32_ml_abc_reg_block_c::type_id::create("hypervisor");
   hypervisor.configure(this);
   hypervisor.build();
   
   machine = uvme_cv32_ml_abc_reg_block_c::type_id::create("machine");
   machine.configure(this);
   machine.build();
   
endfunction : create_blocks


function void uvme_cv32_reg_block_c::create_reg_map();
   
   default_map = create_map(
      .name     ("default_map"),
      .base_addr(base_address),
      .n_bytes  (4),
      .endian   (UVM_LITTLE_ENDIAN)
   );
   
endfunction : create_reg_map


`endif // __UVME_CV32_REG_BLOCK_SV__
