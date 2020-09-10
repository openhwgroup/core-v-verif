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


`ifndef __UVME_CV32_HYPERVISOR_REG_BLOCK_SV__
`define __UVME_CV32_HYPERVISOR_REG_BLOCK_SV__


/**
 * Example hypervisor-level register block based upon Moore.io's RISC-V CSR UVM
 * Library.
 */
class uvme_cv32_hypervisor_reg_block_c extends uvml_ral_reg_block_c;
   
   // Sub-Blocks
   // TODO Add sub-block(s)
   //      Ex: rand uvme_cv32_ml_abc_reg_block_c  abc;
   
   // Registers
   // TODO Add register(s)
   //      Ex: rand uvme_cv32_ml_xyz_reg_c  xyz;
   
   
   `uvm_object_utils_begin(uvme_cv32_hypervisor_reg_block_c)
      // TODO Add field macros for sub-block(s) and register(s)
      //      Ex: `uvm_field_object(abc, UVM_DEFAULT)
      //          `uvm_field_object(xyz, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32_hypervisor_reg_block", int has_coverage=UVM_NO_COVERAGE);
   
   /**
    * Creates sub-block(s).
    */
   extern virtual function void create_blocks();
   
   /**
    * Creates register(s).
    */
   extern virtual function void create_regs();
   
   /**
    * Creates default register map.
    */
   extern virtual function void create_reg_map();
   
   /**
    * Adds register(s) to register map.
    */
   extern virtual function void add_regs_to_map();
   
endclass : uvme_cv32_hypervisor_reg_block_c


function uvme_cv32_hypervisor_reg_block_c::new(string name="uvme_cv32_hypervisor_reg_block", int has_coverage=UVM_NO_COVERAGE);
   
   super.new(name, has_coverage);
   
endfunction : new


function void uvme_cv32_hypervisor_reg_block_c::create_blocks();
   
   // TODO Implement uvme_cv32_hypervisor_reg_block_c::create_blocks()
   //      Ex: abc = uvme_cv32_ml_abc_reg_block_c::type_id::create("abc");
   //          abc.configure(this);
   //          abc.build();
   
endfunction : create_blocks


function void uvme_cv32_hypervisor_reg_block_c::create_regs();
   
   // TODO Implement uvme_cv32_hypervisor_reg_block_c::create_regs()
   //      Ex:  xyz = uvme_cv32_ml_xyz_reg_c::type_id::create("xyz");
   //           xyz.configure(this);
   //           xyz.build();
   
endfunction : create_regs


function void uvme_cv32_hypervisor_reg_block_c::create_reg_map();
   
   default_map = create_map(
      .name     ("default_map"),
      .base_addr(base_address),
      .n_bytes  (4),
      .endian   (UVM_LITTLE_ENDIAN)
   );
   
endfunction : create_reg_map


function void uvme_cv32_hypervisor_reg_block_c::add_regs_to_map();
   
   // TODO Implement uvme_cv32_hypervisor_reg_block_c::add_regs_to_map()
   //      Ex: default_map.add_reg(
   //             .rg    (xyz),
   //             .offset(32'h00_00_00_00),
   //             .rights("RW")
   //          );
   
endfunction : add_regs_to_map


`endif // __UVME_CV32_HYPERVISOR_REG_BLOCK_SV__
