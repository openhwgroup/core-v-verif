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


`ifndef __UVME_CV32_CNTXT_SV__
`define __UVME_CV32_CNTXT_SV__


/**
 * Object encapsulating all state variables for CV32 environment
 * (uvme_cv32_env_c) components.
 */
class uvme_cv32_cntxt_c extends uvm_object;
   
   // Agent context handles
   uvma_clknrst_cntxt_c       clknrst_cntxt;
   uvma_riscv_tracer_cntxt_c  tracer_cntxt ;
   uvma_interrupt_cntxt_c     interrupt_cntxt;
   
   // Scoreboard context handles
   uvml_sb_cntxt_c  sb_gpr_rv32i_cntxt;
   uvml_sb_cntxt_c  sb_gpr_ext_m_cntxt;
   uvml_sb_cntxt_c  sb_gpr_ext_f_cntxt;
   uvml_sb_cntxt_c  sb_gpr_ext_c_cntxt;
   
   // Events
   uvm_event  sample_cfg_e;
   uvm_event  sample_cntxt_e;

   // Interfaces
   virtual uvmt_cv32_isa_covg_if  isa_covg_vif;
   
   
   `uvm_object_utils_begin(uvme_cv32_cntxt_c)
      `uvm_field_object(clknrst_cntxt  , UVM_DEFAULT)
      `uvm_field_object(tracer_cntxt   , UVM_DEFAULT)
      `uvm_field_object(interrupt_cntxt, UVM_DEFAULT)
      
      `uvm_field_object(sb_gpr_rv32i_cntxt, UVM_DEFAULT)
      `uvm_field_object(sb_gpr_ext_m_cntxt, UVM_DEFAULT)
      `uvm_field_object(sb_gpr_ext_f_cntxt, UVM_DEFAULT)
      `uvm_field_object(sb_gpr_ext_c_cntxt, UVM_DEFAULT)
      
      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Builds events and sub-context objects.
    */
   extern function new(string name="uvme_cv32_cntxt");
   
endclass : uvme_cv32_cntxt_c


function uvme_cv32_cntxt_c::new(string name="uvme_cv32_cntxt");
   
   super.new(name);
   
   clknrst_cntxt   = uvma_clknrst_cntxt_c     ::type_id::create("clknrst_cntxt"  );
   tracer_cntxt    = uvma_riscv_tracer_cntxt_c::type_id::create("tracer_cntxt"   );
   interrupt_cntxt = uvma_interrupt_cntxt_c   ::type_id::create("interrupt_cntxt");
   
   sb_gpr_rv32i_cntxt = uvml_sb_cntxt_c::type_id::create("sb_gpr_rv32i_cntxt");
   sb_gpr_ext_m_cntxt = uvml_sb_cntxt_c::type_id::create("sb_gpr_ext_m_cntxt");
   sb_gpr_ext_f_cntxt = uvml_sb_cntxt_c::type_id::create("sb_gpr_ext_f_cntxt");
   sb_gpr_ext_c_cntxt = uvml_sb_cntxt_c::type_id::create("sb_gpr_ext_c_cntxt");
   
   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");
   
endfunction : new


`endif // __UVME_CV32_CNTXT_SV__
