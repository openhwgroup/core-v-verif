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


`ifndef __UVME_CV32_CFG_SV__
`define __UVME_CV32_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running
 * CV32 environment (uvme_cv32_env_c) components.
 */
class uvme_cv32_cfg_c extends uvm_object;
   
   // Integrals
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;
   rand bit                      scoreboarding_enabled;
   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;
   rand int unsigned             sys_clk_period;
   
   // Agent cfg handles
   rand uvma_clknrst_cfg_c       clknrst_cfg;
   rand uvma_riscv_tracer_cfg_c  tracer_cfg ;
   rand uvma_interrupt_cfg_c     interrupt_cfg;
   
   // Objects
   rand uvme_cv32_reg_block_c  ral;
   rand uvml_sb_cfg_c          sb_gpr_rv32i_cfg;
   rand uvml_sb_cfg_c          sb_gpr_ext_m_cfg;
   rand uvml_sb_cfg_c          sb_gpr_ext_f_cfg;
   rand uvml_sb_cfg_c          sb_gpr_ext_c_cfg;
   
   
   `uvm_object_utils_begin(uvme_cv32_cfg_c)
      `uvm_field_int (                         enabled              , UVM_DEFAULT          )
      `uvm_field_enum(uvm_active_passive_enum, is_active            , UVM_DEFAULT          )
      `uvm_field_int (                         scoreboarding_enabled, UVM_DEFAULT          )
      `uvm_field_int (                         cov_model_enabled    , UVM_DEFAULT          )
      `uvm_field_int (                         trn_log_enabled      , UVM_DEFAULT          )
      `uvm_field_int (                         sys_clk_period       , UVM_DEFAULT + UVM_DEC)
      
      `uvm_field_object(clknrst_cfg  , UVM_DEFAULT)
      `uvm_field_object(tracer_cfg   , UVM_DEFAULT)
      `uvm_field_object(interrupt_cfg, UVM_DEFAULT)
      
      `uvm_field_object(ral             , UVM_DEFAULT)
      `uvm_field_object(sb_gpr_rv32i_cfg, UVM_DEFAULT)
      `uvm_field_object(sb_gpr_ext_m_cfg, UVM_DEFAULT)
      `uvm_field_object(sb_gpr_ext_f_cfg, UVM_DEFAULT)
      `uvm_field_object(sb_gpr_ext_c_cfg, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   constraint defaults_cons {
      soft enabled                == 0;
      soft is_active              == UVM_PASSIVE;
      soft scoreboarding_enabled  == 0;
      soft cov_model_enabled      == 0;
      soft trn_log_enabled        == 1;
      soft sys_clk_period         == uvme_cv32_sys_default_clk_period; // see uvme_cv32_constants.sv
   }
   
   constraint agent_cfg_cons {
      if (enabled) {
         clknrst_cfg.enabled == 1;
         //tracer_cfg .enabled == 1;
         interrupt_cfg.enabled == 1;
      }
      tracer_cfg.enabled == 0; // DOP TEMP
      
      if (is_active == UVM_ACTIVE) {
         clknrst_cfg.is_active == UVM_ACTIVE;
         interrupt_cfg.is_active == UVM_ACTIVE;
      }
      tracer_cfg.is_active == UVM_PASSIVE;
      
      if (trn_log_enabled) {
         clknrst_cfg.trn_log_enabled == 1;
         tracer_cfg .trn_log_enabled == 1;
         interrupt_cfg.trn_log_enabled == 1;
      }

      if (scoreboarding_enabled) {
	 sb_gpr_rv32i_cfg.enabled == 1;
	 sb_gpr_ext_m_cfg.enabled == 1;
	 sb_gpr_ext_f_cfg.enabled == 1;
	 sb_gpr_ext_c_cfg.enabled == 1;
      }
      else {
	 sb_gpr_rv32i_cfg.enabled == 0;
	 sb_gpr_ext_m_cfg.enabled == 0;
	 sb_gpr_ext_f_cfg.enabled == 0;
	 sb_gpr_ext_c_cfg.enabled == 0;
      }
   }
   
   
   /**
    * Creates sub-configuration objects.
    */
   extern function new(string name="uvme_cv32_cfg");
   
endclass : uvme_cv32_cfg_c


function uvme_cv32_cfg_c::new(string name="uvme_cv32_cfg");
   
   super.new(name);
   
   clknrst_cfg   = uvma_clknrst_cfg_c     ::type_id::create("clknrst_cfg"  );
   tracer_cfg    = uvma_riscv_tracer_cfg_c::type_id::create("tracer_cfg"   );
   interrupt_cfg = uvma_interrupt_cfg_c   ::type_id::create("interrupt_cfg");
   
   ral = uvme_cv32_reg_block_c::type_id::create("cv32_ral");
   ral.build();
   ral.lock_model();
   
   sb_gpr_rv32i_cfg = uvml_sb_cfg_c::type_id::create("sb_gpr_rv32i_cfg");
   sb_gpr_ext_m_cfg = uvml_sb_cfg_c::type_id::create("sb_gpr_ext_m_cfg");
   sb_gpr_ext_f_cfg = uvml_sb_cfg_c::type_id::create("sb_gpr_ext_f_cfg");
   sb_gpr_ext_c_cfg = uvml_sb_cfg_c::type_id::create("sb_gpr_ext_c_cfg");
   
endfunction : new


`endif // __UVME_CV32_CFG_SV__
