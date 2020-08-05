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


`ifndef __UVME_CV32_SB_SV__
`define __UVME_CV32_SB_SV__


/**
 * Component encapsulating scoreboards which compare CV32
 * DUT's expected (from predictor) vs. actual (monitored) transactions.
 */
class uvme_cv32_sb_c extends uvm_scoreboard;
   
   // Objects
   uvme_cv32_cfg_c    cfg;
   uvme_cv32_cntxt_c  cntxt;
   
   // Components
   uvml_sb_simplex_c  gpr_rv32i_sb;
   uvml_sb_simplex_c  gpr_ext_m_sb;
   uvml_sb_simplex_c  gpr_ext_f_sb;
   uvml_sb_simplex_c  gpr_ext_c_sb;
   
   
   `uvm_component_utils_begin(uvme_cv32_sb_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
      
      `uvm_field_object(gpr_rv32i_sb, UVM_DEFAULT)
      `uvm_field_object(gpr_ext_m_sb, UVM_DEFAULT)
      `uvm_field_object(gpr_ext_f_sb, UVM_DEFAULT)
      `uvm_field_object(gpr_ext_c_sb, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32_sb", uvm_component parent=null);
   
   /**
    * Create and configures sub-scoreboards via:
    * 1. assign_cfg()
    * 2. assign_cntxt()
    * 3. create_sbs()
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * Assigns configuration handles.
    */
   extern virtual function void assign_cfg();
   
   /**
    * Assigns context handles.
    */
   extern virtual function void assign_cntxt();
   
   /**
    * Creates sub-scoreboard components.
    */
   extern virtual function void create_sbs();
   
endclass : uvme_cv32_sb_c


function uvme_cv32_sb_c::new(string name="uvme_cv32_sb", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvme_cv32_sb_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvme_cv32_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvme_cv32_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   assign_cfg  ();
   assign_cntxt();
   create_sbs  ();
   
endfunction : build_phase


function void uvme_cv32_sb_c::assign_cfg();
   
   uvm_config_db#(uvml_sb_cfg_c)::set(this, "gpr_rv32i_sb", "cfg", cfg.sb_gpr_rv32i_cfg);
   uvm_config_db#(uvml_sb_cfg_c)::set(this, "gpr_ext_m_sb", "cfg", cfg.sb_gpr_ext_m_cfg);
   uvm_config_db#(uvml_sb_cfg_c)::set(this, "gpr_ext_f_sb", "cfg", cfg.sb_gpr_ext_f_cfg);
   uvm_config_db#(uvml_sb_cfg_c)::set(this, "gpr_ext_c_sb", "cfg", cfg.sb_gpr_ext_c_cfg);
   
endfunction : assign_cfg


function void uvme_cv32_sb_c::assign_cntxt();
   
   uvm_config_db#(uvml_sb_cntxt_c)::set(this, "gpr_rv32i_sb", "cntxt", cntxt.sb_gpr_rv32i_cntxt);
   uvm_config_db#(uvml_sb_cntxt_c)::set(this, "gpr_ext_m_sb", "cntxt", cntxt.sb_gpr_ext_m_cntxt);
   uvm_config_db#(uvml_sb_cntxt_c)::set(this, "gpr_ext_f_sb", "cntxt", cntxt.sb_gpr_ext_f_cntxt);
   uvm_config_db#(uvml_sb_cntxt_c)::set(this, "gpr_ext_c_sb", "cntxt", cntxt.sb_gpr_ext_c_cntxt);
   
endfunction : assign_cntxt


function void uvme_cv32_sb_c::create_sbs();
   
   gpr_rv32i_sb = uvml_sb_simplex_c::type_id::create("gpr_rv32i_sb", this);
   gpr_ext_m_sb = uvml_sb_simplex_c::type_id::create("gpr_ext_m_sb", this);
   gpr_ext_f_sb = uvml_sb_simplex_c::type_id::create("gpr_ext_f_sb", this);
   gpr_ext_c_sb = uvml_sb_simplex_c::type_id::create("gpr_ext_c_sb", this);
   
endfunction : create_sbs


`endif // __UVME_CV32_SB_SV__
