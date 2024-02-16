// Copyright 2023 OpenHW Group
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


`ifndef __UVMC_RVFI_REFERENCE_MODEL_SV__
`define __UVMC_RVFI_REFERENCE_MODEL_SV__

/**
 * Component that abstracts reference model class
 */
class uvmc_rvfi_reference_model#(int ILEN=DEFAULT_ILEN,
                                  int XLEN=DEFAULT_XLEN) extends uvm_component;

    uvm_analysis_imp_rvfi_instr#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvmc_rvfi_reference_model) m_analysis_imp;
    uvm_analysis_port#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN)) m_analysis_port;

   // Core configuration (used to extract list of CSRs)
   uvma_core_cntrl_cfg_c         cfg;

   `uvm_component_utils_begin(uvmc_rvfi_reference_model)
      `uvm_field_object(cfg,         UVM_DEFAULT | UVM_REFERENCE)
   `uvm_component_utils_end

   /**
    * Uses uvm_config_db to retrieve cfg and hand out to sub-components.
    */
   extern function void get_and_set_cfg();

   /**
    * Default constructor.
    */
   function new(string name="uvmc_rvfi_reference_model", uvm_component parent=null);

       super.new(name, parent);
       m_analysis_imp = new("m_analysis_imp", this);
       m_analysis_port = new("m_analysis_port", this);

   endfunction : new

   /**
    * Build phase
    */
   function void build_phase(uvm_phase phase);

        super.build_phase(phase);

        get_and_set_cfg();

   endfunction : build_phase

   /**
    * Virtual function for steping the reference model
    */
   virtual function uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) step (int i, uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);

       `uvm_fatal(get_type_name(), "RVFI Reference model must be overridden")

   endfunction : step

   /*
    * Write RVFI transactions to send to the scoreboard
    */
   virtual function void write_rvfi_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);

       uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t_reference_model = step(1, t);
       m_analysis_port.write(t_reference_model);

   endfunction : write_rvfi_instr

endclass : uvmc_rvfi_reference_model

function void uvmc_rvfi_reference_model::get_and_set_cfg();

   if (uvm_config_db#(uvma_core_cntrl_cfg_c)::get(this, "", "cfg", cfg)) begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
      uvm_config_db#(uvma_core_cntrl_cfg_c)::set(this, "*", "cfg", cfg);
   end
   else begin
      `uvm_fatal("CFG", $sformatf("%s: Could not find configuration handle", this.get_full_name()));
   end

endfunction : get_and_set_cfg

`endif // __UVMC_RVFI_REFERENCE_MODEL_SV__

