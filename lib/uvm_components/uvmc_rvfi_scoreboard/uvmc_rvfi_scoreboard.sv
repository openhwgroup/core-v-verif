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


`ifndef __uvmc_rvfi_scoreboard_SV__
`define __uvmc_rvfi_scoreboard_SV__

`uvm_analysis_imp_decl(_rvfi_instr_reference_model)
`uvm_analysis_imp_decl(_rvfi_instr_core)

/*
 * Scoreboard component which compares RVFI transactions comming from the
 * core and the reference model
 */
class uvmc_rvfi_scoreboard_c#(int ILEN=DEFAULT_ILEN,
                                  int XLEN=DEFAULT_XLEN) extends uvm_scoreboard;

   uvm_analysis_imp_rvfi_instr_reference_model#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvmc_rvfi_scoreboard_c) m_imp_reference_model;
   uvm_analysis_imp_rvfi_instr_core#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvmc_rvfi_scoreboard_c) m_imp_core;

   // Core configuration (used to extract list of CSRs)
   uvma_core_cntrl_cfg_c         cfg;
   bit [XLEN-1:0] sentinel_value;
   bit            sentinel_enable;

   `uvm_component_utils_begin(uvmc_rvfi_scoreboard_c)
      `uvm_field_object(cfg,         UVM_DEFAULT | UVM_REFERENCE)
   `uvm_component_utils_end

    uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) core[$];
    uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) reference_model[$];

   /*
    * Default constructor.
    */
    function new(string name="uvmc_rvfi_scoreboard_c", uvm_component parent=null);

        super.new(name, parent);

        m_imp_reference_model = new("m_imp_reference_model", this);
        m_imp_core = new("m_imp_core", this);

    endfunction : new

   /**
    * Uses uvm_config_db to retrieve cfg and hand out to sub-components.
    */
   extern function void get_and_set_cfg();

   /*
    *  Build Phase
    */
   extern function void build_phase(uvm_phase phase);

   /*
    *  Run Phase
    */
   extern task run_phase(uvm_phase phase);

   extern virtual function void write_rvfi_instr_reference_model(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);

   extern virtual function void write_rvfi_instr_core(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);

endclass : uvmc_rvfi_scoreboard_c

function void uvmc_rvfi_scoreboard_c::build_phase(uvm_phase phase);
    st_core_cntrl_cfg st;

    get_and_set_cfg();

    st = cfg.to_struct();

    rvfi_initialize(st);

    if($test$plusargs("sentinel_value")) begin
        if ($value$plusargs("sentinel_value=%h", sentinel_value)) begin
            sentinel_enable = '1;
        end
    end

endfunction : build_phase

task uvmc_rvfi_scoreboard_c::run_phase(uvm_phase phase);

    uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t_reference_model;
    uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t_core;

    bit sim_finished;

    t_reference_model = new("t_reference_model");
    t_core = new("t_core");

    sim_finished = 0;
    phase.raise_objection(this);
    while (!sim_finished) begin
        @(reference_model.size > 0)
        while (reference_model.size > 0 && !sim_finished)
        begin
            t_reference_model = reference_model.pop_front();
            t_core = core.pop_front();
            rvfi_compare(t_core.seq2rvfi(), t_reference_model.seq2rvfi());

            if (t_reference_model.halt || (sentinel_enable && (sentinel_value == t_reference_model.insn)))
                sim_finished = 1;
        end
    end
    phase.drop_objection(this);

endtask : run_phase

function void uvmc_rvfi_scoreboard_c::write_rvfi_instr_reference_model(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);

    reference_model.push_back(t);

endfunction : write_rvfi_instr_reference_model

function void uvmc_rvfi_scoreboard_c::write_rvfi_instr_core(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);

    core.push_back(t);

endfunction : write_rvfi_instr_core

function void uvmc_rvfi_scoreboard_c::get_and_set_cfg();

   if (uvm_config_db#(uvma_core_cntrl_cfg_c)::get(this, "", "cfg", cfg)) begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
      uvm_config_db#(uvma_core_cntrl_cfg_c)::set(this, "*", "cfg", cfg);
   end
   else begin
      `uvm_fatal("CFG", $sformatf("%s: Could not find configuration handle", this.get_full_name()));
   end

endfunction : get_and_set_cfg

`endif // __UVMA_RVFI_MON_TRN_LOGGER_SV__

