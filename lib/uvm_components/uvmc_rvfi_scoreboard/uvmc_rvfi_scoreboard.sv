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
                                  int XLEN=DEFAULT_XLEN) extends uvm_scoreboard#(
   .T_TRN  (uvml_trn_seq_item_c),
   .T_CFG  (uvma_rvfi_cfg_c    ),
   .T_CNTXT(uvma_rvfi_cntxt_c  )
);

   uvm_analysis_imp_rvfi_instr_reference_model#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvmc_rvfi_scoreboard_c) m_imp_reference_model;
   uvm_analysis_imp_rvfi_instr_core#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvmc_rvfi_scoreboard_c) m_imp_core;

   `uvm_component_param_utils(uvmc_rvfi_scoreboard_c)

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

   /*
    *  Run Phase
    */
   extern task run_phase(uvm_phase phase);

   extern virtual function void write_rvfi_instr_reference_model(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);

   extern virtual function void write_rvfi_instr_core(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);

endclass : uvmc_rvfi_scoreboard_c

task uvmc_rvfi_scoreboard_c::run_phase(uvm_phase phase);

    uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t_reference_model;
    uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t_core;

    t_reference_model = new("t_reference_model");
    t_core = new("t_core");
    forever begin
        @(reference_model.size > 0)
        while (reference_model.size > 0)
        begin
            t_reference_model = reference_model.pop_front();
            t_core = core.pop_front();
            rvfi_compare(t_core.seq2rvfi(), t_reference_model.seq2rvfi());
        end
    end

endtask : run_phase

function void uvmc_rvfi_scoreboard_c::write_rvfi_instr_reference_model(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);

    reference_model.push_back(t);

endfunction : write_rvfi_instr_reference_model

function void uvmc_rvfi_scoreboard_c::write_rvfi_instr_core(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);

    core.push_back(t);

endfunction : write_rvfi_instr_core

`endif // __UVMA_RVFI_MON_TRN_LOGGER_SV__

