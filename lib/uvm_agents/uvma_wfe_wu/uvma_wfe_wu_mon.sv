//
// Copyright 2023 Silicon Labs Inc.
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
//


`ifndef __UVMA_WFE_WU_MON_SV__
`define __UVMA_WFE_WU_MON_SV__


/**
 * Component sampling transactions from a wfe wakeup virtual interface
 * (uvma_wfe_wu_if_t).
 */
class uvma_wfe_wu_mon_c extends uvm_monitor;

   // Objects
   uvma_wfe_wu_cfg_c    cfg;
   uvma_wfe_wu_cntxt_c  cntxt;

   // TLM
   uvm_analysis_port#(uvma_wfe_wu_mon_trn_c)  ap;


   `uvm_component_utils_begin(uvma_wfe_wu_mon_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_wfe_wu_mon", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Oversees monitoring
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Empty, classes extending this monitor can do their intercept here.
    */
   extern function void process_trn(ref uvma_wfe_wu_mon_trn_c trn);

   extern virtual task sample_trn(output uvma_wfe_wu_mon_trn_c trn);

endclass : uvma_wfe_wu_mon_c


function uvma_wfe_wu_mon_c::new(string name="uvma_wfe_wu_mon", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_wfe_wu_mon_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_wfe_wu_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvma_wfe_wu_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   ap = new("ap", this);

endfunction : build_phase


task uvma_wfe_wu_mon_c::run_phase(uvm_phase phase);

   uvma_wfe_wu_mon_trn_c  trn;

   super.run_phase(phase);

   if (cfg.enabled) begin
      fork
         begin : clk
            forever begin
               sample_trn(trn);
               process_trn(trn);
               ap.write   (trn);
               `uvml_hrtbt()
            end
         end

      join_none
   end

endtask : run_phase

task uvma_wfe_wu_mon_c::sample_trn(output uvma_wfe_wu_mon_trn_c trn);
  bit sampled_trn = 0;

  trn = uvma_wfe_wu_mon_trn_c::type_id::create("trn");

  do begin
    @(cntxt.vif.mon_cb);
    // TODO sample trn from vif
  end while (!sampled_trn);
endtask : sample_trn

function void uvma_wfe_wu_mon_c::process_trn(ref uvma_wfe_wu_mon_trn_c trn);

   // Empty

endfunction : process_trn

`endif // __UVMA_WFE_WU_MON_SV__
