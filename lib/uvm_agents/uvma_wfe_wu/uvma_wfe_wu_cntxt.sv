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


`ifndef __UVMA_WFE_WU_CNTXT_SV__
`define __UVMA_WFE_WU_CNTXT_SV__


/**
 * Object encapsulating all state variables for all wfe wakeup agent
 * (uvma_wfe_wu_agent_c) components.
 */
class uvma_wfe_wu_cntxt_c extends uvm_object;

   // Handle to agent interface
   virtual uvma_wfe_wu_if_t  vif;

   // Events
   uvm_event  sample_cfg_e  ; ///< Event to trigger functional coverage sampling of cfg
   uvm_event  sample_cntxt_e; ///< Event to trigger functional coverage sampling of cntxt


   `uvm_object_utils_begin(uvma_wfe_wu_cntxt_c)
      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
   `uvm_object_utils_end


   /**
    * Builds events.
    */
   extern function new(string name="uvma_wfe_wu_cntxt");

   /**
    * Resets integrals to their default values.
    */
   extern function void reset();

endclass : uvma_wfe_wu_cntxt_c


function uvma_wfe_wu_cntxt_c::new(string name="uvma_wfe_wu_cntxt");

   super.new(name);

   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");

   reset();

endfunction : new


function void uvma_wfe_wu_cntxt_c::reset();

endfunction : reset


`endif // __UVMA_WFE_WU_CNTXT_SV__
