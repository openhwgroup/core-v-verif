// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2022 Silicon Labs, Inc.
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


`ifndef __UVMA_CLIC_CNTXT_SV__
`define __UVMA_CLIC_CNTXT_SV__


/**
 * Object encapsulating all state variables for all Interrupt agent
 * (uvma_clic_agent_c) components.
 */
class uvma_clic_cntxt_c#(CLIC_ID_WIDTH) extends uvm_object;

   // Handle to agent interface
   virtual uvma_clic_if_t#(CLIC_ID_WIDTH)  vif;

   // Events
   uvm_event  sample_cfg_e;
   uvm_event  sample_cntxt_e;

   `uvm_object_utils_begin(uvma_clic_cntxt_c#(CLIC_ID_WIDTH))
      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
   `uvm_object_utils_end

   /**
    * Builds events.
    */
   extern function new(string name="uvma_clic_cntxt");

   /**
    * TODO Describe uvma_clic_cntxt_c::reset()
    */
   extern function void reset();

endclass : uvma_clic_cntxt_c


`pragma protect begin


function uvma_clic_cntxt_c::new(string name="uvma_clic_cntxt");

   super.new(name);

   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");

endfunction : new

function void uvma_clic_cntxt_c::reset();

   // TODO Implement uvma_clic_cntxt_c::reset()

endfunction : reset


`pragma protect end


`endif // __UVMA_CLIC_CNTXT_SV__
