// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVMA_RVFI_CNTXT_SV__
`define __UVMA_RVFI_CNTXT_SV__

/**
 * Object encapsulating all state variables for all Rvfi agent
 * (uvma_rvfi_agent_c) components.
 */
class uvma_rvfi_cntxt_c#(int ILEN=DEFAULT_ILEN,
                         int XLEN=DEFAULT_XLEN) extends uvm_object;

   // Handle to instruction retirement interface
   // The number of interfaces will be equal to the _nret_ value in the configuration object
   virtual uvma_rvfi_instr_if#(ILEN,XLEN) instr_vif[];

   // Handle to CSR interfaces
   virtual uvma_rvfi_csr_if#(XLEN)       csr_vif[string][];
   virtual uvma_rvfi_unified_csr_if#(4096,XLEN) csr_unified_vif[];

   // Events
   uvm_event  sample_cfg_e;
   uvm_event  sample_cntxt_e;

   `uvm_object_utils_begin(uvma_rvfi_cntxt_c)
      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
   `uvm_object_utils_end

   /**
    * Builds events.
    */
   extern function new(string name="uvma_rvfi_cntxt");

   /**
    * TODO Describe uvma_rvfi_cntxt_c::reset()
    */
   extern function void reset();

endclass : uvma_rvfi_cntxt_c


`pragma protect begin


function uvma_rvfi_cntxt_c::new(string name="uvma_rvfi_cntxt");

   super.new(name);

   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");

endfunction : new

function void uvma_rvfi_cntxt_c::reset();

endfunction : reset


`pragma protect end


`endif // __UVMA_RVFI_CNTXT_SV__
