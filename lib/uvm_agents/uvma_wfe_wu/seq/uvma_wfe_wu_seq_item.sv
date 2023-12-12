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


`ifndef __UVMA_WFE_WU_SEQ_ITEM_SV__
`define __UVMA_WFE_WU_SEQ_ITEM_SV__


/**
 * Object created by wfe wakeup agent sequences extending
 * uvma_wfe_wu_seq_base_c.
 */
class uvma_wfe_wu_seq_item_c extends uvml_trn_seq_item_c;

   bit wfe_wu_req;
   rand int unsigned active_cycles;

   rand uvma_wfe_wu_seq_item_action_e action         ; ///< What operation to perform

   `uvm_object_utils_begin(uvma_wfe_wu_seq_item_c)
      `uvm_field_enum(uvma_wfe_wu_seq_item_action_e, action         , UVM_DEFAULT)

      `uvm_field_int(wfe_wu_req   , UVM_DEFAULT)
      `uvm_field_int(active_cycles, UVM_DEFAULT)
   `uvm_object_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_wfe_wu_seq_item");

endclass : uvma_wfe_wu_seq_item_c


function uvma_wfe_wu_seq_item_c::new(string name="uvma_wfe_wu_seq_item");

   super.new(name);

endfunction : new


`endif // __UVMA_WFE_WU_SEQ_ITEM_SV__
