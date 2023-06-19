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


`ifndef __UVMA_CLIC_MON_TRN_SV__
`define __UVMA_CLIC_MON_TRN_SV__


/**
 * Object rebuilt from the Interrupt monitor Analog of uvma_clic_seq_item_c.
 */
class uvma_clic_mon_trn_c#(CLIC_ID_WIDTH) extends uvml_trn_mon_trn_c;

   uvma_clic_mon_action_enum action;

   int unsigned  id;

   `uvm_object_utils_begin(uvma_clic_mon_trn_c#(CLIC_ID_WIDTH))
      `uvm_field_enum(uvma_clic_mon_action_enum, action, UVM_DEFAULT)
      `uvm_field_int(id, UVM_DEFAULT)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_clic_mon_trn");

endclass : uvma_clic_mon_trn_c


`pragma protect begin


function uvma_clic_mon_trn_c::new(string name="uvma_clic_mon_trn");

   super.new(name);

endfunction : new


`pragma protect end


`endif // __UVMA_CLIC_MON_TRN_SV__
