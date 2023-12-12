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


`ifndef __UVMA_WFE_WU_SEQ_LIB_SV__
`define __UVMA_WFE_WU_SEQ_LIB_SV__


/**
 * Object holding sequence library for wfe wakeup agent.
 */
class uvma_wfe_wu_seq_lib_c extends uvm_sequence_library#(
   .REQ(uvma_wfe_wu_seq_item_c),
   .RSP(uvma_wfe_wu_seq_item_c)
);

   `uvm_object_utils          (uvma_wfe_wu_seq_lib_c)
   `uvm_sequence_library_utils(uvma_wfe_wu_seq_lib_c)


   /**
    * Initializes sequence library
    */
   extern function new(string name="uvma_wfe_wu_seq_lib");

endclass : uvma_wfe_wu_seq_lib_c


function uvma_wfe_wu_seq_lib_c::new(string name="uvma_wfe_wu_seq_lib");

   super.new(name);
   init_sequence_library();

endfunction : new


`endif // __UVMA_WFE_WU_SEQ_LIB_SV__
