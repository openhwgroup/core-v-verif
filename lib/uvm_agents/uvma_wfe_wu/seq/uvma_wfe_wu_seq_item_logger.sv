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


`ifndef __UVMA_WFE_WU_SEQ_ITEM_LOGGER_SV__
`define __UVMA_WFE_WU_SEQ_ITEM_LOGGER_SV__


/**
 * Component writing wfe wakeup sequence items debug data to disk as plain
 * text.
 */
class uvma_wfe_wu_seq_item_logger_c extends uvml_logs_seq_item_logger_c#(
   .T_TRN  (uvma_wfe_wu_seq_item_c),
   .T_CFG  (uvma_wfe_wu_cfg_c     ),
   .T_CNTXT(uvma_wfe_wu_cntxt_c   )
);

   `uvm_component_utils(uvma_wfe_wu_seq_item_logger_c)


   /**
    * Default constructor.
    */
   function new(string name="uvma_wfe_wu_seq_item_logger", uvm_component parent=null);

      super.new(name, parent);

   endfunction : new

   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_wfe_wu_seq_item_c t);
   endfunction : write

   /**
    * Writes log header to disk.
    */
   virtual function void print_header();
   endfunction : print_header

endclass : uvma_wfe_wu_seq_item_logger_c


/**
 * Component writing Clock & Reset monitor transactions debug data to disk as
 * JavaScript Object Notation (JSON).
 */
class uvma_wfe_wu_seq_item_logger_json_c extends uvma_wfe_wu_seq_item_logger_c;

   `uvm_component_utils(uvma_wfe_wu_seq_item_logger_json_c)


   /**
    * Set file extension to '.json'.
    */
   function new(string name="uvma_wfe_wu_seq_item_logger_json", uvm_component parent=null);

      super.new(name, parent);
      fextension = "json";

   endfunction : new

   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_wfe_wu_seq_item_c t);
   endfunction : write

   /**
    * Empty function.
    */
   virtual function void print_header();

      // Do nothing: JSON files do not use headers.

   endfunction : print_header

endclass : uvma_wfe_wu_seq_item_logger_json_c


`endif // __UVMA_WFE_WU_SEQ_ITEM_LOGGER_SV__
