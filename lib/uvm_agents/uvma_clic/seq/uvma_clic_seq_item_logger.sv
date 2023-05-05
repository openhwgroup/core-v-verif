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


`ifndef __UVMA_CLIC_SEQ_ITEM_LOGGER_SV__
`define __UVMA_CLIC_SEQ_ITEM_LOGGER_SV__


/**
 * Component writing Interrupt sequence items interrupt data to disk as plain text.
 */
class uvma_clic_seq_item_logger_c#(CLIC_ID_WIDTH) extends uvml_logs_seq_item_logger_c#(
   .T_TRN  (uvma_clic_seq_item_c),
   .T_CFG  (uvma_clic_cfg_c     ),
   .T_CNTXT(uvma_clic_cntxt_c#(CLIC_ID_WIDTH))
);

   `uvm_component_utils(uvma_clic_seq_item_logger_c#(CLIC_ID_WIDTH))


   /**
    * Default constructor.
    */
   function new(string name="uvma_clic_seq_item_logger", uvm_component parent=null);

      super.new(name, parent);

   endfunction : new

   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_clic_seq_item_c t);

      // TODO Implement uvma_clic_seq_item_logger_c::write()
      // Ex: fwrite($sformatf(" %t | %08h | %02b | %04d | %02h |", $realtime(), t.a, t.b, t.c, t.d));

   endfunction : write

   /**
    * Writes log header to disk.
    */
   virtual function void print_header();

      // TODO Implement uvma_clic_seq_item_logger_c::print_header()
      // Ex: fwrite("----------------------------------------------");
      //     fwrite(" TIME | FIELD A | FIELD B | FIELD C | FIELD D ");
      //     fwrite("----------------------------------------------");

   endfunction : print_header

endclass : uvma_clic_seq_item_logger_c


/**
 * Component writing INTERRUPT monitor transactions interrupt data to disk as JavaScript Object Notation (JSON).
 */
class uvma_clic_seq_item_logger_json_c#(CLIC_ID_WIDTH) extends uvma_clic_seq_item_logger_c#(CLIC_ID_WIDTH);

   `uvm_component_utils(uvma_clic_seq_item_logger_json_c)


   /**
    * Set file extension to '.json'.
    */
   function new(string name="uvma_clic_seq_item_logger_json", uvm_component parent=null);

      super.new(name, parent);
      fextension = "json";

   endfunction : new

   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_clic_seq_item_c t);

      // TODO Implement uvma_clic_seq_item_logger_json_c::write()
      // Ex: fwrite({"{",
      //       $sformatf("\"time\":\"%0t\",", $realtime()),
      //       $sformatf("\"a\":%h,"        , t.a        ),
      //       $sformatf("\"b\":%b,"        , t.b        ),
      //       $sformatf("\"c\":%d,"        , t.c        ),
      //       $sformatf("\"d\":%h,"        , t.c        ),
      //     "},"});

   endfunction : write

   /**
    * Empty function.
    */
   virtual function void print_header();

      // Do nothing: JSON files do not use headers.

   endfunction : print_header

endclass : uvma_clic_seq_item_logger_json_c

`endif // __UVMA_CLIC_SEQ_ITEM_LOGGER_SV__
