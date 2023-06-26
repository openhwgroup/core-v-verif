// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group

/**** AXI4 sequence item : Read Address channel  ****/


`ifndef __UVMA_AXI_AR_ITEM_SV__
`define __UVMA_AXI_AR_ITEM_SV__

class uvma_axi_ar_item_c extends uvma_axi_base_seq_item_c;

   int                             ar_latency;

   `uvm_object_utils_begin(uvma_axi_ar_item_c)
      `uvm_field_int(ar_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE);
   `uvm_object_utils_end

   function new(string name = "uvma_axi_ar_item_c");
      super.new(name);
   endfunction

endclass

`endif
