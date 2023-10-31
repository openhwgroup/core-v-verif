//
// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
//

`ifndef __UVMA_OBI_MEMORY_VP_BASE_SEQ_SV__
`define __UVMA_OBI_MEMORY_VP_BASE_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
virtual class uvma_obi_memory_vp_base_seq_c#(
   parameter AUSER_WIDTH = `UVMA_OBI_MEMORY_AUSER_DEFAULT_WIDTH, ///< Width of the auser signal. RI5CY, Ibex, CV32E40* do not have the auser signal.
   parameter WUSER_WIDTH = `UVMA_OBI_MEMORY_WUSER_DEFAULT_WIDTH, ///< Width of the wuser signal. RI5CY, Ibex, CV32E40* do not have the wuser signal.
   parameter RUSER_WIDTH = `UVMA_OBI_MEMORY_RUSER_DEFAULT_WIDTH, ///< Width of the ruser signal. RI5CY, Ibex, CV32E40* do not have the ruser signal.
   parameter ADDR_WIDTH  = `UVMA_OBI_MEMORY_ADDR_DEFAULT_WIDTH , ///< Width of the addr signal.
   parameter DATA_WIDTH  = `UVMA_OBI_MEMORY_DATA_DEFAULT_WIDTH , ///< Width of the rdata and wdata signals. be width is DATA_WIDTH / 8. Valid DATA_WIDTH settings are 32 and 64.
   parameter ID_WIDTH    = `UVMA_OBI_MEMORY_ID_DEFAULT_WIDTH   , ///< Width of the aid and rid signals.
   parameter ACHK_WIDTH  = `UVMA_OBI_MEMORY_ACHK_DEFAULT_WIDTH , ///< Width of the achk signal.
   parameter RCHK_WIDTH  = `UVMA_OBI_MEMORY_RCHK_DEFAULT_WIDTH   ///< Width of the rchk signal.
) extends uvma_obi_memory_slv_base_seq_c#(
   .AUSER_WIDTH(AUSER_WIDTH),
   .WUSER_WIDTH(WUSER_WIDTH),
   .RUSER_WIDTH(RUSER_WIDTH),
   .ADDR_WIDTH(ADDR_WIDTH),
   .DATA_WIDTH(DATA_WIDTH),
   .ID_WIDTH(ID_WIDTH),
   .ACHK_WIDTH(ACHK_WIDTH),
   .RCHK_WIDTH(RCHK_WIDTH)
);

   uvma_obi_memory_mon_trn_c       mon_trn_q[$]; // Used to add transactions to execute (monitored requests)

   // Base address of this virtual peripheral, used to generated offset index for multi-register
   // virtual perhipeerals
   // Should be filled in during registration
   bit [31:0] start_address;

   `uvm_field_utils_begin(uvma_obi_memory_vp_base_seq_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   ))
   `uvm_field_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_vp_base_seq_c");

   /**
    * Simple loop that is triggered externally when the main slave sequence detects an address range
    * claimed by this virtual peripheral
    */
   extern virtual task body();

   /**
    * Utility to get an index for virtual peripheral with multiple registers
    */
   extern virtual function int unsigned get_vp_index(uvma_obi_memory_mon_trn_c mon_trn);

   /**
    * Derived classes must implement the operation of the virtual peripheral
    */
   pure virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);

   /**
    * Derived classes must implement accessor to return number of virtual peripheral registers
    */
   pure virtual function int unsigned get_num_words();

endclass : uvma_obi_memory_vp_base_seq_c


function uvma_obi_memory_vp_base_seq_c::new(string name="uvma_obi_memory_vp_base_seq_c");

   super.new(name);

endfunction : new


task uvma_obi_memory_vp_base_seq_c::body();

   forever begin
      wait (mon_trn_q.size());

      vp_body(mon_trn_q.pop_front());
   end

endtask : body


function int unsigned uvma_obi_memory_vp_base_seq_c::get_vp_index(uvma_obi_memory_mon_trn_c mon_trn);

   int unsigned index;

   // Fatal error if the address in the incoming transaction is less than the configured base address
   if (mon_trn.address < start_address) begin
      `uvm_fatal("FATAL", $sformatf("%s: get_vp_index(), mon_trn.address 0x%08x is less than start address 0x%08x",
                                    this.get_name(),
                                    mon_trn.address,
                                    start_address));
   end

   index = (mon_trn.address - start_address) >> 2;

   // Fatal if the index is greater than expected
   if (index >= get_num_words()) begin
      `uvm_fatal("FATAL", $sformatf("%s: get_vp_index(), mon_trn.address 0x%08x base address 0x%08x, should only have %0s vp registers",
                                    this.get_name(),
                                    mon_trn.address,
                                    start_address,
                                    get_num_words()));
   end

   return index;

endfunction : get_vp_index


`endif // __UVMA_OBI_MEMORY_VP_BASE_SEQ_SV__
