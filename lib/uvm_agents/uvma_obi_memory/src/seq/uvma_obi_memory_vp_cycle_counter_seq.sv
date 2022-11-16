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

`ifndef __UVMA_OBI_MEMORY_VP_CYCLE_COUNTER_SEQ_SV__
`define __UVMA_OBI_MEMORY_VP_CYCLE_COUNTER_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
class uvma_obi_memory_vp_cycle_counter_seq_c#(
   parameter AUSER_WIDTH = `UVMA_OBI_MEMORY_AUSER_DEFAULT_WIDTH, ///< Width of the auser signal. RI5CY, Ibex, CV32E40* do not have the auser signal.
   parameter WUSER_WIDTH = `UVMA_OBI_MEMORY_WUSER_DEFAULT_WIDTH, ///< Width of the wuser signal. RI5CY, Ibex, CV32E40* do not have the wuser signal.
   parameter RUSER_WIDTH = `UVMA_OBI_MEMORY_RUSER_DEFAULT_WIDTH, ///< Width of the ruser signal. RI5CY, Ibex, CV32E40* do not have the ruser signal.
   parameter ADDR_WIDTH  = `UVMA_OBI_MEMORY_ADDR_DEFAULT_WIDTH , ///< Width of the addr signal.
   parameter DATA_WIDTH  = `UVMA_OBI_MEMORY_DATA_DEFAULT_WIDTH , ///< Width of the rdata and wdata signals. be width is DATA_WIDTH / 8. Valid DATA_WIDTH settings are 32 and 64.
   parameter ID_WIDTH    = `UVMA_OBI_MEMORY_ID_DEFAULT_WIDTH   , ///< Width of the aid and rid signals.
   parameter ACHK_WIDTH  = `UVMA_OBI_MEMORY_ACHK_DEFAULT_WIDTH , ///< Width of the achk signal.
   parameter RCHK_WIDTH  = `UVMA_OBI_MEMORY_RCHK_DEFAULT_WIDTH   ///< Width of the rchk signal.
) extends uvma_obi_memory_vp_base_seq_c#(
   .AUSER_WIDTH(AUSER_WIDTH),
   .WUSER_WIDTH(WUSER_WIDTH),
   .RUSER_WIDTH(RUSER_WIDTH),
   .ADDR_WIDTH(ADDR_WIDTH),
   .DATA_WIDTH(DATA_WIDTH),
   .ID_WIDTH(ID_WIDTH),
   .ACHK_WIDTH(ACHK_WIDTH),
   .RCHK_WIDTH(RCHK_WIDTH)
);

   longint unsigned cycle_counter;

   protected bit _stop_count_cycles;

   `uvm_object_utils_begin(uvma_obi_memory_vp_cycle_counter_seq_c#(
     .AUSER_WIDTH(AUSER_WIDTH),
     .WUSER_WIDTH(WUSER_WIDTH),
     .RUSER_WIDTH(RUSER_WIDTH),
     .ADDR_WIDTH(ADDR_WIDTH),
     .DATA_WIDTH(DATA_WIDTH),
     .ID_WIDTH(ID_WIDTH),
     .ACHK_WIDTH(ACHK_WIDTH),
     .RCHK_WIDTH(RCHK_WIDTH)
   ))
      `uvm_field_int(cycle_counter, UVM_DEFAULT)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_vp_cycle_counter_seq_c");

   /**
    * Body will start cycle counting thread before starting parent
    */
   extern virtual task body();

   /**
    * Implement sequence that will return a random number
    */
   extern virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);

   /**
    * Implement accessor to return number of register
    */
   extern virtual function int unsigned get_num_words();

   /**
    * Implements the virtual register to read or write the counter
    */
   extern virtual task rw_counter(uvma_obi_memory_mon_trn_c mon_trn, uvma_obi_memory_slv_seq_item_c slv_rsp);

   /**
    * Implements the virtual register to read or write the counter
    */
   extern virtual task print_counter(uvma_obi_memory_mon_trn_c mon_trn);

   /**
    * Implements the counting thread, should always be fork-join_none'd
    */
   extern virtual task count_cycles();


endclass : uvma_obi_memory_vp_cycle_counter_seq_c

function uvma_obi_memory_vp_cycle_counter_seq_c::new(string name="uvma_obi_memory_vp_cycle_counter_seq_c");

   super.new(name);

endfunction : new


task uvma_obi_memory_vp_cycle_counter_seq_c::body();

   fork
      count_cycles();
   join_none

   super.body();

endtask : body

function int unsigned uvma_obi_memory_vp_cycle_counter_seq_c::get_num_words();

   return 2;

endfunction : get_num_words

task uvma_obi_memory_vp_cycle_counter_seq_c::vp_body(uvma_obi_memory_mon_trn_c mon_trn);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;

   `uvm_create(slv_rsp)

   slv_rsp.orig_trn = mon_trn;
   slv_rsp.err = 1'b0;

   case (get_vp_index(mon_trn))
      0: rw_counter(mon_trn, slv_rsp);
      1: print_counter(mon_trn);
   endcase

   add_r_fields(mon_trn, slv_rsp);
   slv_rsp.set_sequencer(p_sequencer);
   `uvm_send(slv_rsp)

endtask : vp_body

task uvma_obi_memory_vp_cycle_counter_seq_c::count_cycles();

   fork begin
      fork
         begin
            wait  (_stop_count_cycles == 1);
         end
         begin
            while(1) begin
               @(cntxt.vif.mon_cb);
               cycle_counter++;
            end
         end
      join_any

      // kill counting thread
      disable fork;

      // Handshake that the thread is stopped
      _stop_count_cycles = 0;
   end
   join

endtask : count_cycles

task uvma_obi_memory_vp_cycle_counter_seq_c::rw_counter(uvma_obi_memory_mon_trn_c mon_trn, uvma_obi_memory_slv_seq_item_c slv_rsp);

   if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      // First stop the thread, reset counter to write data, then restart

      _stop_count_cycles = 1;
      wait (_stop_count_cycles == 0);

      cycle_counter = mon_trn.data;
      fork
         count_cycles();
      join_none
   end
   else if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin
      slv_rsp.rdata = cycle_counter;
   end

endtask : rw_counter

task uvma_obi_memory_vp_cycle_counter_seq_c::print_counter(uvma_obi_memory_mon_trn_c mon_trn);

   if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      `uvm_info("CYCLE", $sformatf("Cycle count is %0d", cycle_counter), UVM_LOW);
   end

endtask : print_counter

`endif // __UVMA_OBI_MEMORY_VP_CYCLE_COUNTER_SEQ_SV__

