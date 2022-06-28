// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 slave local memory: this uvm component is used as a local memory in the top agent to model AXI slave behaviour and to
      store & retieve data whenever a read  &/or write  is requested by a AXI Master.
  ****/


`ifndef __UVMA_AXI_MEM_SV__
`define __UVMA_AXI_MEM_SV__

class uvma_axi_mem_c extends uvm_component;

   `uvm_component_utils(uvma_axi_mem_c)

   extern function new(string name="uvma_axi_mem_c", uvm_component parent);
   extern virtual function void build_phase(uvm_phase phase);
   extern function void connect_phase(uvm_phase phase);
   extern virtual task run_phase(uvm_phase phase);
   //function for memory initial values
   extern function void axi_mem_init();
   //write to memory
   extern task mem_write();
   //read from memory
   extern task mem_read();

endclass: uvma_axi_mem_c

function uvma_axi_mem_c::new(string name = "uvma_axi_mem_c", uvm_component parent);
   super.new(name, parent);
endfunction

function void uvma_axi_mem_c::build_phase(uvm_phase phase);
   super.build_phase(phase);
endfunction

function void uvma_axi_mem_c::connect_phase(uvm_phase phase);

endfunction

task uvma_axi_mem_c::run_phase(uvm_phase phase);
   super.run_phase(phase);
   this.axi_mem_init();

   fork
      this.mem_write();
      this.mem_read();
   join

endtask: run_phase


function void uvma_axi_mem_c::axi_mem_init();

   //TODO: Randomize all bytes of the memory

endfunction

task uvma_axi_mem_c::mem_write();

   //TODO

endtask : mem_write

task uvma_axi_mem_c::mem_read();

   //TODO

endtask : mem_read

`endif
