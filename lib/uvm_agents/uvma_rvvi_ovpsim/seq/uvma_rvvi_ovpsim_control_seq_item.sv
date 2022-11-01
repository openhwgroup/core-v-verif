// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVMA_RVVI_OVPSIM_CONTROL_SEQ_ITEM_SV__
`define __UVMA_RVVI_OVPSIM_CONTROL_SEQ_ITEM_SV__


/**
 * Object created by RVVI_control agent sequences extending uvma_rvvi_control_seq_base_c.
 */
class uvma_rvvi_ovpsim_control_seq_item_c#(int ILEN=uvma_rvvi_pkg::DEFAULT_ILEN,
                                           int XLEN=uvma_rvvi_pkg::DEFAULT_XLEN)  extends uvma_rvvi_control_seq_item_c#(ILEN,XLEN);


   // Set to signal this instructions is first instruction of external interrupt handler
   rand bit intr;

   // Hint from RVFI of the "winning" interrupt to determine proper interrupt vector entry
   rand int unsigned intr_id;

   // Set to signa external debug request
   rand bit dbg_req;

   // Set to signal in debug mode
   rand bit dbg_mode;

   // Set to signal nmi
   rand bit nmi;

   // Set to signal nmi cause
   rand bit [XLEN-1:0] nmi_cause;

   // Set to signal nmi load parity fault
   rand bit nmi_load_parity_fault;

   // Set to signal nmi store parity fault
   rand bit nmi_store_parity_fault;

   // Set to signal instruction bus error
   rand bit insn_bus_fault;

   // For accuracy of mip model the irq_i inputs for each instrucion
   rand bit[ILEN-1:0] mip;


   // Backdoor hint of register write for testing volatile CSR registers and ensuring RM tracks register value
   rand bit [GPR_ADDR_WL-1:0]    rd1_addr;
   rand bit [XLEN-1:0]           rd1_wdata;

   // Backdoor hint of register writes in the case of
   // an interrupted multi-operation instruction
   rand bit [(32*XLEN)-1:0]      gpr_rdata;
   rand bit [(32)-1:0]           gpr_rmask;
   rand bit [(32*XLEN)-1:0]      gpr_wdata;
   rand bit [(32)-1:0]           gpr_wmask;

   // Backdoor hint of memory transaction for ensuring memory model is updated with volatile read data
   rand bit [(NMEM*XLEN)-1:0]    mem_addr;
   rand bit [(NMEM*XLEN)-1:0]    mem_rdata;
   rand bit [(NMEM*XLEN/8)-1:0]  mem_rmask;
   rand bit [(NMEM*XLEN)-1:0]    mem_wdata;
   rand bit [(NMEM*XLEN/8)-1:0]  mem_wmask;

   static protected string _log_format_string = "0x%08x %s 0x%01x 0x%08x";

   `uvm_object_param_utils_begin(uvma_rvvi_ovpsim_control_seq_item_c#(ILEN,XLEN))
      `uvm_field_int(intr,            UVM_DEFAULT)
      `uvm_field_int(dbg_req,         UVM_DEFAULT)
      `uvm_field_int(dbg_mode,        UVM_DEFAULT)
      `uvm_field_int(nmi,             UVM_DEFAULT)
      `uvm_field_int(nmi_cause,       UVM_DEFAULT)
      `uvm_field_int(insn_bus_fault,  UVM_DEFAULT)
      `uvm_field_int(mip,             UVM_DEFAULT)
      `uvm_field_int(intr_id,         UVM_DEFAULT)
      `uvm_field_int(rd1_addr,        UVM_DEFAULT)
      `uvm_field_int(rd1_wdata,       UVM_DEFAULT)
      `uvm_field_int(gpr_rmask,       UVM_DEFAULT)
      `uvm_field_int(gpr_rdata,       UVM_DEFAULT)
      `uvm_field_int(gpr_wmask,       UVM_DEFAULT)
      `uvm_field_int(gpr_wdata,       UVM_DEFAULT)
      `uvm_field_int(mem_addr,        UVM_DEFAULT)
      `uvm_field_int(mem_rdata,       UVM_DEFAULT)
      `uvm_field_int(mem_rmask,       UVM_DEFAULT)
      `uvm_field_int(mem_wdata,       UVM_DEFAULT)
      `uvm_field_int(mem_wmask,       UVM_DEFAULT)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_ovpsim_control_seq_item");

   /**
    * One-liner log message
    */
   extern function string convert2string();

   /*
    * Return GPR wdata
    */
   extern function bit [XLEN-1:0] get_gpr_wdata(int gpr);

   /*
    * Return GPR rdata
    */
   extern function bit [XLEN-1:0] get_gpr_rdata(int gpr);


   /*
    * Return memory transaction data
    */
   extern function bit [XLEN-1:0] get_mem_data_word(int txn);

   /*
    * Return memory transaction addr
    */
   extern function bit [XLEN-1:0] get_mem_addr(int txn);

   /*
    * Return memory transaction wmask
    */
   extern function bit [(XLEN/8)-1:0] get_mem_wmask(int txn);

   /*
    * Return memory transaction rmask
    */
   extern function bit [(XLEN/8)-1:0] get_mem_rmask(int txn);

   /*
    * Check memory transaction activity
    *
    * Checks if a position in the rvfi memory transaction list
    * indicates any activity.
    * return {read, write}
    */
   extern function bit [1:0] check_mem_act(int txn);

endclass : uvma_rvvi_ovpsim_control_seq_item_c

`pragma protect begin


function uvma_rvvi_ovpsim_control_seq_item_c::new(string name="uvma_rvvi_ovpsim_control_seq_item");

   super.new(name);

endfunction : new

function string uvma_rvvi_ovpsim_control_seq_item_c::convert2string();

   return action.name();

endfunction : convert2string


function bit [XLEN-1:0] uvma_rvvi_ovpsim_control_seq_item_c::get_gpr_wdata(int gpr);
  return gpr_wdata[gpr*XLEN +:XLEN];
endfunction : get_gpr_wdata

function bit [XLEN-1:0] uvma_rvvi_ovpsim_control_seq_item_c::get_gpr_rdata(int gpr);
  return gpr_rdata[gpr*XLEN +:XLEN];
endfunction : get_gpr_rdata

function bit [XLEN-1:0] uvma_rvvi_ovpsim_control_seq_item_c::get_mem_data_word(int txn);
  bit [XLEN-1:0] ret;

  for (int i = 0; i < XLEN/8; i++) begin
    if (mem_wmask[(txn*XLEN/8) + i]) begin
      ret[i*8 +:8] = mem_wdata[((txn*XLEN) + (i*8)) +:8];
    end else begin
      ret[i*8 +:8] = mem_rdata[((txn*XLEN) + (i*8)) +:8];
    end
  end

  return ret;

endfunction : get_mem_data_word

function bit [XLEN-1:0] uvma_rvvi_ovpsim_control_seq_item_c::get_mem_addr(int txn);

  return mem_addr[txn*XLEN +:XLEN];

endfunction : get_mem_addr

function bit [(XLEN/8)-1:0] uvma_rvvi_ovpsim_control_seq_item_c::get_mem_rmask(int txn);

   return mem_rmask[(txn*XLEN/8) +:(XLEN/8)];

endfunction : get_mem_rmask

function bit [(XLEN/8)-1:0] uvma_rvvi_ovpsim_control_seq_item_c::get_mem_wmask(int txn);

   return mem_wmask[(txn*XLEN/8) +:(XLEN/8)];

endfunction : get_mem_wmask

function bit [1:0] uvma_rvvi_ovpsim_control_seq_item_c::check_mem_act(int txn);
   static bit read = 0;
   static bit write = 0;

   if (mem_rmask[(txn*XLEN/8) +:(XLEN/8)]) begin
      read = 1;
   end
   if (mem_wmask[(txn*XLEN/8) +:(XLEN/8)]) begin
      write = 1;
   end

   return {read,write};

endfunction : check_mem_act


`pragma protect end


`endif // __UVMA_RVVI_OVPSIM_CONTROL_SEQ_ITEM_SV__


