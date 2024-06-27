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


`ifndef __UVMA_RVFI_INSTR_SEQ_ITEM_SV__
`define __UVMA_RVFI_INSTR_SEQ_ITEM_SV__


/**
 * Object created by Rvfi agent sequences extending uvma_rvfi_seq_base_c.
 */
class uvma_rvfi_instr_seq_item_c#(int ILEN=DEFAULT_ILEN,
                                  int XLEN=DEFAULT_XLEN) extends uvml_trn_seq_item_c;

   rand int unsigned             nret_id;
   rand bit [CYCLE_CNT_WL-1:0]   cycle_cnt;
   rand bit [ORDER_WL-1:0]       order;
   rand bit [ILEN-1:0]           insn;
   rand bit [TRAP_WL-1:0]        trap;
   rand bit                      halt;
   rand bit [RVFI_INTR_WL-1:0]   intr;
   rand uvma_rvfi_mode           mode;
   rand bit [IXL_WL-1:0]         ixl;
   rand bit [RVFI_DBG_WL-1:0]    dbg;
   rand bit                      dbg_mode;
   rand bit [RVFI_NMIP_WL-1:0]   nmip;

   rand bit                      insn_interrupt;
   rand int unsigned             insn_interrupt_id;
   rand bit                      insn_bus_fault;
   rand bit                      insn_nmi_store_fault;
   rand bit                      insn_nmi_load_fault;

   rand bit [XLEN-1:0]           pc_rdata;
   rand bit [XLEN-1:0]           pc_wdata;

   rand bit [GPR_ADDR_WL-1:0]    rs1_addr;
   rand bit [XLEN-1:0]           rs1_rdata;

   rand bit [GPR_ADDR_WL-1:0]    rs2_addr;
   rand bit [XLEN-1:0]           rs2_rdata;

   rand bit [GPR_ADDR_WL-1:0]    rs3_addr;
   rand bit [XLEN-1:0]           rs3_rdata;

   rand bit [GPR_ADDR_WL-1:0]    rd1_addr;
   rand bit [XLEN-1:0]           rd1_wdata;

   rand bit [GPR_ADDR_WL-1:0]    rd2_addr;
   rand bit [XLEN-1:0]           rd2_wdata;

   rand bit [XLEN-1:0]           mem_addr;
   rand bit [XLEN-1:0]           mem_rdata;
   rand bit [XLEN-1:0]           mem_rmask;
   rand bit [XLEN-1:0]           mem_wdata;
   rand bit [XLEN-1:0]           mem_wmask;

   uvma_rvfi_csr_seq_item_c      name_csrs[string];
   uvma_rvfi_csr_seq_item_c      addr_csrs[longint unsigned];

   static protected string _log_format_string = "0x%08x %s 0x%01x 0x%08x";

   `uvm_object_param_utils_begin(uvma_rvfi_instr_seq_item_c)
      `uvm_field_int(cycle_cnt, UVM_DEFAULT)
      `uvm_field_int(order, UVM_DEFAULT)
      `uvm_field_int(insn, UVM_DEFAULT)
      `uvm_field_int(trap, UVM_DEFAULT)
      `uvm_field_int(halt, UVM_DEFAULT)
      `uvm_field_int(dbg, UVM_DEFAULT)
      `uvm_field_int(dbg_mode, UVM_DEFAULT)
      `uvm_field_int(nmip, UVM_DEFAULT)
      `uvm_field_int(intr, UVM_DEFAULT)
      `uvm_field_int(insn_interrupt, UVM_DEFAULT)
      `uvm_field_int(insn_interrupt_id, UVM_DEFAULT)
      `uvm_field_int(insn_bus_fault, UVM_DEFAULT)
      `uvm_field_int(insn_nmi_load_fault, UVM_DEFAULT)
      `uvm_field_int(insn_nmi_store_fault, UVM_DEFAULT)
      `uvm_field_enum(uvma_rvfi_mode, mode, UVM_DEFAULT)
      `uvm_field_int(ixl, UVM_DEFAULT)
      `uvm_field_int(pc_rdata, UVM_DEFAULT)
      `uvm_field_int(pc_wdata, UVM_DEFAULT)
      `uvm_field_int(rs1_addr, UVM_DEFAULT)
      `uvm_field_int(rs1_rdata, UVM_DEFAULT)
      `uvm_field_int(rs2_addr, UVM_DEFAULT)
      `uvm_field_int(rs2_rdata, UVM_DEFAULT)
      `uvm_field_int(rs3_addr, UVM_DEFAULT)
      `uvm_field_int(rs3_rdata, UVM_DEFAULT)
      `uvm_field_int(rd1_addr, UVM_DEFAULT)
      `uvm_field_int(rd1_wdata, UVM_DEFAULT)
      `uvm_field_int(rd2_addr, UVM_DEFAULT)
      `uvm_field_int(rd2_wdata, UVM_DEFAULT)
      `uvm_field_int(mem_addr, UVM_DEFAULT)
      `uvm_field_int(mem_rmask, UVM_DEFAULT)
      `uvm_field_int(mem_rdata, UVM_DEFAULT)
      `uvm_field_int(mem_wmask, UVM_DEFAULT)
      `uvm_field_int(mem_wdata, UVM_DEFAULT)

      `uvm_field_aa_object_string(name_csrs, UVM_DEFAULT)
      `uvm_field_aa_object_int(addr_csrs, UVM_DEFAULT)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvfi_seq_item");

   /**
    * One-liner log message
    */
   extern function string convert2string();

   /**
    * Get instruction hex string with compressed instructions displayed
    */
   extern function string get_insn_word_str();

   /**
    * Get string representing memory data
    */
   extern function string get_mem_data_string();

   /**
    * Decode compressed instruction
    */
   extern function bit is_compressed_insn();

   /**
    * Decode if instruction is a trap
    */
   extern function bit is_trap();

   /*
    * Decode if instruction is a synchronous trap with debug entry
    */
   extern function bit is_debug_entry_trap();

   /*
    * Decode if instruction is a synchronous trap without debug entry
    */
   extern function bit is_nondebug_entry_trap();

   /*
    * Retrieve trap cause field
    */
   extern function bit [TRAP_CAUSE_WL-1:0] get_trap_cause();

   /*
    * Retrieve trap debug cause
    */
   extern function bit [TRAP_DBG_CAUSE_WL-1:0] get_trap_debug_cause();


   extern function st_rvfi seq2rvfi();

   extern function void rvfi2seq(st_rvfi rvfi);

endclass : uvma_rvfi_instr_seq_item_c

`pragma protect begin

function uvma_rvfi_instr_seq_item_c::new(string name="uvma_rvfi_seq_item");

   super.new(name);

endfunction : new

function string uvma_rvfi_instr_seq_item_c::convert2string();

   convert2string = $sformatf("Order: %0d, insn: 0x%08x, pc: 0x%08x, nret_id: %0d, mode: %s, ixl: 0x%01x",
                              order, insn, pc_rdata, this.nret_id, mode.name(), ixl);
   if (rs1_addr)
      convert2string = $sformatf("%s rs1: x%0d = 0x%08x", convert2string, rs1_addr, rs1_rdata);
   if (rs2_addr)
      convert2string = $sformatf("%s rs2: x%0d = 0x%08x", convert2string, rs2_addr, rs2_rdata);
   if (rs3_addr)
      convert2string = $sformatf("%s rs3: x%0d = 0x%08x", convert2string, rs3_addr, rs3_rdata);
   if (rd1_addr)
      convert2string = $sformatf("%s rd: x%0d = 0x%08x", convert2string, rd1_addr, rd1_wdata);
   if (rd2_addr)
      convert2string = $sformatf("%s rd2: x%0d = 0x%08x", convert2string, rd2_addr, rd2_wdata);
   if (trap)
      convert2string = $sformatf("%s TRAP %0d", convert2string, trap);
   if (halt)
      convert2string = $sformatf("%s HALT", convert2string);
   if (insn_interrupt)
      convert2string = $sformatf("%s INTR %0d", convert2string, this.insn_interrupt_id);
   if (insn_nmi_load_fault)
      convert2string = $sformatf("%s NMI LOAD", convert2string);
   if (insn_nmi_store_fault)
      convert2string = $sformatf("%s NMI STORE", convert2string);
   if (insn_bus_fault)
      convert2string = $sformatf("%s INSN_BUS_FAULT", convert2string);
   if (dbg)
      convert2string = $sformatf("%s DEBUG", convert2string);

endfunction : convert2string

function string uvma_rvfi_instr_seq_item_c::get_insn_word_str();

   if (is_compressed_insn)
      return $sformatf("----%04x", insn[15:0]);

   return $sformatf("%08x", insn);

endfunction : get_insn_word_str

function string uvma_rvfi_instr_seq_item_c::get_mem_data_string();
   string mem_data_str;

   if (mem_wmask) begin
      for (int i = 0; i < XLEN/8; i++) begin
         if (mem_wmask[i])
            mem_data_str = $sformatf("%02x%s", mem_wdata[i*8+:8], mem_data_str);
         else
            mem_data_str = $sformatf("--%s", mem_data_str);
      end
   end
   else if (mem_rmask) begin
      for (int i = 0; i < XLEN/8; i++) begin
         if (mem_rmask[i])
            mem_data_str = $sformatf("%02x%s", mem_rdata[i*8+:8], mem_data_str);
         else
            mem_data_str = $sformatf("--%s", mem_data_str);
      end
   end

   return mem_data_str;

endfunction : get_mem_data_string

function bit uvma_rvfi_instr_seq_item_c::is_compressed_insn();

   if (insn[31:16] == 0 && insn[1:0] inside {0,1,2})
      return 1;

   return 0;

endfunction : is_compressed_insn

function bit uvma_rvfi_instr_seq_item_c::is_trap();

   return trap[TRAP_EXCP_LSB];

endfunction : is_trap

function bit uvma_rvfi_instr_seq_item_c::is_debug_entry_trap();

   return trap[TRAP_DBG_ENTRY_LSB];

endfunction : is_debug_entry_trap

function bit uvma_rvfi_instr_seq_item_c::is_nondebug_entry_trap();

   return trap[TRAP_NONDBG_ENTRY_LSB];

endfunction : is_nondebug_entry_trap

function bit [TRAP_CAUSE_WL-1:0] uvma_rvfi_instr_seq_item_c::get_trap_cause();

   return trap[TRAP_CAUSE_LSB +: TRAP_CAUSE_WL];

endfunction : get_trap_cause

function bit [TRAP_DBG_CAUSE_WL-1:0] uvma_rvfi_instr_seq_item_c::get_trap_debug_cause();

   return trap[TRAP_DBG_CAUSE_LSB +: TRAP_DBG_CAUSE_WL];

endfunction : get_trap_debug_cause

function st_rvfi uvma_rvfi_instr_seq_item_c::seq2rvfi();

    st_rvfi rvfi;
    longint unsigned csr_index = 0;

    rvfi.nret_id = nret_id;
    rvfi.cycle_cnt = cycle_cnt;
    rvfi.order = order;
    rvfi.insn = insn;
    rvfi.trap = trap;
    rvfi.halt = halt;
    rvfi.intr = intr;
    rvfi.mode = mode;
    rvfi.ixl = ixl;
    rvfi.dbg = dbg;
    rvfi.dbg_mode = dbg_mode;
    rvfi.nmip = nmip;

    rvfi.insn_interrupt = insn_interrupt;
    rvfi.insn_interrupt_id = insn_interrupt_id;
    rvfi.insn_bus_fault = insn_bus_fault;
    rvfi.insn_nmi_store_fault = insn_nmi_store_fault;
    rvfi.insn_nmi_load_fault = insn_nmi_load_fault;

    rvfi.pc_rdata = pc_rdata;
    rvfi.pc_wdata = pc_wdata;

    rvfi.rs1_addr = rs1_addr;
    rvfi.rs1_rdata = rs1_rdata;

    rvfi.rs2_addr = rs2_addr;
    rvfi.rs2_rdata = rs2_rdata;

    rvfi.rs3_addr = rs3_addr;
    rvfi.rs3_rdata = rs3_rdata;

    rvfi.rd1_addr = rd1_addr;
    rvfi.rd1_wdata = rd1_wdata;

    rvfi.rd2_addr = rd2_addr;
    rvfi.rd2_wdata = rd2_wdata;

    rvfi.mem_addr = mem_addr;
    rvfi.mem_rdata = mem_rdata;
    rvfi.mem_rmask = mem_rmask;
    rvfi.mem_wdata = mem_wdata;
    rvfi.mem_wmask = mem_wmask;

    foreach(addr_csrs[i]) begin
        longint unsigned addr = addr_csrs[i].addr;

        rvfi.csr_valid[addr] = 1;
        rvfi.csr_addr [addr] = addr_csrs[i].addr;
        rvfi.csr_rdata[addr] = addr_csrs[i].rdata;
        rvfi.csr_rmask[addr] = addr_csrs[i].rmask;
        rvfi.csr_wdata[addr] = addr_csrs[i].wdata;
        rvfi.csr_wmask[addr] = addr_csrs[i].wmask;
    end
    foreach(name_csrs[i]) begin
        longint unsigned addr = csr_name2addr[i];

        rvfi.csr_valid[addr] = 1;
        rvfi.csr_addr [addr] = csr_name2addr[i];
        rvfi.csr_rdata[addr] = name_csrs[i].rdata;
        rvfi.csr_rmask[addr] = name_csrs[i].rmask;
        rvfi.csr_wdata[addr] = name_csrs[i].wdata;
        rvfi.csr_wmask[addr] = name_csrs[i].wmask;
    end
    return rvfi;

endfunction : seq2rvfi

function void uvma_rvfi_instr_seq_item_c::rvfi2seq(st_rvfi rvfi);

    nret_id = rvfi.nret_id;
    cycle_cnt = rvfi.cycle_cnt;
    order = rvfi.order;
    insn = rvfi.insn;
    trap = rvfi.trap;
    halt = rvfi.halt;
    intr = rvfi.intr;
    mode = rvfi.mode;
    ixl = rvfi.ixl;
    dbg = rvfi.dbg;
    dbg_mode = rvfi.dbg_mode;
    nmip = rvfi.nmip;

    insn_interrupt = rvfi.insn_interrupt;
    insn_interrupt_id = rvfi.insn_interrupt_id;
    insn_bus_fault = rvfi.insn_bus_fault;
    insn_nmi_store_fault = rvfi.insn_nmi_store_fault;
    insn_nmi_load_fault = rvfi.insn_nmi_load_fault;

    pc_rdata = rvfi.pc_rdata;
    pc_wdata = rvfi.pc_wdata;

    rs1_addr = rvfi.rs1_addr;
    rs1_rdata = rvfi.rs1_rdata;

    rs2_addr = rvfi.rs2_addr;
    rs2_rdata = rvfi.rs2_rdata;

    rs3_addr = rvfi.rs3_addr;
    rs3_rdata = rvfi.rs3_rdata;

    rd1_addr = rvfi.rd1_addr;
    rd1_wdata = rvfi.rd1_wdata;

    rd2_addr = rvfi.rd2_addr;
    rd2_wdata = rvfi.rd2_wdata;

    mem_addr = rvfi.mem_addr;
    mem_rdata = rvfi.mem_rdata;
    mem_rmask = rvfi.mem_rmask;
    mem_wdata = rvfi.mem_wdata;
    mem_wmask = rvfi.mem_wmask;

    for (int i = 0; i < CSR_MAX_SIZE; i++) begin
        if (rvfi.csr_valid[i]) begin
            uvma_rvfi_csr_seq_item_c csr_trn = uvma_rvfi_csr_seq_item_c#(XLEN)::type_id::create({rvfi.csr_addr[i], "_trn"});
            csr_trn.addr  = rvfi.csr_addr[i];
            csr_trn.rdata = rvfi.csr_rdata[i];
            csr_trn.rmask = rvfi.csr_rmask[i];
            csr_trn.wdata = rvfi.csr_wdata[i];
            csr_trn.wmask = rvfi.csr_wmask[i];
            addr_csrs[rvfi.csr_addr[i]] = csr_trn;
        end
    end
endfunction : rvfi2seq

`pragma protect end

`endif // __UVMA_RVFI_SEQ_ITEM_SV__

