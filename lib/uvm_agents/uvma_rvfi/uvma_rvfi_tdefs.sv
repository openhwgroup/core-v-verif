// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVMA_RVFI_TDEFS_SV__
`define __UVMA_RVFI_TDEFS_SV__

typedef enum bit[MODE_WL-1:0] {
   UVMA_RVFI_U_MODE        = 0,
   UVMA_RVFI_S_MODE        = 1,
   UVMA_RVFI_RESERVED_MODE = 2,
   UVMA_RVFI_M_MODE        = 3
} uvma_rvfi_mode;

typedef struct packed {
   bit [MAX_XLEN-1:0]         nret_id;
   bit [MAX_XLEN-1:0]         cycle_cnt;
   bit [MAX_XLEN-1:0]         order;
   bit [MAX_XLEN-1:0]         insn;
   bit [MAX_XLEN-1:0]         trap;
   bit [MAX_XLEN-1:0]         halt;
   bit [MAX_XLEN-1:0]         intr;
   bit [MAX_XLEN-1:0]         mode;
   bit [MAX_XLEN-1:0]         ixl;
   bit [MAX_XLEN-1:0]         dbg;
   bit [MAX_XLEN-1:0]         dbg_mode;
   bit [MAX_XLEN-1:0]         nmip;

   bit [MAX_XLEN-1:0]         insn_interrupt;
   bit [MAX_XLEN-1:0]         insn_interrupt_id;
   bit [MAX_XLEN-1:0]         insn_bus_fault;
   bit [MAX_XLEN-1:0]         insn_nmi_store_fault;
   bit [MAX_XLEN-1:0]         insn_nmi_load_fault;

   bit [MAX_XLEN-1:0]         pc_rdata;
   bit [MAX_XLEN-1:0]         pc_wdata;

   bit [MAX_XLEN-1:0]         rs1_addr;
   bit [MAX_XLEN-1:0]         rs1_rdata;

   bit [MAX_XLEN-1:0]         rs2_addr;
   bit [MAX_XLEN-1:0]         rs2_rdata;

   bit [MAX_XLEN-1:0]         rs3_addr;
   bit [MAX_XLEN-1:0]         rs3_rdata;

   bit [MAX_XLEN-1:0]         rd1_addr;
   bit [MAX_XLEN-1:0]         rd1_wdata;

   bit [MAX_XLEN-1:0]         rd2_addr;
   bit [MAX_XLEN-1:0]         rd2_wdata;

   bit [MAX_XLEN-1:0]         mem_addr;
   bit [MAX_XLEN-1:0]         mem_rdata;
   bit [MAX_XLEN-1:0]         mem_rmask;
   bit [MAX_XLEN-1:0]         mem_wdata;
   bit [MAX_XLEN-1:0]         mem_wmask;

   bit [CSR_MAX_SIZE-1:0] [MAX_XLEN-1:0] csr_valid;
   bit [CSR_MAX_SIZE-1:0] [MAX_XLEN-1:0] csr_addr;
   bit [CSR_MAX_SIZE-1:0] [MAX_XLEN-1:0] csr_rdata;
   bit [CSR_MAX_SIZE-1:0] [MAX_XLEN-1:0] csr_rmask;
   bit [CSR_MAX_SIZE-1:0] [MAX_XLEN-1:0] csr_wdata;
   bit [CSR_MAX_SIZE-1:0] [MAX_XLEN-1:0] csr_wmask;

} st_rvfi;

`define ST_NUM_WORDS ($size(st_rvfi)/MAX_XLEN)
parameter ST_NUM_WORDS =  ($size(st_rvfi)/MAX_XLEN);

    typedef bit [ST_NUM_WORDS-1:0] [MAX_XLEN-1:0] vector_rvfi;
typedef union {
    st_rvfi rvfi;
    vector_rvfi array;
} union_rvfi;

function string get_mode_str(uvma_rvfi_mode mode);
   case (mode)
      UVMA_RVFI_U_MODE: return "U";
      UVMA_RVFI_M_MODE: return "M";
      UVMA_RVFI_S_MODE: return "S";
   endcase

   return "?";

endfunction : get_mode_str

function bit is_csr_insn (st_rvfi rvfi);
    return (rvfi.insn[6:0] == 'b1110011);
endfunction : is_csr_insn

function bit [11:0] get_insn_rs1 (st_rvfi rvfi);
    return rvfi.insn[31:20];
endfunction

`endif // __UVMA_RVFI_TDEFS_SV__
