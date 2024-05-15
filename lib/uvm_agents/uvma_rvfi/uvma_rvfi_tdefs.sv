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

typedef struct packed {
   longint unsigned         nret_id;
   longint unsigned         cycle_cnt;
   longint unsigned         order;
   longint unsigned         insn;
   longint unsigned         trap;
   longint unsigned         cause;
   longint unsigned         halt;
   longint unsigned         intr;
   longint unsigned         mode;
   longint unsigned         ixl;
   longint unsigned         dbg;
   longint unsigned         dbg_mode;
   longint unsigned         nmip;

   longint unsigned         insn_interrupt;
   longint unsigned         insn_interrupt_id;
   longint unsigned         insn_bus_fault;
   longint unsigned         insn_nmi_store_fault;
   longint unsigned         insn_nmi_load_fault;

   longint unsigned         pc_rdata;
   longint unsigned         pc_wdata;

   longint unsigned         rs1_addr;
   longint unsigned         rs1_rdata;

   longint unsigned         rs2_addr;
   longint unsigned         rs2_rdata;

   longint unsigned         rs3_addr;
   longint unsigned         rs3_rdata;

   longint unsigned         rd1_addr;
   longint unsigned         rd1_wdata;

   longint unsigned         rd2_addr;
   longint unsigned         rd2_wdata;

   longint unsigned         mem_addr;
   longint unsigned         mem_rdata;
   longint unsigned         mem_rmask;
   longint unsigned         mem_wdata;
   longint unsigned         mem_wmask;

} st_rvfi;

`define ST_NUM_WORDS (($size(st_rvfi)/$size(longint unsigned)))

typedef union {
    st_rvfi rvfi;
    bit [63:0] array [`ST_NUM_WORDS-1:0] ;
} union_rvfi;

typedef enum bit[MODE_WL-1:0] {
   UVMA_RVFI_U_MODE        = 0,
   UVMA_RVFI_S_MODE        = 1,
   UVMA_RVFI_RESERVED_MODE = 2,
   UVMA_RVFI_M_MODE        = 3
} uvma_rvfi_mode;

typedef struct packed {
  logic [10:0] cause;
  logic        interrupt;
  logic        exception;
  logic        intr;
} rvfi_intr_t;

typedef struct packed {
  logic        clicptr;
  logic [1:0]  cause_type;
  logic [2:0]  debug_cause;
  logic [5:0]  exception_cause;
  logic        debug;
  logic        exception;
  logic        trap;
} rvfi_trap_t;

function string get_mode_str(uvma_rvfi_mode mode);
   case (mode)
      UVMA_RVFI_U_MODE: return "U";
      UVMA_RVFI_M_MODE: return "M";
      UVMA_RVFI_S_MODE: return "S";
   endcase

   return "?";

endfunction : get_mode_str

`endif // __UVMA_RVFI_TDEFS_SV__
