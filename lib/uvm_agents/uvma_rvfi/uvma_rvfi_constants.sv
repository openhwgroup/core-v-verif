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


`ifndef __UVMA_RVFI_CONSTANTS_SV__
`define __UVMA_RVFI_CONSTANTS_SV__


// RVFI field widths
localparam ORDER_WL         = 64;
localparam MODE_WL          = 2;
localparam IXL_WL           = 2;
localparam TRAP_WL          = 14;
localparam GPR_ADDR_WL      = 5;
localparam RVFI_DBG_WL      = 3;
localparam RVFI_NMIP_WL     = 2;
localparam CYCLE_CNT_WL     = 32;
localparam NMEM             = 128;

// Fields within TRAP
localparam TRAP_EXCP_LSB         = 0;
localparam TRAP_EXCP_WL          = 1;
localparam TRAP_NONDBG_ENTRY_LSB = 1;
localparam TRAP_NONDBG_ENTRY_WL  = 1;
localparam TRAP_DBG_ENTRY_LSB    = 2;
localparam TRAP_DBG_ENTRY_WL     = 1;
localparam TRAP_CAUSE_LSB        = 3;
localparam TRAP_CAUSE_WL         = 6;
localparam TRAP_DBG_CAUSE_LSB    = 9;
localparam TRAP_DBG_CAUSE_WL     = 3;

// Lengths & Sizes
localparam DEFAULT_ILEN     = 32;
localparam DEFAULT_XLEN     = 32;
localparam MAX_XLEN         = 64;
localparam DEFAULT_NRET     = 1;

// RISC-V Constants
parameter logic[ 2:0]  DBG_CAUSE_TRIGGER               =  3'h 2;
parameter logic[ 1:0]  PRIV_LVL_M                      =  2'b 11;
parameter logic[ 1:0]  PRIV_LVL_U                      =  2'b 00;
parameter logic[10:0]  EXC_CAUSE_INSTR_ACC_FAULT       = 11'd 1;
parameter logic[10:0]  EXC_CAUSE_ILLEGAL_INSTR         = 11'd 2;
parameter logic[10:0]  EXC_CAUSE_BREAKPOINT            = 11'd 3;
parameter logic[10:0]  EXC_CAUSE_LOAD_ACC_FAULT        = 11'd 5;
parameter logic[10:0]  EXC_CAUSE_STORE_ACC_FAULT       = 11'd 7;
parameter logic[10:0]  EXC_CAUSE_ENV_CALL_U            = 11'd 8;
parameter logic[10:0]  EXC_CAUSE_ENV_CALL_M            = 11'd 11;
parameter logic[10:0]  EXC_CAUSE_INSTR_BUS_FAULT       = 11'd 24;
parameter logic[10:0]  EXC_CAUSE_INSTR_INTEGRITY_FAULT = 11'd 25;

localparam CSR_QUEUE_SIZE = 250;

const string format_header_str = "%8s | RVFI | %8s | %6s | %8s | %8s | %s | %03s | %08s | %03s | %08s | %03s | %08s | %03s | %08s | %08s | %s";
const string format_instr_str  = "%8s | RVFI | %8d | %6d | %8x | %8s | %s | x%-2d | %8x | x%-2d | %8x | x%-2d | %16x";
`define FORMAT_INSTR_STR_MACRO "%8s | RVFI | %8d | %6d | %8x | %8s | %s | x%-2d | %8x | x%-2d | %8x | x%-2d | %16x | %s"
const string format_mem_str    = "| %02s | %08x | %08s |";

`endif // __UVMA_RVFI_CONSTANTS_SV__
