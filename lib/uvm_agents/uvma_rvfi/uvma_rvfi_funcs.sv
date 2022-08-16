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

// This file includes a set of helper functions for parsing RVFI
// signals when evaluating them directly, outside of the UVM environment,
// mainly for formal verifications and assertions in general.


`ifndef __UVMA_RVFI_FUNCS_SV__
`define __UVMA_RVFI_FUNCS_SV__


// Return wdata of register "gpr"
function bit [ DEFAULT_XLEN-1:0] rvfi_get_gpr_wdata( int gpr,
                                            bit [(32* DEFAULT_XLEN)-1:0] gpr_wdata
                                            );
  return gpr_wdata[gpr* DEFAULT_XLEN +: DEFAULT_XLEN];
endfunction : rvfi_get_gpr_wdata

// Return rdata of register "gpr"
function bit [ DEFAULT_XLEN-1:0] rvfi_get_gpr_rdata( int gpr,
                                            bit [(32* DEFAULT_XLEN)-1:0] gpr_rdata
                                            );
  return gpr_rdata[gpr* DEFAULT_XLEN +: DEFAULT_XLEN];
endfunction : rvfi_get_gpr_rdata

// Return valid data of memory transaction "txn"
function bit [ DEFAULT_XLEN-1:0] rvfi_get_mem_data_word( int txn,
                                                bit [(NMEM* DEFAULT_XLEN)-1:0] mem_wdata,
                                                bit [(NMEM* DEFAULT_XLEN)-1:0] mem_rdata,
                                                bit [(NMEM* DEFAULT_XLEN/8)-1:0] mem_wmask
                                                );
  bit [ DEFAULT_XLEN-1:0] ret;

  for (int i = 0; i <  DEFAULT_XLEN/8; i++) begin
    if (mem_wmask[(txn* DEFAULT_XLEN/8) + i]) begin
      ret[i*8 +:8] = mem_wdata[((txn* DEFAULT_XLEN) + (i*8)) +:8];
    end else begin
      ret[i*8 +:8] = mem_rdata[((txn* DEFAULT_XLEN) + (i*8)) +:8];
    end
  end

  return ret;

endfunction : rvfi_get_mem_data_word

//Return addr of memory transaction "txn"
function bit [ DEFAULT_XLEN-1:0] rvfi_get_mem_addr(  int txn,
                                            bit [(NMEM* DEFAULT_XLEN)-1:0] mem_addr
                                            );

  return mem_addr[txn* DEFAULT_XLEN +: DEFAULT_XLEN];

endfunction : rvfi_get_mem_addr

//Return rmask of memory transaction "txn"
function bit [( DEFAULT_XLEN/8)-1:0] rvfi_get_mem_rmask( int txn,
                                                bit [(NMEM* DEFAULT_XLEN/8)-1:0] mem_rmask
                                                );

   return mem_rmask[(txn* DEFAULT_XLEN/8) +:( DEFAULT_XLEN/8)];

endfunction : rvfi_get_mem_rmask

//Return wmask of memory transaction "txn"
function bit [( DEFAULT_XLEN/8)-1:0] rvfi_get_mem_wmask( int txn,
                                                bit [(NMEM* DEFAULT_XLEN/8)-1:0] mem_wmask
                                                );

   return mem_wmask[(txn* DEFAULT_XLEN/8) +:( DEFAULT_XLEN/8)];

endfunction : rvfi_get_mem_wmask


//Check memory transaction activity

//Checks if a position in the rvfi memory transaction list
//indicates any activity.
//return {read, write}
function bit [1:0] rvfi_check_mem_act(  int txn,
                                        bit [(NMEM* DEFAULT_XLEN/8)-1:0] mem_rmask,
                                        bit [(NMEM* DEFAULT_XLEN/8)-1:0] mem_wmask
                                        );
   static bit read = 0;
   static bit write = 0;

   if (mem_rmask[(txn* DEFAULT_XLEN/8) +:( DEFAULT_XLEN/8)]) begin
      read = 1;
   end
   if (mem_wmask[(txn* DEFAULT_XLEN/8) +:( DEFAULT_XLEN/8)]) begin
      write = 1;
   end

   return {read,write};

endfunction : rvfi_check_mem_act

function bit rvfi_match_instr(  bit [ DEFAULT_XLEN-1:0] instr,
                                bit [ DEFAULT_XLEN-1:0] ref_instr,
                                bit [ DEFAULT_XLEN-1:0] ref_mask
                                );

  if ((instr & ref_mask) == ref_instr) begin
    return 1;
  end
  else begin
    return 0;
  end

endfunction : rvfi_match_instr
`endif // __UVMA_RVFI_FUNCS_SV__
