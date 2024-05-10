// ----------------------------------------------------------------------------
//Copyright 2023 CEA*
//*Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
//
//Licensed under the Apache License, Version 2.0 (the "License");
//you may not use this file except in compliance with the License.
//You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
//Unless required by applicable law or agreed to in writing, software
//distributed under the License is distributed on an "AS IS" BASIS,
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//See the License for the specific language governing permissions and
//limitations under the License.
//[END OF HEADER]
// ----------------------------------------------------------------------------

package axi2mem_pkg;

    timeunit 1ns;

    import uvm_pkg::*;

    typedef enum logic [1:0] {
       BURST_FIXED = 2'b00,
       BURST_INCR  = 2'b01,
       BURST_WRAP  = 2'b10
    } axi_burst_t; 

    typedef enum logic [1:0] {
      RESP_OKAY   = 2'b00,
      RESP_EXOKAY = 2'b01,
      RESP_SLVERR = 2'b10,
      RESP_DECERR = 2'b11
    } axi_resp_t; 

    typedef enum logic [3:0] {
      CACHE_BUFFERABLE = 4'b0001,
      CACHE_MODIFIABLE = 4'b0010,
      CACHE_RD_ALLOC   = 4'b0100,
      CACHE_WR_ALLOC   = 4'b1000
    } axi_cache_t; 


  // 3:0 if 5:4 = 'b11
  localparam AXI_ATOMIC_SWAP  = 0000;
  localparam AXI_ATOMIC_CMP   = 0001;
  // ATOMIC[5:4]
  /// Perform no atomic operation.
  localparam AXI_ATOMIC_NONE        = 2'b00;
  localparam AXI_ATOMIC_STORE   = 2'b01;
  localparam AXI_ATOMIC_LOAD    = 2'b10;
  localparam AXI_ATOMIC_OTHERS  = 2'b11; // SWP, CMP
  localparam AXI_ATOMIC_LITTLE_END  = 1'b0;
  localparam AXI_ATOMIC_BIG_END     = 1'b1;
  localparam AXI_ATOMIC_ADD   = 3'b000;
  localparam AXI_ATOMIC_CLR   = 3'b001;
  localparam AXI_ATOMIC_EOR   = 3'b010;
  localparam AXI_ATOMIC_SET   = 3'b011;
  localparam AXI_ATOMIC_SMAX  = 3'b100;
  localparam AXI_ATOMIC_SMIN  = 3'b101;
  localparam AXI_ATOMIC_UMAX  = 3'b110;
  localparam AXI_ATOMIC_UMIN  = 3'b111;


    import memory_rsp_model_pkg::*;

    `include "uvm_macros.svh";
    `include "axi2mem.svh";

endpackage :axi2mem_pkg


