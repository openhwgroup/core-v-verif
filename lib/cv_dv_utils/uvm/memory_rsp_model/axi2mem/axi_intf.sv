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

/// An AXI4 interface.
import axi2mem_pkg::*;

interface axi_if ( input bit clk, input bit rstn );

  parameter int unsigned wd_addr = 0;
  parameter int unsigned wd_data = 0;
  parameter int unsigned wd_id   = 0;
  parameter int unsigned wd_user = 0;

  localparam int unsigned wd_strb = wd_data / 8;


  logic                      aw_valid;
  logic                      aw_ready;
  logic [wd_addr-1:0]        aw_addr;
  logic [7:0]                aw_len;
  logic [2:0]                aw_size;
  logic [5:0]                aw_atop;
  logic [wd_id-1:0]          aw_id;
  axi_burst_t                aw_burst;
  logic                      aw_lock;
  axi_cache_t                aw_cache;
  logic [2:0]                aw_prot;
  logic [3:0]                aw_qos;
  logic [3:0]                aw_region;
  logic [wd_user-1:0]        aw_user;

  logic                      w_valid;
  logic                      w_ready;
  logic [wd_strb-1:0]        w_strb;
  logic [wd_data-1:0]        w_data;
  logic                      w_last;
  logic [wd_user-1:0]        w_user;

  logic                      b_valid;
  logic                      b_ready;
  axi_resp_t                 b_resp;
  logic [wd_id-1:0]          b_id;
  logic [wd_user-1:0]        b_user;

  logic                      ar_valid;
  logic                      ar_ready;
  logic [wd_addr-1:0]        ar_addr;
  logic [7:0]                ar_len;
  logic [2:0]                ar_size;
  axi_burst_t                ar_burst;
  logic [wd_id-1:0]          ar_id;
  logic                      ar_lock;
  axi_cache_t                ar_cache;
  logic [2:0]                ar_prot;
  logic [3:0]                ar_qos;
  logic [3:0]                ar_region;
  logic [wd_user-1:0]        ar_user;

  logic                      r_valid;
  logic                      r_ready;
  logic [wd_data-1:0]        r_data;
  logic                      r_last;
  logic [wd_id-1:0]          r_id;
  axi_resp_t                 r_resp;
  logic [wd_user-1:0]        r_user;
 
endinterface

