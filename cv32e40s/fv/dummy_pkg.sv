// TODO:silabs-robin  Delete this file, make core-v-verif files fv compatible.


// Copyright 2022 Silicon Labs, Inc.
// Copyright 2022 OpenHW Group
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
//
// SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0


// Create bind for RVFI CSR interface
`define RVFI_CSR_BIND(csr_name) \
  bind cv32e40s_wrapper \
    uvma_rvfi_csr_if#(uvme_cv32e40s_pkg::XLEN) rvfi_csr_``csr_name``_if_0_i(.clk(clk_i), \
                                                                            .reset_n(rst_ni), \
                                                                            .rvfi_csr_rmask(rvfi_i.rvfi_csr_``csr_name``_rmask), \
                                                                            .rvfi_csr_wmask(rvfi_i.rvfi_csr_``csr_name``_wmask), \
                                                                            .rvfi_csr_rdata(rvfi_i.rvfi_csr_``csr_name``_rdata), \
                                                                            .rvfi_csr_wdata(rvfi_i.rvfi_csr_``csr_name``_wdata) \
    );


`define  RVFI_CSR_IDX_BIND(csr_name,csr_suffix,idx)
`define  RVFI_CSR_UVM_CONFIG_DB_SET(csr_name)


package cvverif_pkg;
endpackage


`include "uvma_obi_memory_macros.sv"


package uvmt_cv32e40s_pkg;
  `include "uvmt_cv32e40s_constants.sv"
  `include "uvmt_cv32e40s_tdefs.sv"

  import cv32e40s_pkg::*;
endpackage


package uvme_cv32e40s_pkg;
  `include "uvme_cv32e40s_constants.sv"
endpackage


package uvma_rvfi_pkg;
  `include "uvma_rvfi_constants.sv"
  `include "uvma_rvfi_tdefs.sv"
endpackage


package uvma_fencei_pkg;
endpackage


package svlib_pkg;
  function automatic longint sys_dayTime();
  endfunction: sys_dayTime
endpackage


interface uvma_rvfi_csr_if
  import uvma_rvfi_pkg::*;
  #(int XLEN=DEFAULT_XLEN)
  (
    input                      clk,
    input                      reset_n,

    input [XLEN-1:0]           rvfi_csr_rmask,
    input [XLEN-1:0]           rvfi_csr_wmask,
    input [XLEN-1:0]           rvfi_csr_rdata,
    input [XLEN-1:0]           rvfi_csr_wdata
  );
endinterface


interface uvma_obi_if
   (
       input clk,
       input reset_n,
       input req,
       input gnt,
       input [31:0] addr,
       input we,
       input [3:0] be,
       input [31:0] wdata,
       input [31:0] rdata,
       input rvalid,
       input rready
   );
endinterface


class uvm_config_db#(type T=int);
  //static function void set(uvm_component cntxt,
  static function void set(chandle cntxt,
                           string inst_name,
                           string field_name,
                           T value);
  endfunction

  //static function bit get(uvm_component cntxt,
  static function bit get(chandle cntxt,
                          string inst_name,
                          string field_name,
                          inout T value);
  endfunction
endclass


class uvm_report_server;
  //function int get_severity_count(uvm_severity severity);
  function int get_severity_count(int severity);
  endfunction
endclass


interface uvma_isacov_if;
  event        retire;
  logic [31:0] instr;
endinterface


interface uvma_clknrst_if;
  logic clk;
  logic reset_n;
  logic [63:0] clk_period;
endinterface


interface uvma_debug_if;
  logic clk;
  logic reset_n;
  logic debug_req;
endinterface


interface uvma_interrupt_if;
  logic clk;
  logic reset_n;
  logic [31:0] irq;
  logic [9:0] irq_id;
  logic irq_ack;
endinterface


interface uvme_cv32e40s_core_cntrl_if;
  logic        clk;
  logic        fetch_en;

  logic        scan_cg_en;
  logic [31:0] boot_addr;
  logic [31:0] mtvec_addr;
  logic [31:0] dm_halt_addr;
  logic [31:0] dm_exception_addr;
  logic [31:0] nmi_addr;
  logic [31:0] mhartid;
  logic [3:0]  mimpid_patch;

  logic [31:0] num_mhpmcounters;
  cv32e40s_pkg::b_ext_e b_ext;
endinterface


`include "uvma_obi_memory_if.sv"
`include "uvma_clic_if.sv"


module uvmt_cv32e40s_iss_wrap
  #(
    parameter int ROM_START_ADDR = 'h00000000,
    parameter int ROM_BYTE_SIZE  = 'h0,
    parameter int RAM_BYTE_SIZE  = 'h1B000000,
    parameter int ID = 0
   )

   (
    input realtime                clk_period,
    uvma_clknrst_if               clknrst_if
   );
endmodule


module uvma_obi_assert
  #(
    parameter int ADDR_WIDTH=32,
    parameter int DATA_WIDTH=32
  )
  (
    input                    clk,
    input                    reset_n,

    input                    req,
    input                    gnt,
    input [ADDR_WIDTH-1:0]   addr,
    input                    we,
    input [DATA_WIDTH/8-1:0] be,
    input [DATA_WIDTH-1:0]   wdata,
    input [DATA_WIDTH-1:0]   rdata,
    input                    rvalid,
    input                    rready
  );
endmodule


module uvma_obi_memory_assert_if_wrp
  #(
    parameter int unsigned ADDR_WIDTH  = 32,
    parameter int unsigned DATA_WIDTH  = 32,
    parameter int unsigned AUSER_WIDTH = 0,
    parameter int unsigned WUSER_WIDTH = 0,
    parameter int unsigned RUSER_WIDTH = 0,
    parameter int unsigned ID_WIDTH    = 0,
    parameter int unsigned ACHK_WIDTH  = 0,
    parameter int unsigned RCHK_WIDTH  = 0,
    parameter bit          IS_1P2      = 0
  )
  (
    uvma_obi_memory_if obi
  );
endmodule

