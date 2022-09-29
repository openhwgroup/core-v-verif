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


`define  RVFI_CSR_BIND(csr_name)
`define  RVFI_CSR_IDX_BIND(csr_name,csr_suffix,idx)
`define  RVFI_CSR_UVM_CONFIG_DB_SET(csr_name)


package cvverif_pkg;
endpackage


package uvmt_cv32e40s_pkg;
  `include "uvmt_cv32e40s_constants.sv"
endpackage


package uvme_cv32e40s_pkg;
  parameter ILEN = 32;
  parameter XLEN = 32;
endpackage


package uvma_rvfi_pkg;
  `include "uvma_rvfi_constants.sv"

  typedef struct packed {
    logic [10:0] cause;
    logic        interrupt;
    logic        exception;
    logic        intr;
  } rvfi_intr_t;
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


`define UVMA_OBI_MEMORY_ADDR_DEFAULT_WIDTH   32
`define UVMA_OBI_MEMORY_DATA_DEFAULT_WIDTH   32
`define UVMA_OBI_MEMORY_AUSER_DEFAULT_WIDTH   1
`define UVMA_OBI_MEMORY_WUSER_DEFAULT_WIDTH   1
`define UVMA_OBI_MEMORY_RUSER_DEFAULT_WIDTH   1
`define UVMA_OBI_MEMORY_ID_DEFAULT_WIDTH      1
`define UVMA_OBI_MEMORY_ACHK_DEFAULT_WIDTH    1
`define UVMA_OBI_MEMORY_RCHK_DEFAULT_WIDTH    1
interface uvma_obi_memory_if #(
   parameter AUSER_WIDTH = `UVMA_OBI_MEMORY_AUSER_DEFAULT_WIDTH,
   parameter WUSER_WIDTH = `UVMA_OBI_MEMORY_WUSER_DEFAULT_WIDTH,
   parameter RUSER_WIDTH = `UVMA_OBI_MEMORY_RUSER_DEFAULT_WIDTH,
   parameter ADDR_WIDTH  = `UVMA_OBI_MEMORY_ADDR_DEFAULT_WIDTH ,
   parameter DATA_WIDTH  = `UVMA_OBI_MEMORY_DATA_DEFAULT_WIDTH ,
   parameter ID_WIDTH    = `UVMA_OBI_MEMORY_ID_DEFAULT_WIDTH   ,
   parameter ACHK_WIDTH  = `UVMA_OBI_MEMORY_ACHK_DEFAULT_WIDTH ,
   parameter RCHK_WIDTH  = `UVMA_OBI_MEMORY_RCHK_DEFAULT_WIDTH
  )(
    input logic clk,
    input logic reset_n
  );
   wire                         req;
   wire                         gnt;
   wire [(ADDR_WIDTH-1):0]      addr;
   wire                         we;
   wire [((DATA_WIDTH/8)-1):0]  be;
   wire [(DATA_WIDTH-1):0]      wdata;
   wire [(AUSER_WIDTH-1):0]     auser;
   wire [(WUSER_WIDTH-1):0]     wuser;
   wire [(ID_WIDTH-1):0]        aid;
   wire [5:0]                   atop;
   wire [1:0]                   memtype;
   wire [2:0]                   prot;
   wire                         reqpar;
   wire                         gntpar;
   wire [(ACHK_WIDTH-1):0]      achk;

   wire                      rvalid;
   wire                      rready;
   wire [(DATA_WIDTH-1):0]   rdata;
   wire                      err;
   wire [(RUSER_WIDTH-1):0]  ruser;
   wire [(ID_WIDTH-1):0]     rid;
   wire                      exokay;
   wire                      rvalidpar;
   wire                      rreadypar;
   wire [(RCHK_WIDTH-1):0]   rchk;
endinterface


module mm_ram
 #(
     parameter RAM_ADDR_WIDTH    =  16,
               INSTR_RDATA_WIDTH = 128, // width of read_data on instruction bus
               DATA_RDATA_WIDTH  =  32, // width of read_data on data bus
               DBG_ADDR_WIDTH    =  14, // POT ammount of memory allocated for debugger
                                        // physically located at end of memory
               IRQ_WIDTH         =  32  // IRQ vector width
  )
  (
     input logic                          clk_i,
     input logic                          rst_ni,
     input logic [31:0]                   dm_halt_addr_i,

     input logic                          instr_req_i,
     input logic [31:0]                   instr_addr_i,
     output logic [INSTR_RDATA_WIDTH-1:0] instr_rdata_o,
     output logic                         instr_rvalid_o,
     output logic                         instr_gnt_o,

     input logic                          data_req_i,
     input logic [31:0]                   data_addr_i,
     input logic                          data_we_i,
     input logic [3:0]                    data_be_i,
     input logic [31:0]                   data_wdata_i,
     output logic [31:0]                  data_rdata_o,
     output logic                         data_rvalid_o,
     output logic                         data_gnt_o,

     input logic [4:0]                    irq_id_i,
     input logic                          irq_ack_i,
     output logic [IRQ_WIDTH-1:0]         irq_o,

     input logic [31:0]                   pc_core_id_i,

     output logic                         debug_req_o,

     output logic                         tests_passed_o,
     output logic                         tests_failed_o,
     output logic                         exit_valid_o,
     output logic [31:0]                  exit_value_o
);
endmodule


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

