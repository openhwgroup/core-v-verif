///////////////////////////////////////////////////////////////////////////////
//
// Copyright 2021 OpenHW Group
// Copyright 2021 Thales DIS Design Services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//
///////////////////////////////////////////////////////////////////////////////
//
// CVA6 "core_only" testbench wrapper.
//
///////////////////////////////////////////////////////////////////////////////

`define MAIN_MEM(P) uvmt_cva6_tb.cva6_dut_wrap.cva6_tb_wrapper_i.i_sram.gen_cut[0].i_tc_sram_wrapper.i_tc_sram.init_val[(``P``)]
`define USER_MEM(P) uvmt_cva6_tb.cva6_dut_wrap.cva6_tb_wrapper_i.i_sram.gen_cut[0].gen_mem_user.i_tc_sram_wrapper_user.i_tc_sram.init_val[(``P``)]

import uvm_pkg::*;

`include "uvm_macros.svh"

import "DPI-C" function read_elf(input string filename);
import "DPI-C" function byte get_section(output longint address, output longint len);
import "DPI-C" context function void read_section(input longint address, inout byte buffer[]);

module cva6_tb_wrapper
 import uvmt_cva6_pkg::*;
#(
  parameter int unsigned AXI_USER_EN = ariane_pkg::DATA_USER_EN,
  parameter int unsigned NUM_WORDS = 2**25
) (
  input  logic                         clk_i,
  input  logic                         rst_ni,
  input  logic [XLEN-1:0]              boot_addr_i,
  output logic [31:0]                  tb_exit_o,
  output ariane_pkg::rvfi_port_t       rvfi_o,
  input  cvxif_pkg::cvxif_resp_t       cvxif_resp,
  output cvxif_pkg::cvxif_req_t        cvxif_req,
  uvma_axi_intf                        axi_slave,
  uvmt_axi_switch_intf                 axi_switch_vif
);

  ariane_axi_soc::req_t    axi_ariane_req;
  ariane_axi_soc::resp_t   axi_ariane_resp;

  static uvm_cmdline_processor uvcl = uvm_cmdline_processor::get_inst();
  string binary = "";

  ariane_pkg::rvfi_port_t  rvfi;
  assign rvfi_o = rvfi;

  cva6 #(
    .ArianeCfg            ( ariane_soc::ArianeSocCfg  ),
    .AxiAddrWidth         ( ariane_axi_soc::AddrWidth ),
    .AxiDataWidth         ( ariane_axi_soc::DataWidth ),
    .AxiIdWidth           ( ariane_axi_soc::IdWidth   ),
    .AxiUserWidth         ( ariane_axi_soc::UserWidth ),
    .axi_ar_chan_t        ( ariane_axi_soc::ar_chan_t ),
    .axi_r_chan_t         ( ariane_axi_soc::r_chan_t  ),
    .axi_aw_chan_t        ( ariane_axi_soc::aw_chan_t ),
    .axi_w_chan_t         ( ariane_axi_soc::w_chan_t  ),
    .axi_b_chan_t         ( ariane_axi_soc::b_chan_t  ),
    .axi_req_t            ( ariane_axi_soc::req_t     ),
    .axi_rsp_t            ( ariane_axi_soc::resp_t    )
  ) i_cva6 (
    .clk_i                ( clk_i                     ),
    .rst_ni               ( rst_ni                    ),
    .boot_addr_i          ( boot_addr_i               ),//Driving the boot_addr value from the core control agent
    .hart_id_i            ( 64'h0000_0000_0000_0000   ),
    .irq_i                ( 2'b00 /*irqs*/            ),
    .ipi_i                ( 1'b0  /*ipi*/             ),
    .time_irq_i           ( 1'b0  /*timer_irq*/       ),
    .debug_req_i          ( 1'b0                      ),
    .rvfi_o               ( rvfi                      ),
    .cvxif_req_o          ( cvxif_req                 ),
    .cvxif_resp_i         ( cvxif_resp                ),
    .axi_req_o            ( axi_ariane_req            ),
    .axi_resp_i           ( axi_ariane_resp           )
  );

  //----------------------------------------------------------------------------
  // RVFI
  //----------------------------------------------------------------------------

  rvfi_tracer  #(
    .HART_ID(8'h0),
    .DEBUG_START(0),
    .DEBUG_STOP(0),
    .NR_COMMIT_PORTS(ariane_pkg::NR_COMMIT_PORTS)
  ) rvfi_tracer_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .rvfi_i(rvfi),
    .end_of_test_o(tb_exit_o)
  ) ;

  //----------------------------------------------------------------------------
  // Memory
  //----------------------------------------------------------------------------

  logic                         req;
  logic                         we;
  logic ariane_axi_soc::addr_t  addr;
  logic ariane_axi_soc::strb_t  be;
  logic ariane_axi_soc::data_t  wdata;
  logic ariane_axi_soc::user_t  wuser;
  logic ariane_axi_soc::data_t  rdata;
  logic ariane_axi_soc::user_t  ruser;

  //Response structs
   assign axi_ariane_resp.aw_ready = (axi_switch_vif.active) ? axi_slave.aw_ready : cva6_axi_bus.aw_ready;
   assign axi_ariane_resp.ar_ready = (axi_switch_vif.active) ? axi_slave.ar_ready : cva6_axi_bus.ar_ready;
   assign axi_ariane_resp.w_ready  = (axi_switch_vif.active) ? axi_slave.w_ready  : cva6_axi_bus.w_ready;
   assign axi_ariane_resp.b_valid  = (axi_switch_vif.active) ? axi_slave.b_valid  : cva6_axi_bus.b_valid;
   assign axi_ariane_resp.r_valid  = (axi_switch_vif.active) ? axi_slave.r_valid  : cva6_axi_bus.r_valid;
   // B Channel
   assign axi_ariane_resp.b.id   = (axi_switch_vif.active) ? axi_slave.b_id   : cva6_axi_bus.b_id;
   assign axi_ariane_resp.b.resp = (axi_switch_vif.active) ? axi_slave.b_resp : cva6_axi_bus.b_resp;
   assign axi_ariane_resp.b.user = (axi_switch_vif.active) ? axi_slave.b_user : cva6_axi_bus.b_user;
   // R Channel
   assign axi_ariane_resp.r.id   = (axi_switch_vif.active) ? axi_slave.r_id   : cva6_axi_bus.r_id;
   assign axi_ariane_resp.r.data = (axi_switch_vif.active) ? axi_slave.r_data : cva6_axi_bus.r_data;
   assign axi_ariane_resp.r.resp = (axi_switch_vif.active) ? axi_slave.r_resp : cva6_axi_bus.r_resp;
   assign axi_ariane_resp.r.last = (axi_switch_vif.active) ? axi_slave.r_last : cva6_axi_bus.r_last;
   assign axi_ariane_resp.r.user = (axi_switch_vif.active) ? axi_slave.r_user : cva6_axi_bus.r_user;

   assign axi_slave.aw_ready  = (axi_switch_vif.active) ? axi_slave.aw_ready : cva6_axi_bus.aw_ready;
   assign axi_slave.ar_ready  = (axi_switch_vif.active) ? axi_slave.ar_ready : cva6_axi_bus.ar_ready;
   assign axi_slave.w_ready   = (axi_switch_vif.active) ? axi_slave.w_ready  : cva6_axi_bus.w_ready;
   assign axi_slave.b_valid   = (axi_switch_vif.active) ? axi_slave.b_valid  : cva6_axi_bus.b_valid;
   assign axi_slave.r_valid   = (axi_switch_vif.active) ? axi_slave.r_valid  : cva6_axi_bus.r_valid;

   assign axi_slave.b_id      = (axi_switch_vif.active) ? axi_slave.b_id   : cva6_axi_bus.b_id;
   assign axi_slave.b_resp    = (axi_switch_vif.active) ? axi_slave.b_resp : cva6_axi_bus.b_resp;
   assign axi_slave.b_user    = (axi_switch_vif.active) ? axi_slave.b_user : cva6_axi_bus.b_user;

   assign axi_slave.r_id      = (axi_switch_vif.active) ? axi_slave.r_id   : cva6_axi_bus.r_id;
   assign axi_slave.r_data    = (axi_switch_vif.active) ? axi_slave.r_data : cva6_axi_bus.r_data;
   assign axi_slave.r_resp    = (axi_switch_vif.active) ? axi_slave.r_resp : cva6_axi_bus.r_resp;
   assign axi_slave.r_last    = (axi_switch_vif.active) ? axi_slave.r_last : cva6_axi_bus.r_last;
   assign axi_slave.r_user    = (axi_switch_vif.active) ? axi_slave.r_user : cva6_axi_bus.r_user;

   // Request structs
   assign axi_slave.aw_valid = axi_ariane_req.aw_valid;
   assign axi_slave.w_valid  = axi_ariane_req.w_valid;
   assign axi_slave.b_ready  = axi_ariane_req.b_ready;
   assign axi_slave.ar_valid = axi_ariane_req.ar_valid;
   assign axi_slave.r_ready  = axi_ariane_req.r_ready;
   // AW Channel
   assign axi_slave.aw_id     = axi_ariane_req.aw.id;
   assign axi_slave.aw_addr   = axi_ariane_req.aw.addr;
   assign axi_slave.aw_len    = axi_ariane_req.aw.len;
   assign axi_slave.aw_size   = axi_ariane_req.aw.size;
   assign axi_slave.aw_burst  = axi_ariane_req.aw.burst;
   assign axi_slave.aw_lock   = axi_ariane_req.aw.lock;
   assign axi_slave.aw_cache  = axi_ariane_req.aw.cache;
   assign axi_slave.aw_prot   = axi_ariane_req.aw.prot;
   assign axi_slave.aw_qos    = axi_ariane_req.aw.qos;
   assign axi_slave.aw_region = axi_ariane_req.aw.region;
   assign axi_slave.aw_user   = 0;
    // W Channel
   assign axi_slave.w_data = axi_ariane_req.w.data;
   assign axi_slave.w_strb = axi_ariane_req.w.strb;
   assign axi_slave.w_last = axi_ariane_req.w.last;
   assign axi_slave.w_user = 0;
   // AR Channel
   assign axi_slave.ar_id     = axi_ariane_req.ar.id;
   assign axi_slave.ar_addr   = axi_ariane_req.ar.addr;
   assign axi_slave.ar_len    = axi_ariane_req.ar.len;
   assign axi_slave.ar_size   = axi_ariane_req.ar.size;
   assign axi_slave.ar_burst  = axi_ariane_req.ar.burst;
   assign axi_slave.ar_lock   = axi_ariane_req.ar.lock;
   assign axi_slave.ar_cache  = axi_ariane_req.ar.cache;
   assign axi_slave.ar_prot   = axi_ariane_req.ar.prot;
   assign axi_slave.ar_qos    = axi_ariane_req.ar.qos;
   assign axi_slave.ar_region = axi_ariane_req.ar.region;
   assign axi_slave.ar_user   = 0;


  AXI_BUS #(
    .AXI_ADDR_WIDTH ( ariane_axi_soc::AddrWidth    ),
    .AXI_DATA_WIDTH ( ariane_axi_soc::DataWidth    ),
    .AXI_ID_WIDTH   ( ariane_axi_soc::IdWidthSlave ),
    .AXI_USER_WIDTH ( ariane_axi_soc::UserWidth    )
  ) cva6_axi_bus();

  axi_master_connect #(
  ) i_axi_master_connect_cva6_to_mem (
    .axi_req_i  (axi_ariane_req),
    .dis_mem    (axi_switch_vif.active),
    .master     (cva6_axi_bus)
  );

  axi2mem #(
    .AXI_ID_WIDTH   ( ariane_axi_soc::IdWidthSlave ),
    .AXI_ADDR_WIDTH ( ariane_axi_soc::AddrWidth    ),
    .AXI_DATA_WIDTH ( ariane_axi_soc::DataWidth    ),
    .AXI_USER_WIDTH ( ariane_axi_soc::UserWidth    )
  ) i_cva6_axi2mem (
    .clk_i  ( clk_i       ),
    .rst_ni ( rst_ni      ),
    .slave  ( cva6_axi_bus ),
    .req_o  ( req          ),
    .we_o   ( we           ),
    .addr_o ( addr         ),
    .be_o   ( be           ),
    .user_o ( wuser        ),
    .data_o ( wdata        ),
    .user_i ( ruser        ),
    .data_i ( rdata        )
  );

  sram #(
    .USER_WIDTH ( ariane_axi_soc::UserWidth ),
    .DATA_WIDTH ( ariane_axi_soc::DataWidth ),
    .USER_EN    ( AXI_USER_EN               ),
    .SIM_INIT   ( "zeros"                   ),
    .NUM_WORDS  ( NUM_WORDS                 )
  ) i_sram (
    .clk_i      ( clk_i                                                                       ),
    .rst_ni     ( rst_ni                                                                      ),
    .req_i      ( req                                                                         ),
    .we_i       ( we                                                                          ),
    .addr_i     ( addr[$clog2(NUM_WORDS)-1+$clog2(ariane_axi_soc::StrbWidth):$clog2(ariane_axi_soc::StrbWidth)] ),
    .wuser_i    ( wuser                                                                       ),
    .wdata_i    ( wdata                                                                       ),
    .be_i       ( be                                                                          ),
    .ruser_o    ( ruser                                                                       ),
    .rdata_o    ( rdata                                                                       )
  );

    initial begin
        wait (
          !$isunknown(axi_switch_vif.active)
        );
        if(!axi_switch_vif.active) begin
           automatic logic [7:0][7:0] mem_row;
           longint address;
           longint len;
           byte buffer[];
           void'(uvcl.get_arg_value("+PRELOAD=", binary));

           if (binary != "") begin

               void'(read_elf(binary));

               wait(clk_i);

               // while there are more sections to process
               while (get_section(address, len)) begin
                   automatic int num_words0 = (len+7)/8;
                   `uvm_info( "Core Test", $sformatf("Loading Address: %x, Length: %x", address, len), UVM_LOW)
                   buffer = new [num_words0*8];
                   void'(read_section(address, buffer));
                   // preload memories
                   // 64-bit
                   for (int i = 0; i < num_words0; i++) begin
                       mem_row = '0;
                       for (int j = 0; j < 8; j++) begin
                           mem_row[j] = buffer[i*8 + j];
                       end
                       `MAIN_MEM((address[23:0] >> 3) + i) = mem_row;
                   end
               end
           end
        end
    end

endmodule
