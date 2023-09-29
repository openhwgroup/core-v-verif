// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Copyright 2020,2023 OpenHW Group
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
//
///////////////////////////////////////////////////////////////////////////////


`ifndef __UVMT_CV32E20_DUT_WRAP_SV__
`define __UVMT_CV32E20_DUT_WRAP_SV__

import uvm_pkg::*; // needed for the UVM messaging service (`uvm_info(), etc.)
import cve2_pkg::*;// definitions of enumerated types used by cve2

/**
 * Wrapper for the CV32E20 RTL DUT.
 * Includes the RVFI Tracer and the IBEX core.
 */
module uvmt_cv32e20_dut_wrap #(
                            // CV32E20 parameters.  See User Manual.
                            parameter int unsigned MHPMCounterNum    = 10,
                            parameter int unsigned MHPMCounterWidth  = 40,
                            parameter bit          RV32E             = 1'b0,
                            parameter rv32m_e      RV32M             = RV32MFast,
                            parameter bit          BranchPredictor   = 1'b0,
                            parameter int unsigned DmHaltAddr        = 32'h1A110800,
                            parameter int unsigned DmExceptionAddr   = 32'h1A110808,
                            // Remaining parameters are used by TB components only
                            parameter int unsigned INSTR_ADDR_WIDTH    =  32,
                            parameter int unsigned INSTR_RDATA_WIDTH   =  32,
                            parameter int unsigned RAM_ADDR_WIDTH      =  22
                           )

                           (
                            uvma_clknrst_if              clknrst_if,
                            uvma_interrupt_if            interrupt_if,
                            // vp_status_if is driven by ENV and used in TB
                            uvma_interrupt_if            vp_interrupt_if,
                            uvmt_cv32e20_core_cntrl_if  core_cntrl_if,
                            uvmt_cv32e20_core_status_if core_status_if,
                            uvma_obi_memory_if           obi_memory_instr_if,
                            uvma_obi_memory_if           obi_memory_data_if
                           );

    // signals connecting core to memory
    logic                         instr_req;
    logic                         instr_gnt;
    logic                         instr_rvalid;
    logic [INSTR_ADDR_WIDTH-1 :0] instr_addr;
    logic [INSTR_RDATA_WIDTH-1:0] instr_rdata;

    logic                         data_req;
    logic                         data_gnt;
    logic                         data_rvalid;
    logic [31:0]                  data_addr;
    logic                         data_we;
    logic [3:0]                   data_be;
    logic [31:0]                  data_rdata;
    logic [31:0]                  data_wdata;

    logic [31:0]                  irq_vp;
    logic [31:0]                  irq_uvma;
    logic [31:0]                  irq;
    logic                         irq_ack;
    logic [ 4:0]                  irq_id;

    logic                         debug_req_vp;
    logic                         debug_req_uvma;
    logic                         debug_req;
    logic                         debug_havereset;
    logic                         debug_running;
    logic                         debug_halted;

    assign debug_if.clk      = clknrst_if.clk;
    assign debug_if.reset_n  = clknrst_if.reset_n;
    assign debug_req_uvma    = debug_if.debug_req;

    assign debug_req = debug_req_vp | debug_req_uvma;

    // --------------------------------------------
    // Instruction bus is read-only, OBI v1.0
    assign obi_memory_instr_if.we        = 'b0;
    assign obi_memory_instr_if.be        = '1;
    // Data bus is read/write, OBI v1.0

    // --------------------------------------------
    // Connect to uvma_interrupt_if
    assign interrupt_if.clk                     = clknrst_if.clk;
    assign interrupt_if.reset_n                 = clknrst_if.reset_n;
    assign irq_uvma                             = interrupt_if.irq;
    assign interrupt_if.irq_id                  = cv32e20_top_i.u_cve2_top.u_cve2_core.id_stage_i.controller_i.exc_cause_o[4:0]; //irq_id;
//    assign interrupt_if.irq_ack                 = cv32e20_top_i.u_cve2_top.u_cve2_core.id_stage_i.controller_i.handle_irq; //irq_ack;
    assign interrupt_if.irq_ack                 = (cv32e20_top_i.u_cve2_top.u_cve2_core.id_stage_i.controller_i.ctrl_fsm_cs == 4'h7);//irq_ack

    assign vp_interrupt_if.clk                  = clknrst_if.clk;
    assign vp_interrupt_if.reset_n              = clknrst_if.reset_n;
    assign irq_vp                               = irq_uvma;
    // {irq_q[31:16], pending_enabled_irq_q[11], pending_enabled_irq_q[3], pending_enabled_irq_q[7]}
    // was vp_interrupt_if.irq;
    assign vp_interrupt_if.irq_id               = cv32e20_top_i.u_cve2_top.u_cve2_core.id_stage_i.controller_i.exc_cause_o[4:0];    //irq_id;
    assign vp_interrupt_if.irq_ack              = (cv32e20_top_i.u_cve2_top.u_cve2_core.id_stage_i.controller_i.ctrl_fsm_cs == 4'h7);//irq_ack

    assign irq = irq_uvma | irq_vp;

    // ------------------------------------------------------------------------
    // Instantiate the core
//    cve2_top #( 
    cve2_top_tracing #( 
               .MHPMCounterNum   (MHPMCounterNum),
               .MHPMCounterWidth (MHPMCounterWidth),
               .RV32E            (RV32E),
               .RV32M            (RV32M),
               .BranchPredictor  (BranchPredictor),
               .DmHaltAddr       (DmHaltAddr),
               .DmExceptionAddr  (DmExceptionAddr)
              )
    cv32e20_top_i
        (
         .clk_i                  ( clknrst_if.clk                 ),
         .rst_ni                 ( clknrst_if.reset_n             ),

         .test_en_i              ( 1'b1                           ), // enable all clock gates for testing
         .ram_cfg_i              ( prim_ram_1p_pkg::RAM_1P_CFG_DEFAULT ),

         .hart_id_i              ( 32'h0000_0000                  ),
         .boot_addr_i            ( 32'h0000_0000                  ), //<---MJS changing to 0 

  // Instruction memory interface
         .instr_req_o            ( obi_memory_instr_if.req        ), // core to agent
         .instr_gnt_i            ( obi_memory_instr_if.gnt        ), // agent to core
         .instr_rvalid_i         ( obi_memory_instr_if.rvalid     ),
         .instr_addr_o           ( obi_memory_instr_if.addr       ),
         .instr_rdata_i          ( obi_memory_instr_if.rdata      ),
         .instr_err_i            ( '0                             ),

  // Data memory interface
         .data_req_o             ( obi_memory_data_if.req         ),
         .data_gnt_i             ( obi_memory_data_if.gnt         ),
         .data_rvalid_i          ( obi_memory_data_if.rvalid      ),
         .data_we_o              ( obi_memory_data_if.we          ),
         .data_be_o              ( obi_memory_data_if.be          ),
         .data_addr_o            ( obi_memory_data_if.addr        ),
         .data_wdata_o           ( obi_memory_data_if.wdata       ),
         .data_rdata_i           ( obi_memory_data_if.rdata       ),
         .data_err_i             ( '0                             ),

  // Interrupt inputs
         .irq_software_i         ( irq_uvma[3]),
         .irq_timer_i            ( irq_uvma[7]),
         .irq_external_i         ( irq_uvma[11]),
         .irq_fast_i             ( irq_uvma[30:16]),
         .irq_nm_i               ( irq_uvma[31]),       // non-maskeable interrupt

  // Debug Interface
         .debug_req_i             ('0),
         .crash_dump_o            (),

  // RISC-V Formal Interface
  // Does not comply with the coding standards of _i/_o suffixes, but follows
  // the convention of RISC-V Formal Interface Specification.
/*
`ifdef RVFI
         .rvfi_valid              (),
         .rvfi_order              (),
         .rvfi_insn               (),
         .rvfi_trap               (),
         .rvfi_halt               (),
         .rvfi_intr               (),
         .rvfi_mode               (),
         .rvfi_ixl                (),
         .rvfi_rs1_addr           (),
         .rvfi_rs2_addr           (),
         .rvfi_rs3_addr           (),
         .rvfi_rs1_rdata          (),
         .rvfi_rs2_rdata          (),
         .rvfi_rs3_rdata          (),
         .rvfi_rd_addr            (),
         .rvfi_rd_wdata           (),
         .rvfi_pc_rdata           (),
         .rvfi_pc_wdata           (),
         .rvfi_mem_addr           (),
         .rvfi_mem_rmask          (),
         .rvfi_mem_wmask          (),
         .rvfi_mem_rdata          (),
         .rvfi_mem_wdata          (),
         .rvfi_ext_mip            (),
         .rvfi_ext_nmi            (),
         .rvfi_ext_debug_req      (),
         .rvfi_ext_mcycle         (),
`endif
 */ //LRH
  // CPU Control Signals
         .fetch_enable_i          ('1), // fetch_enable_t
         .core_sleep_o            ()
        );


endmodule : uvmt_cv32e20_dut_wrap

`endif // __UVMT_CV32E20_DUT_WRAP_SV__


