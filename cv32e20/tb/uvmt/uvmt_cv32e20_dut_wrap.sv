// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Copyright 2020,2022 OpenHW Group
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


/**
 * Wrapper for the CV32E20 RTL DUT.
 * Includes the RVFI Tracer and the IBEX core.
 */
module uvmt_cv32e20_dut_wrap #(
                            // CV32E20 parameters.  See User Manual.
                            parameter PULP_XPULP          =  0,
                                      PULP_CLUSTER        =  0,
                                      FPU                 =  0,
                                      PULP_ZFINX          =  0,
                                      NUM_MHPMCOUNTERS    =  1,
                            // Remaining parameters are used by TB components only
                                      INSTR_ADDR_WIDTH    =  32,
                                      INSTR_RDATA_WIDTH   =  32,
                                      RAM_ADDR_WIDTH      =  22
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

    import uvm_pkg::*; // needed for the UVM messaging service (`uvm_info(), etc.)

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
    assign vp_interrupt_if.clk                  = clknrst_if.clk;
    assign vp_interrupt_if.reset_n              = clknrst_if.reset_n;
    assign irq_vp                               = vp_interrupt_if.irq;
    assign interrupt_if.irq_id                  = irq_id;
    assign interrupt_if.irq_ack                 = irq_ack;

    assign irq = irq_uvma | irq_vp;

    // ------------------------------------------------------------------------
    // Instantiate the core
    ibex_top #(
               // TODO: work out parameterization for CV32E20 v1.0.0
               //parameter bit          PMPEnable        = 1'b0,
               //parameter int unsigned PMPGranularity   = 0,
               //parameter int unsigned PMPNumRegions    = 4,
               //parameter int unsigned MHPMCounterNum   = 0,
               //parameter int unsigned MHPMCounterWidth = 40,
               //parameter bit          RV32E            = 1'b0,
               //parameter rv32m_e      RV32M            = RV32MFast,
               //parameter rv32b_e      RV32B            = RV32BNone,
               //parameter regfile_e    RegFile          = RegFileFF,
               //parameter bit          BranchTargetALU  = 1'b0,
               //parameter bit          WritebackStage   = 1'b0,
               //parameter bit          ICache           = 1'b0,
               //parameter bit          ICacheECC        = 1'b0,
               //parameter bit          BranchPredictor  = 1'b0,
               //parameter bit          DbgTriggerEn     = 1'b0,
               //parameter int unsigned DbgHwBreakNum    = 1,
               //parameter bit          SecureIbex       = 1'b0,
               //parameter bit          ICacheScramble   = 1'b0,
               //parameter lfsr_seed_t  RndCnstLfsrSeed  = RndCnstLfsrSeedDefault,
               //parameter lfsr_perm_t  RndCnstLfsrPerm  = RndCnstLfsrPermDefault,
               //parameter int unsigned DmHaltAddr       = 32'h1A110800,
               //parameter int unsigned DmExceptionAddr  = 32'h1A110808,
               //// Default seed and nonce for scrambling
               //parameter logic [SCRAMBLE_KEY_W-1:0]   RndCnstIbexKey   = RndCnstIbexKeyDefault,
               //parameter logic [SCRAMBLE_NONCE_W-1:0] RndCnstIbexNonce = RndCnstIbexNonceDefault
              )
    cv32e20_top_i
        (
         .clk_i                  ( clknrst_if.clk                 ),
         .rst_ni                 ( clknrst_if.reset_n             ),

         .test_en_i              ( 1'b1                           ), // enable all clock gates for testing
         .ram_cfg_i              ( prim_ram_1p_pkg::RAM_1P_CFG_DEFAULT ),

         .hart_id_i              ( 32'h0000_0000                  ),
         .boot_addr_i            ( 32'h0000_0800                  ),

  // Instruction memory interface
         .instr_req_o            ( obi_memory_instr_if.req        ), // core to agent
         .instr_gnt_i            ( obi_memory_instr_if.gnt        ), // agent to core
         .instr_rvalid_i         ( obi_memory_instr_if.rvalid     ),
         .instr_addr_o           ( obi_memory_instr_if.addr       ),
         .instr_rdata_i          ( obi_memory_instr_if.rdata      ),
         .instr_rdata_intg_i     ( '0                             ),
         .instr_err_i            ( '0                             ),

  // Data memory interface
         .data_req_o             ( obi_memory_data_if.req         ),
         .data_gnt_i             ( obi_memory_data_if.gnt         ),
         .data_rvalid_i          ( obi_memory_data_if.rvalid      ),
         .data_we_o              ( obi_memory_data_if.we          ),
         .data_be_o              ( obi_memory_data_if.be          ),
         .data_addr_o            ( obi_memory_data_if.addr        ),
         .data_wdata_o           ( obi_memory_data_if.wdata       ),
         .data_wdata_intg_o      (                                ),
         .data_rdata_i           ( obi_memory_data_if.rdata       ),
         .data_rdata_intg_i      ( '0                             ),
         .data_err_i             ( '0                             ),

  // Interrupt inputs
         .irq_software_i         ( '0),
         .irq_timer_i            ( '0),
         .irq_external_i         ( '0),
         .irq_fast_i             ( '0),
         .irq_nm_i               ( '0),       // non-maskeable interrupt

  // Scrambling Interface
         .scramble_key_valid_i    ('0),
         .scramble_key_i          ('0),
         .scramble_nonce_i        ('0),
         .scramble_req_o          (),

  // Debug Interface
         .debug_req_i             ('0),
         .crash_dump_o            (),
         .double_fault_seen_o     (),

  // RISC-V Formal Interface
  // Does not comply with the coding standards of _i/_o suffixes, but follows
  // the convention of RISC-V Formal Interface Specification.
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

  // CPU Control Signals
         .fetch_enable_i          ('1), // fetch_enable_t
         .alert_minor_o           (),
         .alert_major_internal_o  (),
         .alert_major_bus_o       (),
         .core_sleep_o            (),

  // DFT bypass controls
         .scan_rst_ni             (1'b1)
        );
    /*
    cv32e20_wrapper #(
                 .PULP_XPULP       (PULP_XPULP),
                 .PULP_CLUSTER     (PULP_CLUSTER),
                 .FPU              (FPU),
                 .PULP_ZFINX       (PULP_ZFINX),
                 .NUM_MHPMCOUNTERS (NUM_MHPMCOUNTERS)
                )
    cv32e20_wrapper_i
        (
         .clk_i                  ( clknrst_if.clk                 ),
         .rst_ni                 ( clknrst_if.reset_n             ),

         .pulp_clock_en_i        ( core_cntrl_if.pulp_clock_en    ),
         .scan_cg_en_i           ( core_cntrl_if.scan_cg_en       ),

         .boot_addr_i            ( core_cntrl_if.boot_addr        ),
         .mtvec_addr_i           ( core_cntrl_if.mtvec_addr       ),
         .dm_halt_addr_i         ( core_cntrl_if.dm_halt_addr     ),
         .hart_id_i              ( core_cntrl_if.hart_id          ),
         .dm_exception_addr_i    ( core_cntrl_if.dm_exception_addr),

         .instr_req_o            ( obi_memory_instr_if.req        ), // core to agent
         .instr_gnt_i            ( obi_memory_instr_if.gnt        ), // agent to core
         .instr_rvalid_i         ( obi_memory_instr_if.rvalid     ),
         .instr_addr_o           ( obi_memory_instr_if.addr       ),
         .instr_rdata_i          ( obi_memory_instr_if.rdata      ),

         .data_req_o             ( obi_memory_data_if.req         ),
         .data_gnt_i             ( obi_memory_data_if.gnt         ),
         .data_rvalid_i          ( obi_memory_data_if.rvalid      ),
         .data_we_o              ( obi_memory_data_if.we          ),
         .data_be_o              ( obi_memory_data_if.be          ),
         .data_addr_o            ( obi_memory_data_if.addr        ),
         .data_wdata_o           ( obi_memory_data_if.wdata       ),
         .data_rdata_i           ( obi_memory_data_if.rdata       ),

         // APU not verified in cv32e20 (future work)
         .apu_req_o              (                                ),
         .apu_gnt_i              ( 1'b0                           ),
         .apu_operands_o         (                                ),
         .apu_op_o               (                                ),
         .apu_flags_o            (                                ),
         .apu_rvalid_i           ( 1'b0                           ),
         .apu_result_i           ( {32{1'b0}}                     ),
         .apu_flags_i            ( {5{1'b0}}                      ), // APU_NUSFLAGS_CPU

         .irq_i                  ( irq_uvma                       ),
         .irq_ack_o              ( irq_ack                        ),
         .irq_id_o               ( irq_id                         ),

         .debug_req_i            ( debug_req_uvma                 ),
         .debug_havereset_o      ( debug_havereset                ),
         .debug_running_o        ( debug_running                  ),
         .debug_halted_o         ( debug_halted                   ),

         .fetch_enable_i         ( core_cntrl_if.fetch_en         ),
         .core_sleep_o           ( core_status_if.core_busy       )
        ); // cv32e20_wrapper_i
    */


endmodule : uvmt_cv32e20_dut_wrap

`endif // __UVMT_CV32E20_DUT_WRAP_SV__


