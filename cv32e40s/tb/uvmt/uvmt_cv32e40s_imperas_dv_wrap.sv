//
// Copyright 2022 OpenHW Group
// Copyright 2023 Imperas
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
//


`ifndef __UVMT_CV32E40S_IMPERAS_DV_WRAP_SV__
`define __UVMT_CV32E40S_IMPERAS_DV_WRAP_SV__

`define DUT_PATH dut_wrap.cv32e40s_wrapper_i
`define RVFI_IF  `DUT_PATH.rvfi_instr_if

`define STRINGIFY(x) `"x`"

////////////////////////////////////////////////////////////////////////////
// Assign the rvvi CSR values from RVFI - CSR = (wdata & wmask) | (rdata & ~wmask)
////////////////////////////////////////////////////////////////////////////
`define RVVI_SET_CSR(CSR_ADDR, CSR_NAME) \
    bit csr_``CSR_NAME``_wb; \
    wire [31:0] csr_``CSR_NAME``_w; \
    wire [31:0] csr_``CSR_NAME``_r; \
    assign csr_``CSR_NAME``_w = `DUT_PATH.rvfi_csr_``CSR_NAME``_if.rvfi_csr_wdata &   `DUT_PATH.rvfi_csr_``CSR_NAME``_if.rvfi_csr_wmask; \
    assign csr_``CSR_NAME``_r = `DUT_PATH.rvfi_csr_``CSR_NAME``_if.rvfi_csr_rdata & ~(`DUT_PATH.rvfi_csr_``CSR_NAME``_if.rvfi_csr_wmask); \
    assign rvvi.csr[0][0][``CSR_ADDR]    = csr_``CSR_NAME``_w | csr_``CSR_NAME``_r; \
    assign rvvi.csr_wb[0][0][``CSR_ADDR] = csr_``CSR_NAME``_wb; \
    always @(rvvi.csr[0][0][``CSR_ADDR]) begin \
      if ((`DUT_PATH.rvfi_csr_``CSR_NAME``_if.rvfi_csr_rmask || `DUT_PATH.rvfi_csr_``CSR_NAME``_if.rvfi_csr_wmask) && `RVFI_IF.rvfi_valid) begin \
        csr_``CSR_NAME``_wb = 1; \
      end \
    end \
    always @(posedge rvvi.clk) begin \
        if (`RVFI_IF.rvfi_valid && csr_``CSR_NAME``_wb) begin \
            csr_``CSR_NAME``_wb = 0; \
        end \
    end

////////////////////////////////////////////////////////////////////////////
// Assign the NET IRQ values from the core irq inputs
////////////////////////////////////////////////////////////////////////////
`define RVVI_WRITE_IRQ(IRQ_NAME, IRQ_IDX) \
    wire   irq_``IRQ_NAME; \
    assign irq_``IRQ_NAME = `DUT_PATH.irq_i[IRQ_IDX]; \
    always @(irq_``IRQ_NAME) begin \
        void'(rvvi.net_push(`STRINGIFY(``IRQ_NAME), irq_``IRQ_NAME)); \
    end

////////////////////////////////////////////////////////////////////////////
// CSR definitions
////////////////////////////////////////////////////////////////////////////
`define CSR_JVT_ADDR            32'h017
`define CSR_MSTATUS_ADDR        32'h300
`define CSR_MISA_ADDR           32'h301
`define CSR_MIE_ADDR            32'h304
`define CSR_MTVEC_ADDR          32'h305
`define CSR_MCOUNTEREN_ADDR     32'h306
`define CSR_MENVCFG_ADDR        32'h30A
`define CSR_MSTATEEN0_ADDR      32'h30C
`define CSR_MSTATEEN1_ADDR      32'h30D
`define CSR_MSTATEEN2_ADDR      32'h30E
`define CSR_MSTATEEN3_ADDR      32'h30F
`define CSR_MTVT_ADDR           32'h307 // only available when CLIC=1
`define CSR_MSTATUSH_ADDR       32'h310
`define CSR_MENVCFGH_ADDR       32'h31A
`define CSR_MSTATEEN0H_ADDR     32'h31C
`define CSR_MSTATEEN1H_ADDR     32'h31D
`define CSR_MSTATEEN2H_ADDR     32'h31E
`define CSR_MSTATEEN3H_ADDR     32'h31F
`define CSR_MCOUNTINHIBIT_ADDR  32'h320

`define CSR_MHPMEVENT3_ADDR     32'h323
`define CSR_MHPMEVENT4_ADDR     32'h324
`define CSR_MHPMEVENT5_ADDR     32'h325
`define CSR_MHPMEVENT6_ADDR     32'h326
`define CSR_MHPMEVENT7_ADDR     32'h327
`define CSR_MHPMEVENT8_ADDR     32'h328
`define CSR_MHPMEVENT9_ADDR     32'h329
`define CSR_MHPMEVENT10_ADDR    32'h32A
`define CSR_MHPMEVENT11_ADDR    32'h32B
`define CSR_MHPMEVENT12_ADDR    32'h32C
`define CSR_MHPMEVENT13_ADDR    32'h32D
`define CSR_MHPMEVENT14_ADDR    32'h32E
`define CSR_MHPMEVENT15_ADDR    32'h32F
`define CSR_MHPMEVENT16_ADDR    32'h330
`define CSR_MHPMEVENT17_ADDR    32'h331
`define CSR_MHPMEVENT18_ADDR    32'h332
`define CSR_MHPMEVENT19_ADDR    32'h333
`define CSR_MHPMEVENT20_ADDR    32'h334
`define CSR_MHPMEVENT21_ADDR    32'h335
`define CSR_MHPMEVENT22_ADDR    32'h336
`define CSR_MHPMEVENT23_ADDR    32'h337
`define CSR_MHPMEVENT24_ADDR    32'h338
`define CSR_MHPMEVENT25_ADDR    32'h339
`define CSR_MHPMEVENT26_ADDR    32'h33A
`define CSR_MHPMEVENT27_ADDR    32'h33B
`define CSR_MHPMEVENT28_ADDR    32'h33C
`define CSR_MHPMEVENT29_ADDR    32'h33D
`define CSR_MHPMEVENT30_ADDR    32'h33E
`define CSR_MHPMEVENT31_ADDR    32'h33F

`define CSR_MSCRATCH_ADDR       32'h340
`define CSR_MEPC_ADDR           32'h341
`define CSR_MCAUSE_ADDR         32'h342
`define CSR_MTVAL_ADDR          32'h343
`define CSR_MIP_ADDR            32'h344
`define CSR_MNXTI_ADDR          32'h345 // only available when CLIC=1
`define CSR_MINTSTATUS_ADDR     32'hFB1 // only available when CLIC=1
`define CSR_MINTTHRESH_ADDR     32'h347 // only available when CLIC=1
`define CSR_MSCRATCHCSW_ADDR    32'h348 // only available when CLIC=1
`define CSR_MSCRATCHCSWL_ADDR   32'h349 // only available when CLIC=1
`define CSR_MCLICBASE_ADDR      32'h34A // only available when CLIC=1

`define CSR_PMPCFG0_ADDR        32'h3A0
`define CSR_PMPCFG1_ADDR        32'h3A1
`define CSR_PMPCFG2_ADDR        32'h3A2
`define CSR_PMPCFG3_ADDR        32'h3A3
`define CSR_PMPCFG4_ADDR        32'h3A4
`define CSR_PMPCFG5_ADDR        32'h3A5
`define CSR_PMPCFG6_ADDR        32'h3A6
`define CSR_PMPCFG7_ADDR        32'h3A7
`define CSR_PMPCFG8_ADDR        32'h3A8
`define CSR_PMPCFG9_ADDR        32'h3A9
`define CSR_PMPCFG10_ADDR       32'h3AA
`define CSR_PMPCFG11_ADDR       32'h3AB
`define CSR_PMPCFG12_ADDR       32'h3AC
`define CSR_PMPCFG13_ADDR       32'h3AD
`define CSR_PMPCFG14_ADDR       32'h3AE
`define CSR_PMPCFG15_ADDR       32'h3AF

`define CSR_PMPADDR0_ADDR       32'h3B0
`define CSR_PMPADDR1_ADDR       32'h3B1
`define CSR_PMPADDR2_ADDR       32'h3B2
`define CSR_PMPADDR3_ADDR       32'h3B3
`define CSR_PMPADDR4_ADDR       32'h3B4
`define CSR_PMPADDR5_ADDR       32'h3B5
`define CSR_PMPADDR6_ADDR       32'h3B6
`define CSR_PMPADDR7_ADDR       32'h3B7
`define CSR_PMPADDR8_ADDR       32'h3B8
`define CSR_PMPADDR9_ADDR       32'h3B9
`define CSR_PMPADDR10_ADDR      32'h3BA
`define CSR_PMPADDR11_ADDR      32'h3BB
`define CSR_PMPADDR12_ADDR      32'h3BC
`define CSR_PMPADDR13_ADDR      32'h3BD
`define CSR_PMPADDR14_ADDR      32'h3BE
`define CSR_PMPADDR15_ADDR      32'h3BF
`define CSR_PMPADDR16_ADDR      32'h3C0
`define CSR_PMPADDR17_ADDR      32'h3C1
`define CSR_PMPADDR18_ADDR      32'h3C2
`define CSR_PMPADDR19_ADDR      32'h3C3
`define CSR_PMPADDR20_ADDR      32'h3C4
`define CSR_PMPADDR21_ADDR      32'h3C5
`define CSR_PMPADDR22_ADDR      32'h3C6
`define CSR_PMPADDR23_ADDR      32'h3C7
`define CSR_PMPADDR24_ADDR      32'h3C8
`define CSR_PMPADDR25_ADDR      32'h3C9
`define CSR_PMPADDR26_ADDR      32'h3CA
`define CSR_PMPADDR27_ADDR      32'h3CB
`define CSR_PMPADDR28_ADDR      32'h3CC
`define CSR_PMPADDR29_ADDR      32'h3CD
`define CSR_PMPADDR30_ADDR      32'h3CE
`define CSR_PMPADDR31_ADDR      32'h3CF
`define CSR_PMPADDR32_ADDR      32'h3D0
`define CSR_PMPADDR33_ADDR      32'h3D1
`define CSR_PMPADDR34_ADDR      32'h3D2
`define CSR_PMPADDR35_ADDR      32'h3D3
`define CSR_PMPADDR36_ADDR      32'h3D4
`define CSR_PMPADDR37_ADDR      32'h3D5
`define CSR_PMPADDR38_ADDR      32'h3D6
`define CSR_PMPADDR39_ADDR      32'h3D7
`define CSR_PMPADDR40_ADDR      32'h3D8
`define CSR_PMPADDR41_ADDR      32'h3D9
`define CSR_PMPADDR42_ADDR      32'h3DA
`define CSR_PMPADDR43_ADDR      32'h3DB
`define CSR_PMPADDR44_ADDR      32'h3DC
`define CSR_PMPADDR45_ADDR      32'h3DD
`define CSR_PMPADDR46_ADDR      32'h3DE
`define CSR_PMPADDR47_ADDR      32'h3DF
`define CSR_PMPADDR48_ADDR      32'h3E0
`define CSR_PMPADDR49_ADDR      32'h3E1
`define CSR_PMPADDR50_ADDR      32'h3E2
`define CSR_PMPADDR51_ADDR      32'h3E3
`define CSR_PMPADDR52_ADDR      32'h3E4
`define CSR_PMPADDR53_ADDR      32'h3E5
`define CSR_PMPADDR54_ADDR      32'h3E6
`define CSR_PMPADDR55_ADDR      32'h3E7
`define CSR_PMPADDR56_ADDR      32'h3E8
`define CSR_PMPADDR57_ADDR      32'h3E9
`define CSR_PMPADDR58_ADDR      32'h3EA
`define CSR_PMPADDR59_ADDR      32'h3EB
`define CSR_PMPADDR60_ADDR      32'h3EC
`define CSR_PMPADDR61_ADDR      32'h3ED
`define CSR_PMPADDR62_ADDR      32'h3EE
`define CSR_PMPADDR63_ADDR      32'h3EF

`define CSR_MSECCFG_ADDR        32'h747
`define CSR_MSECCFGH_ADDR       32'h757

`define CSR_TSELECT_ADDR        32'h7A0 // only when DBG_NUM_TRIGGERS > 0
`define CSR_TDATA1_ADDR         32'h7A1 // only when DBG_NUM_TRIGGERS > 0
`define CSR_TDATA2_ADDR         32'h7A2 // only when DBG_NUM_TRIGGERS > 0
`define CSR_TINFO_ADDR          32'h7A4 // only when DBG_NUM_TRIGGERS > 0

`define CSR_DCSR_ADDR           32'h7B0
`define CSR_DPC_ADDR            32'h7B1
`define CSR_DSCRATCH0_ADDR      32'h7B2
`define CSR_DSCRATCH1_ADDR      32'h7B3

`define CSR_MCYCLE_ADDR         32'hB00
`define CSR_MINSTRET_ADDR       32'hB02

`define CSR_MHPMCOUNTER3_ADDR   32'hB03
`define CSR_MHPMCOUNTER4_ADDR   32'hB04
`define CSR_MHPMCOUNTER5_ADDR   32'hB05
`define CSR_MHPMCOUNTER6_ADDR   32'hB06
`define CSR_MHPMCOUNTER7_ADDR   32'hB07
`define CSR_MHPMCOUNTER8_ADDR   32'hB08
`define CSR_MHPMCOUNTER9_ADDR   32'hB09
`define CSR_MHPMCOUNTER10_ADDR  32'hB0A
`define CSR_MHPMCOUNTER11_ADDR  32'hB0B
`define CSR_MHPMCOUNTER12_ADDR  32'hB0C
`define CSR_MHPMCOUNTER13_ADDR  32'hB0D
`define CSR_MHPMCOUNTER14_ADDR  32'hB0E
`define CSR_MHPMCOUNTER15_ADDR  32'hB0F
`define CSR_MHPMCOUNTER16_ADDR  32'hB10
`define CSR_MHPMCOUNTER17_ADDR  32'hB11
`define CSR_MHPMCOUNTER18_ADDR  32'hB12
`define CSR_MHPMCOUNTER19_ADDR  32'hB13
`define CSR_MHPMCOUNTER20_ADDR  32'hB14
`define CSR_MHPMCOUNTER21_ADDR  32'hB15
`define CSR_MHPMCOUNTER22_ADDR  32'hB16
`define CSR_MHPMCOUNTER23_ADDR  32'hB17
`define CSR_MHPMCOUNTER24_ADDR  32'hB18
`define CSR_MHPMCOUNTER25_ADDR  32'hB19
`define CSR_MHPMCOUNTER26_ADDR  32'hB1A
`define CSR_MHPMCOUNTER27_ADDR  32'hB1B
`define CSR_MHPMCOUNTER28_ADDR  32'hB1C
`define CSR_MHPMCOUNTER29_ADDR  32'hB1D
`define CSR_MHPMCOUNTER30_ADDR  32'hB1E
`define CSR_MHPMCOUNTER31_ADDR  32'hB1F

`define CSR_MCYCLEH_ADDR        32'hB80
`define CSR_MINSTRETH_ADDR      32'hB82

`define CSR_MHPMCOUNTER3H_ADDR  32'hB83
`define CSR_MHPMCOUNTER4H_ADDR  32'hB84
`define CSR_MHPMCOUNTER5H_ADDR  32'hB85
`define CSR_MHPMCOUNTER6H_ADDR  32'hB86
`define CSR_MHPMCOUNTER7H_ADDR  32'hB87
`define CSR_MHPMCOUNTER8H_ADDR  32'hB88
`define CSR_MHPMCOUNTER9H_ADDR  32'hB89
`define CSR_MHPMCOUNTER10H_ADDR 32'hB8A
`define CSR_MHPMCOUNTER11H_ADDR 32'hB8B
`define CSR_MHPMCOUNTER12H_ADDR 32'hB8C
`define CSR_MHPMCOUNTER13H_ADDR 32'hB8D
`define CSR_MHPMCOUNTER14H_ADDR 32'hB8E
`define CSR_MHPMCOUNTER15H_ADDR 32'hB8F
`define CSR_MHPMCOUNTER16H_ADDR 32'hB90
`define CSR_MHPMCOUNTER17H_ADDR 32'hB91
`define CSR_MHPMCOUNTER18H_ADDR 32'hB92
`define CSR_MHPMCOUNTER19H_ADDR 32'hB93
`define CSR_MHPMCOUNTER20H_ADDR 32'hB94
`define CSR_MHPMCOUNTER21H_ADDR 32'hB95
`define CSR_MHPMCOUNTER22H_ADDR 32'hB96
`define CSR_MHPMCOUNTER23H_ADDR 32'hB97
`define CSR_MHPMCOUNTER24H_ADDR 32'hB98
`define CSR_MHPMCOUNTER25H_ADDR 32'hB99
`define CSR_MHPMCOUNTER26H_ADDR 32'hB9A
`define CSR_MHPMCOUNTER27H_ADDR 32'hB9B
`define CSR_MHPMCOUNTER28H_ADDR 32'hB9C
`define CSR_MHPMCOUNTER29H_ADDR 32'hB9D
`define CSR_MHPMCOUNTER30H_ADDR 32'hB9E
`define CSR_MHPMCOUNTER31H_ADDR 32'hB9F

`define CSR_CPUCTRL_ADDR        32'hBF0
`define CSR_SECURESEED0_ADDR    32'hBF9
`define CSR_SECURESEED1_ADDR    32'hBFA
`define CSR_SECURESEED2_ADDR    32'hBFC

`define CSR_MVENDORID_ADDR      32'hF11
`define CSR_MARCHID_ADDR        32'hF12
`define CSR_MIMPID_ADDR         32'hF13
`define CSR_MHARTID_ADDR        32'hF14
`define CSR_MCONFIGPTR_ADDR     32'hF15

///////////////////////////////////////////////////////////////////////////////
// Module wrapper for Imperas DV.
////////////////////////////////////////////////////////////////////////////
`ifdef USE_IMPERASDV

`include "idv/idv.svh" // located in $IMPERAS_HOME/ImpProprietary/include/host

module uvmt_cv32e40s_imperas_dv_wrap
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  import uvme_cv32e40s_pkg::*;
  import rvviApiPkg::*;
  #(
   )

   (
           rvviTrace rvvi // RVVI SystemVerilog Interface
   );

   trace2api       #(.CMP_PC      (1),
                   .CMP_INS     (1),
                   .CMP_GPR     (1),
                   .CMP_FPR     (0),
                   .CMP_VR      (0),
                   .CMP_CSR     (1)
                   )
                   idv_trace2api(rvvi);

   trace2log       idv_trace2log(rvvi);

   trace2cov       idv_trace2cov(rvvi);

   string info_tag = "ImperasDV_wrap";

   // Make the UVM environment configuration available to the Reference Model as needed.
   uvme_cv32e40s_cfg_c  uvm_env_cfg;

   initial begin
     @(rvvi.clk);
     void'(uvm_config_db#(uvme_cv32e40s_cfg_c)::get(null, "uvm_test_top.env", "cfg", uvm_env_cfg));
     if (!uvm_env_cfg) begin
      `uvm_fatal(info_tag, "Configuration handle is null")
     end
     else begin
      `uvm_info(info_tag, $sformatf("Found UVM environment configuration handle:\n%s", uvm_env_cfg.sprint()), UVM_DEBUG)
     end
   end

   ////////////////////////////////////////////////////////////////////////////
   // Adopted from:
   // ImperasDV/examples/openhwgroup_cv32e40s/systemverilog/cv32e40s_testbench.sv
   //
   // InstrunctionBusFault(48) is in fact a TRAP which is derived externally
   // This is strange as other program TRAPS are derived by the model, for now
   // We have to ensure we do not step the REF model for this TRAP as it will
   // Step too far. So instead we block it as being VALID, but pass on the
   // signals.
   // maybe we need a different way to communicate this to the model, for
   // instance the ability to register a callback on fetch, in order to assert
   // this signal.
   ////////////////////////////////////////////////////////////////////////////
   assign rvvi.clk            = `RVFI_IF.clk;
   assign rvvi.valid[0][0]    = `RVFI_IF.rvfi_valid;
   assign rvvi.order[0][0]    = `RVFI_IF.rvfi_order;
   assign rvvi.insn[0][0]     = `RVFI_IF.rvfi_insn;
   assign rvvi.trap[0][0]     =  (`RVFI_IF.rvfi_trap.trap && `RVFI_IF.rvfi_trap.exception == 1'b1)                                      || // Exceptions never retire
                                 (`RVFI_IF.rvfi_trap.trap && `RVFI_IF.rvfi_trap.debug == 1'b1 && `RVFI_IF.rvfi_trap.debug_cause == 'h1) || // Ebreak never retires
                                 (`RVFI_IF.rvfi_trap.trap && `RVFI_IF.rvfi_trap.debug == 1'b1 && `RVFI_IF.rvfi_trap.debug_cause == 'h2);   // Trigger match never retires
   assign rvvi.intr[0][0]     = `RVFI_IF.rvfi_intr;
   assign rvvi.mode[0][0]     = `RVFI_IF.rvfi_mode;
   assign rvvi.ixl[0][0]      = `RVFI_IF.rvfi_ixl;
   assign rvvi.pc_rdata[0][0] = `RVFI_IF.rvfi_pc_rdata;
   assign rvvi.pc_wdata[0][0] = `RVFI_IF.rvfi_pc_wdata;

   `RVVI_SET_CSR( `CSR_JVT_ADDR,           jvt           )
   `RVVI_SET_CSR( `CSR_MSTATUS_ADDR,       mstatus       )
   `RVVI_SET_CSR( `CSR_MISA_ADDR,          misa          )
   `RVVI_SET_CSR( `CSR_MIE_ADDR,           mie           )
   `RVVI_SET_CSR( `CSR_MTVEC_ADDR,         mtvec         )
   `RVVI_SET_CSR( `CSR_MCOUNTEREN_ADDR,    mcounteren    )
   `RVVI_SET_CSR( `CSR_MENVCFG_ADDR,       menvcfg       )
   `RVVI_SET_CSR( `CSR_MSTATEEN0_ADDR,     mstateen0     )
   `RVVI_SET_CSR( `CSR_MSTATEEN1_ADDR,     mstateen1     )
   `RVVI_SET_CSR( `CSR_MSTATEEN2_ADDR,     mstateen2     )
   `RVVI_SET_CSR( `CSR_MSTATEEN3_ADDR,     mstateen3     )

   `RVVI_SET_CSR( `CSR_MSTATUSH_ADDR,      mstatush      )
   `RVVI_SET_CSR( `CSR_MENVCFGH_ADDR,      menvcfgh      )
   `RVVI_SET_CSR( `CSR_MSTATEEN0H_ADDR,    mstateen0h    )
   `RVVI_SET_CSR( `CSR_MSTATEEN1H_ADDR,    mstateen1h    )
   `RVVI_SET_CSR( `CSR_MSTATEEN2H_ADDR,    mstateen2h    )
   `RVVI_SET_CSR( `CSR_MSTATEEN3H_ADDR,    mstateen3h    )
   `RVVI_SET_CSR( `CSR_MCOUNTINHIBIT_ADDR, mcountinhibit )

   `RVVI_SET_CSR( `CSR_MHPMEVENT3_ADDR,    mhpmevent3    )
   `RVVI_SET_CSR( `CSR_MHPMEVENT4_ADDR,    mhpmevent4    )
   `RVVI_SET_CSR( `CSR_MHPMEVENT5_ADDR,    mhpmevent5    )
   `RVVI_SET_CSR( `CSR_MHPMEVENT6_ADDR,    mhpmevent6    )
   `RVVI_SET_CSR( `CSR_MHPMEVENT7_ADDR,    mhpmevent7    )
   `RVVI_SET_CSR( `CSR_MHPMEVENT8_ADDR,    mhpmevent8    )
   `RVVI_SET_CSR( `CSR_MHPMEVENT9_ADDR,    mhpmevent9    )
   `RVVI_SET_CSR( `CSR_MHPMEVENT10_ADDR,   mhpmevent10   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT11_ADDR,   mhpmevent11   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT12_ADDR,   mhpmevent12   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT13_ADDR,   mhpmevent13   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT14_ADDR,   mhpmevent14   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT15_ADDR,   mhpmevent15   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT16_ADDR,   mhpmevent16   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT17_ADDR,   mhpmevent17   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT18_ADDR,   mhpmevent18   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT19_ADDR,   mhpmevent19   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT20_ADDR,   mhpmevent20   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT21_ADDR,   mhpmevent21   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT22_ADDR,   mhpmevent22   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT23_ADDR,   mhpmevent23   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT24_ADDR,   mhpmevent24   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT25_ADDR,   mhpmevent25   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT26_ADDR,   mhpmevent26   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT27_ADDR,   mhpmevent27   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT28_ADDR,   mhpmevent28   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT29_ADDR,   mhpmevent29   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT30_ADDR,   mhpmevent30   )
   `RVVI_SET_CSR( `CSR_MHPMEVENT31_ADDR,   mhpmevent31   )

   `RVVI_SET_CSR( `CSR_MSCRATCH_ADDR,      mscratch      )
   `RVVI_SET_CSR( `CSR_MEPC_ADDR,          mepc          )
   `RVVI_SET_CSR( `CSR_MCAUSE_ADDR,        mcause        )
   `RVVI_SET_CSR( `CSR_MTVAL_ADDR,         mtval         )
   `RVVI_SET_CSR( `CSR_MIP_ADDR,           mip           )

   `RVVI_SET_CSR( `CSR_PMPCFG0_ADDR,       pmpcfg0       )
   `RVVI_SET_CSR( `CSR_PMPCFG1_ADDR,       pmpcfg1       )
   `RVVI_SET_CSR( `CSR_PMPCFG2_ADDR,       pmpcfg2       )
   `RVVI_SET_CSR( `CSR_PMPCFG3_ADDR,       pmpcfg3       )
   `RVVI_SET_CSR( `CSR_PMPCFG4_ADDR,       pmpcfg4       )
   `RVVI_SET_CSR( `CSR_PMPCFG5_ADDR,       pmpcfg5       )
   `RVVI_SET_CSR( `CSR_PMPCFG6_ADDR,       pmpcfg6       )
   `RVVI_SET_CSR( `CSR_PMPCFG7_ADDR,       pmpcfg7       )
   `RVVI_SET_CSR( `CSR_PMPCFG8_ADDR,       pmpcfg8       )
   `RVVI_SET_CSR( `CSR_PMPCFG9_ADDR,       pmpcfg9       )
   `RVVI_SET_CSR( `CSR_PMPCFG10_ADDR,      pmpcfg10      )
   `RVVI_SET_CSR( `CSR_PMPCFG11_ADDR,      pmpcfg11      )
   `RVVI_SET_CSR( `CSR_PMPCFG12_ADDR,      pmpcfg12      )
   `RVVI_SET_CSR( `CSR_PMPCFG13_ADDR,      pmpcfg13      )
   `RVVI_SET_CSR( `CSR_PMPCFG14_ADDR,      pmpcfg14      )
   `RVVI_SET_CSR( `CSR_PMPCFG15_ADDR,      pmpcfg15      )

   `RVVI_SET_CSR( `CSR_PMPADDR0_ADDR,      pmpaddr0      )
   `RVVI_SET_CSR( `CSR_PMPADDR1_ADDR,      pmpaddr1      )
   `RVVI_SET_CSR( `CSR_PMPADDR2_ADDR,      pmpaddr2      )
   `RVVI_SET_CSR( `CSR_PMPADDR3_ADDR,      pmpaddr3      )
   `RVVI_SET_CSR( `CSR_PMPADDR4_ADDR,      pmpaddr4      )
   `RVVI_SET_CSR( `CSR_PMPADDR5_ADDR,      pmpaddr5      )
   `RVVI_SET_CSR( `CSR_PMPADDR6_ADDR,      pmpaddr6      )
   `RVVI_SET_CSR( `CSR_PMPADDR7_ADDR,      pmpaddr7      )
   `RVVI_SET_CSR( `CSR_PMPADDR8_ADDR,      pmpaddr8      )
   `RVVI_SET_CSR( `CSR_PMPADDR9_ADDR,      pmpaddr9      )
   `RVVI_SET_CSR( `CSR_PMPADDR10_ADDR,     pmpaddr10     )
   `RVVI_SET_CSR( `CSR_PMPADDR11_ADDR,     pmpaddr11     )
   `RVVI_SET_CSR( `CSR_PMPADDR12_ADDR,     pmpaddr12     )
   `RVVI_SET_CSR( `CSR_PMPADDR13_ADDR,     pmpaddr13     )
   `RVVI_SET_CSR( `CSR_PMPADDR14_ADDR,     pmpaddr14     )
   `RVVI_SET_CSR( `CSR_PMPADDR15_ADDR,     pmpaddr15     )
   `RVVI_SET_CSR( `CSR_PMPADDR16_ADDR,     pmpaddr16     )
   `RVVI_SET_CSR( `CSR_PMPADDR17_ADDR,     pmpaddr17     )
   `RVVI_SET_CSR( `CSR_PMPADDR18_ADDR,     pmpaddr18     )
   `RVVI_SET_CSR( `CSR_PMPADDR19_ADDR,     pmpaddr19     )
   `RVVI_SET_CSR( `CSR_PMPADDR20_ADDR,     pmpaddr20     )
   `RVVI_SET_CSR( `CSR_PMPADDR21_ADDR,     pmpaddr21     )
   `RVVI_SET_CSR( `CSR_PMPADDR22_ADDR,     pmpaddr22     )
   `RVVI_SET_CSR( `CSR_PMPADDR23_ADDR,     pmpaddr23     )
   `RVVI_SET_CSR( `CSR_PMPADDR24_ADDR,     pmpaddr24     )
   `RVVI_SET_CSR( `CSR_PMPADDR25_ADDR,     pmpaddr25     )
   `RVVI_SET_CSR( `CSR_PMPADDR26_ADDR,     pmpaddr26     )
   `RVVI_SET_CSR( `CSR_PMPADDR27_ADDR,     pmpaddr27     )
   `RVVI_SET_CSR( `CSR_PMPADDR28_ADDR,     pmpaddr28     )
   `RVVI_SET_CSR( `CSR_PMPADDR29_ADDR,     pmpaddr29     )
   `RVVI_SET_CSR( `CSR_PMPADDR30_ADDR,     pmpaddr30     )
   `RVVI_SET_CSR( `CSR_PMPADDR31_ADDR,     pmpaddr31     )
   `RVVI_SET_CSR( `CSR_PMPADDR32_ADDR,     pmpaddr32     )
   `RVVI_SET_CSR( `CSR_PMPADDR33_ADDR,     pmpaddr33     )
   `RVVI_SET_CSR( `CSR_PMPADDR34_ADDR,     pmpaddr34     )
   `RVVI_SET_CSR( `CSR_PMPADDR35_ADDR,     pmpaddr35     )
   `RVVI_SET_CSR( `CSR_PMPADDR36_ADDR,     pmpaddr36     )
   `RVVI_SET_CSR( `CSR_PMPADDR37_ADDR,     pmpaddr37     )
   `RVVI_SET_CSR( `CSR_PMPADDR38_ADDR,     pmpaddr38     )
   `RVVI_SET_CSR( `CSR_PMPADDR39_ADDR,     pmpaddr39     )
   `RVVI_SET_CSR( `CSR_PMPADDR40_ADDR,     pmpaddr40     )
   `RVVI_SET_CSR( `CSR_PMPADDR41_ADDR,     pmpaddr41     )
   `RVVI_SET_CSR( `CSR_PMPADDR42_ADDR,     pmpaddr42     )
   `RVVI_SET_CSR( `CSR_PMPADDR43_ADDR,     pmpaddr43     )
   `RVVI_SET_CSR( `CSR_PMPADDR44_ADDR,     pmpaddr44     )
   `RVVI_SET_CSR( `CSR_PMPADDR45_ADDR,     pmpaddr45     )
   `RVVI_SET_CSR( `CSR_PMPADDR46_ADDR,     pmpaddr46     )
   `RVVI_SET_CSR( `CSR_PMPADDR47_ADDR,     pmpaddr47     )
   `RVVI_SET_CSR( `CSR_PMPADDR48_ADDR,     pmpaddr48     )
   `RVVI_SET_CSR( `CSR_PMPADDR49_ADDR,     pmpaddr49     )
   `RVVI_SET_CSR( `CSR_PMPADDR50_ADDR,     pmpaddr50     )
   `RVVI_SET_CSR( `CSR_PMPADDR51_ADDR,     pmpaddr51     )
   `RVVI_SET_CSR( `CSR_PMPADDR52_ADDR,     pmpaddr52     )
   `RVVI_SET_CSR( `CSR_PMPADDR53_ADDR,     pmpaddr53     )
   `RVVI_SET_CSR( `CSR_PMPADDR54_ADDR,     pmpaddr54     )
   `RVVI_SET_CSR( `CSR_PMPADDR55_ADDR,     pmpaddr55     )
   `RVVI_SET_CSR( `CSR_PMPADDR56_ADDR,     pmpaddr56     )
   `RVVI_SET_CSR( `CSR_PMPADDR57_ADDR,     pmpaddr57     )
   `RVVI_SET_CSR( `CSR_PMPADDR58_ADDR,     pmpaddr58     )
   `RVVI_SET_CSR( `CSR_PMPADDR59_ADDR,     pmpaddr59     )
   `RVVI_SET_CSR( `CSR_PMPADDR60_ADDR,     pmpaddr60     )
   `RVVI_SET_CSR( `CSR_PMPADDR61_ADDR,     pmpaddr61     )
   `RVVI_SET_CSR( `CSR_PMPADDR62_ADDR,     pmpaddr62     )
   `RVVI_SET_CSR( `CSR_PMPADDR63_ADDR,     pmpaddr63     )

   `RVVI_SET_CSR( `CSR_MSECCFG_ADDR,       mseccfg       )
   `RVVI_SET_CSR( `CSR_MSECCFGH_ADDR,      mseccfgh      )

   if (CORE_PARAM_DBG_NUM_TRIGGERS > 0) begin
     `RVVI_SET_CSR( `CSR_TSELECT_ADDR,       tselect       )
     `RVVI_SET_CSR( `CSR_TDATA1_ADDR,        tdata1        )
     `RVVI_SET_CSR( `CSR_TDATA2_ADDR,        tdata2        )
     `RVVI_SET_CSR( `CSR_TINFO_ADDR,         tinfo         )
   end

   `RVVI_SET_CSR( `CSR_DCSR_ADDR,          dcsr          )
   `RVVI_SET_CSR( `CSR_DPC_ADDR,           dpc           )
   `RVVI_SET_CSR( `CSR_DSCRATCH0_ADDR,     dscratch0     )
   `RVVI_SET_CSR( `CSR_DSCRATCH1_ADDR,     dscratch1     )

   `RVVI_SET_CSR( `CSR_MHPMCOUNTER3_ADDR, mhpmcounter3   )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER4_ADDR, mhpmcounter4   )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER5_ADDR, mhpmcounter5   )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER6_ADDR, mhpmcounter6   )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER7_ADDR, mhpmcounter7   )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER8_ADDR, mhpmcounter8   )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER9_ADDR, mhpmcounter9   )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER10_ADDR, mhpmcounter10 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER11_ADDR, mhpmcounter11 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER12_ADDR, mhpmcounter12 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER13_ADDR, mhpmcounter13 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER14_ADDR, mhpmcounter14 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER15_ADDR, mhpmcounter15 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER16_ADDR, mhpmcounter16 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER17_ADDR, mhpmcounter17 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER18_ADDR, mhpmcounter18 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER19_ADDR, mhpmcounter19 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER20_ADDR, mhpmcounter20 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER21_ADDR, mhpmcounter21 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER22_ADDR, mhpmcounter22 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER23_ADDR, mhpmcounter23 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER24_ADDR, mhpmcounter24 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER25_ADDR, mhpmcounter25 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER26_ADDR, mhpmcounter26 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER27_ADDR, mhpmcounter27 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER28_ADDR, mhpmcounter28 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER29_ADDR, mhpmcounter29 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER30_ADDR, mhpmcounter30 )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER31_ADDR, mhpmcounter31 )

   `RVVI_SET_CSR( `CSR_MCYCLE_ADDR,        mcycle        )
   `RVVI_SET_CSR( `CSR_MINSTRET_ADDR,      minstret      )

   `RVVI_SET_CSR( `CSR_MHPMCOUNTER3H_ADDR, mhpmcounter3h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER4H_ADDR, mhpmcounter4h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER5H_ADDR, mhpmcounter5h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER6H_ADDR, mhpmcounter6h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER7H_ADDR, mhpmcounter7h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER8H_ADDR, mhpmcounter8h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER9H_ADDR, mhpmcounter9h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER10H_ADDR,mhpmcounter10h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER11H_ADDR,mhpmcounter11h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER12H_ADDR,mhpmcounter12h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER13H_ADDR,mhpmcounter13h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER14H_ADDR,mhpmcounter14h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER15H_ADDR,mhpmcounter15h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER16H_ADDR,mhpmcounter16h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER17H_ADDR,mhpmcounter17h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER18H_ADDR,mhpmcounter18h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER19H_ADDR,mhpmcounter19h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER20H_ADDR,mhpmcounter20h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER21H_ADDR,mhpmcounter21h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER22H_ADDR,mhpmcounter22h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER23H_ADDR,mhpmcounter23h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER24H_ADDR,mhpmcounter24h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER25H_ADDR,mhpmcounter25h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER26H_ADDR,mhpmcounter26h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER27H_ADDR,mhpmcounter27h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER28H_ADDR,mhpmcounter28h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER29H_ADDR,mhpmcounter29h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER30H_ADDR,mhpmcounter30h )
   `RVVI_SET_CSR( `CSR_MHPMCOUNTER31H_ADDR,mhpmcounter31h )

   `RVVI_SET_CSR( `CSR_CPUCTRL_ADDR,       cpuctrl       )
   `RVVI_SET_CSR( `CSR_SECURESEED0_ADDR,   secureseed0   )
   `RVVI_SET_CSR( `CSR_SECURESEED1_ADDR,   secureseed1   )
   `RVVI_SET_CSR( `CSR_SECURESEED2_ADDR,   secureseed2   )

   `RVVI_SET_CSR( `CSR_MVENDORID_ADDR,     mvendorid     )
   `RVVI_SET_CSR( `CSR_MARCHID_ADDR,       marchid       )
   `RVVI_SET_CSR( `CSR_MIMPID_ADDR,        mimpid        )
   `RVVI_SET_CSR( `CSR_MHARTID_ADDR,       mhartid       )
   `RVVI_SET_CSR( `CSR_MCONFIGPTR_ADDR,    mconfigptr    )

   `RVVI_SET_CSR( `CSR_MCYCLEH_ADDR,       mcycleh       )
   `RVVI_SET_CSR( `CSR_MINSTRETH_ADDR,     minstreth     )

   if (CORE_PARAM_CLIC == 1) begin
     `RVVI_SET_CSR( `CSR_MTVT_ADDR,        mtvt          )
     `RVVI_SET_CSR( `CSR_MNXTI_ADDR,       mnxti         )
     `RVVI_SET_CSR( `CSR_MINTSTATUS_ADDR,  mintstatus    )
     `RVVI_SET_CSR( `CSR_MINTTHRESH_ADDR,  mintthresh    )
     `RVVI_SET_CSR( `CSR_MSCRATCHCSW_ADDR, mscratchcsw   )
     `RVVI_SET_CSR( `CSR_MSCRATCHCSWL_ADDR,mscratchcswl  )
   end


   ////////////////////////////////////////////////////////////////////////////
   // Assign the RVVI GPR registers
   ////////////////////////////////////////////////////////////////////////////
   bit [31:0] XREG[32];
   genvar gi;
   generate
       for(gi=0; gi<32; gi++)
           assign rvvi.x_wdata[0][0][gi] = XREG[gi];
   endgenerate

   always_comb begin
     int i;
     if (|`RVFI_IF.rvfi_gpr_wmask[31:1] && `RVFI_IF.rvfi_valid) begin
       for (i=1; i<32; i++) begin
         if (`RVFI_IF.rvfi_gpr_wmask[i]) begin
           XREG[i] = `RVFI_IF.rvfi_gpr_wdata[i*XLEN+:XLEN];
         end
         else begin
           XREG[i] = 32'h0;
         end
       end
     end
   end

   assign rvvi.x_wb[0][0] = `RVFI_IF.rvfi_gpr_wmask;

   ////////////////////////////////////////////////////////////////////////////
   // RESET
   ////////////////////////////////////////////////////////////////////////////
   always @`DUT_PATH.rst_ni begin
       void'(rvvi.net_push("reset", !`DUT_PATH.rst_ni));
   end

   ////////////////////////////////////////////////////////////////////////////
   // DEBUG REQUESTS,
   ////////////////////////////////////////////////////////////////////////////
   logic debug_req_i;
   assign debug_req_i = `DUT_PATH.debug_req_i;
   always @(debug_req_i) begin
       void'(rvvi.net_push("haltreq", debug_req_i));
   end

   ////////////////////////////////////////////////////////////////////////////
   // WFE REQUESTS
   ////////////////////////////////////////////////////////////////////////////
   logic wu_wfe_i;
   assign wu_wfe_i = `DUT_PATH.wu_wfe_i;
   always @(wu_wfe_i) begin
     void'(rvvi.net_push("wu_wfe_i", wu_wfe_i));
   end

   ////////////////////////////////////////////////////////////////////////////
   // INTERRUPTS
   ////////////////////////////////////////////////////////////////////////////
  if (CORE_PARAM_CLIC == 0) begin
    `RVVI_WRITE_IRQ(MSWInterrupt,        3)
    `RVVI_WRITE_IRQ(MTimerInterrupt,     7)
    `RVVI_WRITE_IRQ(MExternalInterrupt, 11)
    `RVVI_WRITE_IRQ(LocalInterrupt0,    16)
    `RVVI_WRITE_IRQ(LocalInterrupt1,    17)
    `RVVI_WRITE_IRQ(LocalInterrupt2,    18)
    `RVVI_WRITE_IRQ(LocalInterrupt3,    19)
    `RVVI_WRITE_IRQ(LocalInterrupt4,    20)
    `RVVI_WRITE_IRQ(LocalInterrupt5,    21)
    `RVVI_WRITE_IRQ(LocalInterrupt6,    22)
    `RVVI_WRITE_IRQ(LocalInterrupt7,    23)
    `RVVI_WRITE_IRQ(LocalInterrupt8,    24)
    `RVVI_WRITE_IRQ(LocalInterrupt9,    25)
    `RVVI_WRITE_IRQ(LocalInterrupt10,   26)
    `RVVI_WRITE_IRQ(LocalInterrupt11,   27)
    `RVVI_WRITE_IRQ(LocalInterrupt12,   28)
    `RVVI_WRITE_IRQ(LocalInterrupt13,   29)
    `RVVI_WRITE_IRQ(LocalInterrupt14,   30)
    `RVVI_WRITE_IRQ(LocalInterrupt15,   31)
  end else begin
    logic clic_irq;
    logic [10:0] clic_irq_id;
    logic [7:0]  clic_irq_level;
    logic [1:0]  clic_irq_priv;
    logic        clic_irq_shv;

    assign clic_irq       = `DUT_PATH.clic_irq_i;
    assign clic_irq_id    = `DUT_PATH.clic_irq_id_i;
    assign clic_irq_level = `DUT_PATH.clic_irq_level_i;
    assign clic_irq_priv  = `DUT_PATH.clic_irq_priv_i;
    assign clic_irq_shv   = `DUT_PATH.clic_irq_shv_i;
    always @(clic_irq, clic_irq_id, clic_irq_level, clic_irq_priv, clic_irq_shv) begin
      void'(rvvi.net_push("irq_i",       clic_irq));
      void'(rvvi.net_push("irq_id_i",    clic_irq_id));
      void'(rvvi.net_push("irq_lev_i",   clic_irq_level));
      void'(rvvi.net_push("irq_sec_i",   clic_irq_priv));
      void'(rvvi.net_push("irq_shv_i",   clic_irq_shv));
    end
  end

   ////////////////////////////////////////////////////////////////////////////
   // RVFI Monitor: pass NMI Load/Store and Fetch to the ref
   ////////////////////////////////////////////////////////////////////////////
   bit InstructionBusFault;
   bit DataBusFault;
   int DataBusFaultCause;
   int order;

   always_comb begin: Monitor_RVFI
       bit        trap_trap;
       bit        trap_exception;
       bit        trap_debug;
       bit [5:0]  trap_exception_cause;
       bit [2:0]  trap_debug_cause;
       bit [1:0]  trap_cause_type;

       bit        intr_intr;
       bit        intr_exception;
       bit        intr_interrupt;
       bit [10:0] intr_cause;

       bit        nmi_pending;
       bit        nmi_load_store;

       bit        nmi_c1, nmi_c2;

       bit        ifault;

       if (`RVFI_IF.rvfi_valid && (order != `RVFI_IF.rvfi_order)) begin
           order                = `RVFI_IF.rvfi_order;

           trap_trap            = `RVFI_IF.rvfi_trap.trap;
           trap_exception       = `RVFI_IF.rvfi_trap.exception;
           trap_debug           = `RVFI_IF.rvfi_trap.debug;
           trap_exception_cause = `RVFI_IF.rvfi_trap.exception_cause;
           trap_debug_cause     = `RVFI_IF.rvfi_trap.debug_cause;
           trap_cause_type      = `RVFI_IF.rvfi_trap.cause_type;

           intr_intr            = `RVFI_IF.rvfi_intr.intr;
           intr_exception       = `RVFI_IF.rvfi_intr.exception;
           intr_interrupt       = `RVFI_IF.rvfi_intr.interrupt;
           intr_cause           = `RVFI_IF.rvfi_intr.cause;

           nmi_pending          = `RVFI_IF.rvfi_nmip[0];
           nmi_load_store       = `RVFI_IF.rvfi_nmip[1];

           // Only in debug Mode
           `uvm_info(info_tag, $sformatf("RVFI Valid %t", $time), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("valid      = %X", `RVFI_IF.rvfi_valid), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("order      = %0d", `RVFI_IF.rvfi_order), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("insn       = %X", `RVFI_IF.rvfi_insn), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("trap       trap=%X exception=%X debug=%X exception_cause=0x%X debug_cause=0x%X cause_type=0x%X",
                 trap_trap, trap_exception, trap_debug, trap_exception_cause, trap_debug_cause, trap_cause_type), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("halt       = %X", `RVFI_IF.rvfi_halt), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("dbg        = %X", `RVFI_IF.rvfi_dbg), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("dbg_mode   = %X", `RVFI_IF.rvfi_dbg_mode), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("nmip       nmi=%X nmi_load0_store1=%X", `RVFI_IF.rvfi_nmip[0], `RVFI_IF.rvfi_nmip[1]), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("intr       intr=%X exception=%X interrupt=%X cause=0x%X",
                 intr_intr, intr_exception, intr_interrupt, intr_cause), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("mode       = %X", `RVFI_IF.rvfi_mode), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("ixl        = %X", `RVFI_IF.rvfi_ixl), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("pc_rdata   = %X", `RVFI_IF.rvfi_pc_rdata), UVM_DEBUG)
           `uvm_info(info_tag, $sformatf("pc_wdata   = %X", `RVFI_IF.rvfi_pc_wdata), UVM_DEBUG)

           //
           // Load Store - NMI
           //
           nmi_c1 = (intr_intr && intr_interrupt && ((intr_cause==1024 || intr_cause==1025)));
           nmi_c2 = nmi_pending;

           if (nmi_c1 || nmi_c2) begin
               // Load / Store
               if (DataBusFaultCause != intr_cause) begin
                   void'(rvvi.net_push("nmi_cause", intr_cause)); // Load Error = 1024, Store Error = 1025
               end
               if (!DataBusFault) begin
                   void'(rvvi.net_push("nmi", 1));
               end
               DataBusFault = 1;
               DataBusFaultCause = intr_cause;
           end else begin
               if (DataBusFault) begin
                   void'(rvvi.net_push("nmi", 0));
               end
               DataBusFault = 0;
           end

           //
           //  Fetch - Exception on TRAP
           //
           if (trap_trap && trap_exception && trap_exception_cause==24) begin
               if (!InstructionBusFault) begin
                   void'(rvvi.net_push("InstructionBusFault", 1));
               end
               InstructionBusFault = 1;
           end else begin
               if (InstructionBusFault) begin
                   void'(rvvi.net_push("InstructionBusFault", 0));
               end
               InstructionBusFault = 0;
           end

       end
   end: Monitor_RVFI

endmodule : uvmt_cv32e40s_imperas_dv_wrap

interface uvmt_imperas_dv_if_t;
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  import uvme_cv32e40s_pkg::*;
  import rvviApiPkg::*;

  string info_tag = "ImperasDV_if";

  task ref_init;
    string test_program_elf;
    logic [31:0] hart_id;

    // Select processor name
    void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_NAME, "CVE4S"));
    // Worst case propagation of events 4 retirements (actually 3 observed)
    void'(rvviRefConfigSetInt(IDV_CONFIG_MAX_NET_LATENCY_RETIREMENTS, 4));
    // Redirect stdout to parent systemverilog simulator
    void'(rvviRefConfigSetInt(IDV_CONFIG_REDIRECT_STDOUT, RVVI_TRUE));

    // Initialize REF and load the test-program into it's memory (do this before initializing the DUT).
    // TODO: is this the best place for this?
    if (!rvviVersionCheck(RVVI_API_VERSION)) begin
      `uvm_fatal(info_tag, $sformatf("Expecting RVVI API version %0d.", RVVI_API_VERSION))
    end
    // Test-program must have been compiled before we got here...
    if ($value$plusargs("elf_file=%s", test_program_elf)) begin
      `uvm_info(info_tag, $sformatf("ImperasDV loading test_program %0s", test_program_elf), UVM_LOW)
      void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_VENDOR,  "openhwgroup.ovpworld.org"));
      void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_VARIANT, "CV32E40S_DEV"));
      if (!rvviRefInit(test_program_elf)) begin
        `uvm_fatal(info_tag, "rvviRefInit failed")
      end
      else begin
        `uvm_info(info_tag, "rvviRefInit() succeed", UVM_LOW)
      end
    end
    else begin
      `uvm_fatal(info_tag, "No test_program specified")
    end

    hart_id = 32'h0000_0000;

    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MCYCLE_ADDR       ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MCYCLEH_ADDR      ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MINSTRET_ADDR     ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MINSTRETH_ADDR    ));

    // cannot predict this register due to latency between
    // pending and taken
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MIP_ADDR          ));

    // TODO: deal with the MHPMCOUNTER CSRs properly.
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER3_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER3H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT3_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER4_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER4H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT4_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER5_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER5H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT5_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER6_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER6H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT6_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER7_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER7H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT7_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER8_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER8H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT8_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER9_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER9H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT9_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER10_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER10H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT10_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER11_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER11H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT11_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER12_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER12H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT12_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER13_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER13H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT13_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER14_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER14H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT14_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER15_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER15H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT15_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER16_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER16H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT16_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER17_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER17H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT17_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER18_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER18H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT18_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER19_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER19H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT19_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER20_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER20H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT20_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER21_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER21H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT21_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER22_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER22H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT22_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER23_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER23H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT23_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER24_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER24H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT24_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER25_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER25H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT25_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER26_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER26H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT26_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER27_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER27H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT27_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER28_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER28H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT28_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER29_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER29H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT29_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER30_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER30H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT30_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER31_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER31H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id,   `CSR_MHPMEVENT31_ADDR ));

    // Mask out pending bits, due to interrupts showing as pending
    // and enabled but not taken immediately due to instructions
    // in-flight, eg Load/Store
    rvviRefCsrCompareEnable(hart_id, `CSR_MIP_ADDR, RVVI_FALSE);
    void'(rvviRefCsrSetVolatileMask(hart_id, `CSR_DCSR_ADDR, 'h8));

    // TODO: Set these as volatiles as a temporary fix until
    // we have a proper fix implemented in the ISS
    if (CORE_PARAM_CLIC == 1) begin
      void'(rvviRefCsrSetVolatile(hart_id, `CSR_MNXTI_ADDR));
      void'(rvviRefCsrSetVolatile(hart_id, `CSR_MSCRATCHCSW_ADDR));
      void'(rvviRefCsrSetVolatile(hart_id, `CSR_MSCRATCHCSWL_ADDR));
    end

    // define asynchronous grouping
    // Interrupts
    if (CORE_PARAM_CLIC == 0) begin
      rvviRefNetGroupSet(rvviRefNetIndexGet("MSWInterrupt"),        1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("MTimerInterrupt"),     1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("MExternalInterrupt"),  1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt0"),     1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt1"),     1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt2"),     1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt3"),     1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt4"),     1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt5"),     1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt6"),     1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt7"),     1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt8"),     1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt9"),     1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt10"),    1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt11"),    1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt12"),    1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt13"),    1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt14"),    1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("LocalInterrupt15"),    1);
    end else begin
      rvviRefNetGroupSet(rvviRefNetIndexGet("irq_i"),               1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("irq_id_i"),            1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("irq_lev_i"),           1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("irq_sec_i"),           1);
      rvviRefNetGroupSet(rvviRefNetIndexGet("irq_shv_i"),           1);
    end

    rvviRefNetGroupSet(rvviRefNetIndexGet("InstructionBusFault"), 2);

    // NMI
    rvviRefNetGroupSet(rvviRefNetIndexGet("nmi"),                 3);
    rvviRefNetGroupSet(rvviRefNetIndexGet("nmi_cause"),           3);

    // Debug
    rvviRefNetGroupSet(rvviRefNetIndexGet("haltreq"),             4);

    // Add IO regions of memory
    // According to silabs this range is 0x0080_0000 to 0x0080_0FFF
    void'(rvviRefMemorySetVolatile('h00800000, 'h00800FFF)); //TODO: deal with int return value

    `uvm_info(info_tag, "ref_init() complete", UVM_LOW)
  endtask // ref_init
endinterface : uvmt_imperas_dv_if_t

`endif  // USE_IMPERASDV

`endif // __UVMT_CV32E40S_IMPERAS_DV_WRAP_SV__

