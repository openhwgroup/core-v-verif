//
// Copyright 2022 OpenHW Group
// Copyright 2022 Imperas
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


`ifndef __UVMT_CV32E40P_IMPERAS_DV_WRAP_SV__
`define __UVMT_CV32E40P_IMPERAS_DV_WRAP_SV__

`define DUT_PATH dut_wrap.cv32e40p_tb_wrapper_i
`define RVFI_IF  `DUT_PATH.rvfi_i

`define STRINGIFY(x) `"x`"

////////////////////////////////////////////////////////////////////////////
// Assign the rvvi CSR values from RVFI - CSR = (wdata & wmask) | (rdata & ~wmask)
////////////////////////////////////////////////////////////////////////////
`define RVVI_SET_CSR(CSR_ADDR, CSR_NAME) \
    bit csr_``CSR_NAME``_wb; \
    wire [31:0] csr_``CSR_NAME``_w; \
    wire [31:0] csr_``CSR_NAME``_r; \
    assign csr_``CSR_NAME``_w = `RVFI_IF.rvfi_csr_``CSR_NAME``_wdata &   `RVFI_IF.rvfi_csr_``CSR_NAME``_wmask; \
    assign csr_``CSR_NAME``_r = `RVFI_IF.rvfi_csr_``CSR_NAME``_rdata & ~(`RVFI_IF.rvfi_csr_``CSR_NAME``_wmask); \
    assign rvvi.csr[0][0][``CSR_ADDR]    = csr_``CSR_NAME``_w | csr_``CSR_NAME``_r; \
    assign rvvi.csr_wb[0][0][``CSR_ADDR] = csr_``CSR_NAME``_wb; \
    always @(rvvi.csr[0][0][``CSR_ADDR]) begin \
        csr_``CSR_NAME``_wb = 1; \
    end \
    always @(posedge rvvi.clk) begin \
        if (`RVFI_IF.rvfi_valid && csr_``CSR_NAME``_wb) begin \
            csr_``CSR_NAME``_wb = 0; \
        end \
    end

`define RVVI_SET_CSR_VEC(CSR_ADDR, CSR_NAME, CSR_ID) \
    bit csr_``CSR_NAME````CSR_ID``_wb; \
    wire [31:0] csr_``CSR_NAME````CSR_ID``_w; \
    wire [31:0] csr_``CSR_NAME````CSR_ID``_r; \
    assign csr_``CSR_NAME````CSR_ID``_w = `RVFI_IF.rvfi_csr_``CSR_NAME``_wdata[``CSR_ID] &   `RVFI_IF.rvfi_csr_``CSR_NAME``_wmask[``CSR_ID]; \
    assign csr_``CSR_NAME````CSR_ID``_r = `RVFI_IF.rvfi_csr_``CSR_NAME``_rdata[``CSR_ID] & ~(`RVFI_IF.rvfi_csr_``CSR_NAME``_wmask[``CSR_ID]); \
    assign rvvi.csr[0][0][``CSR_ADDR]    = csr_``CSR_NAME````CSR_ID``_w | csr_``CSR_NAME````CSR_ID``_r; \
    assign rvvi.csr_wb[0][0][``CSR_ADDR] = csr_``CSR_NAME````CSR_ID``_wb; \
    always @(rvvi.csr[0][0][``CSR_ADDR]) begin \
        csr_``CSR_NAME````CSR_ID``_wb = 1; \
    end \
    always @(posedge rvvi.clk) begin \
        if (`RVFI_IF.rvfi_valid && csr_``CSR_NAME````CSR_ID``_wb) begin \
            csr_``CSR_NAME````CSR_ID``_wb = 0; \
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
`define CSR_JVT_ADDR           32'h017
`define CSR_MSTATUS_ADDR       32'h300
`define CSR_MISA_ADDR          32'h301
`define CSR_MIE_ADDR           32'h304
`define CSR_MTVEC_ADDR         32'h305
`define CSR_MCOUNTEREN_ADDR    32'h306
`define CSR_MENVCFG_ADDR       32'h30A
`define CSR_MSTATEEN0_ADDR     32'h30C
`define CSR_MSTATEEN1_ADDR     32'h30D
`define CSR_MSTATEEN2_ADDR     32'h30E
`define CSR_MSTATEEN3_ADDR     32'h30F
`define CSR_MTVT_ADDR          32'h307 // only available when SMCLIC=1
`define CSR_MSTATUSH_ADDR      32'h310
`define CSR_MENVCFGH_ADDR      32'h31A
`define CSR_MSTATEEN0H_ADDR    32'h31C
`define CSR_MSTATEEN1H_ADDR    32'h31D
`define CSR_MSTATEEN2H_ADDR    32'h31E
`define CSR_MSTATEEN3H_ADDR    32'h31F
`define CSR_MCOUNTINHIBIT_ADDR 32'h320
`define CSR_MSCRATCH_ADDR      32'h340
`define CSR_MEPC_ADDR          32'h341
`define CSR_MCAUSE_ADDR        32'h342
`define CSR_MTVAL_ADDR         32'h343
`define CSR_MIP_ADDR           32'h344
`define CSR_MNXTI_ADDR         32'h345 // only available when SMCLIC=1
`define CSR_MINTSTATUS_ADDR    32'h346 // only available when SMCLIC=1
`define CSR_MINTTHRESH_ADDR    32'h347 // only available when SMCLIC=1
`define CSR_MSCRATCHCSW_ADDR   32'h348 // only available when SMCLIC=1
`define CSR_MCLICBASE_ADDR     32'h34A // only available when SMCLIC=1
`define CSR_MSECCFG            32'h747
`define CSR_MSECCFGH           32'h757

`define CSR_TSELECT_ADDR       32'h7A0 // only when DBG_NUM_TRIGGERS > 0
`define CSR_TDATA1_ADDR        32'h7A1 // only when DBG_NUM_TRIGGERS > 0
`define CSR_TDATA2_ADDR        32'h7A2 // only when DBG_NUM_TRIGGERS > 0
`define CSR_TDATA3_ADDR        32'h7A3 // only when DBG_NUM_TRIGGERS > 0
`define CSR_TINFO_ADDR         32'h7A4 // only when DBG_NUM_TRIGGERS > 0
`define CSR_TCONTROL_ADDR      32'h7A5 // only when DBG_NUM_TRIGGERS > 0
`define CSR_MCONTEXT_ADDR      32'h7A8
`define CSR_MSCONTEXT_ADDR     32'h7A9 // ???
`define CSR_SCONTEXT_ADDR      32'h7AA
`define CSR_DCSR_ADDR          32'h7B0
`define CSR_DPC_ADDR           32'h7B1
`define CSR_DSCRATCH0_ADDR     32'h7B2
`define CSR_DSCRATCH1_ADDR     32'h7B3
`define CSR_MCYCLE_ADDR        32'hB00
`define CSR_MINSTRET_ADDR      32'hB02

`define CSR_CYCLE_ADDR         32'hC00
`define CSR_INSTRET_ADDR       32'hC02
`define CSR_CYCLEH_ADDR        32'hC80
`define CSR_INSTRETH_ADDR      32'hC82

`define CSR_MHPMCOUNTER3_ADDR  32'hB03
`define CSR_MHPMCOUNTER4_ADDR  32'hB04
`define CSR_MHPMCOUNTER5_ADDR  32'hB05
`define CSR_MHPMCOUNTER6_ADDR  32'hB06
`define CSR_MHPMCOUNTER7_ADDR  32'hB07
`define CSR_MHPMCOUNTER8_ADDR  32'hB08
`define CSR_MHPMCOUNTER9_ADDR  32'hB09
`define CSR_MHPMCOUNTER10_ADDR 32'hB0A
`define CSR_MHPMCOUNTER11_ADDR 32'hB0B
`define CSR_MHPMCOUNTER12_ADDR 32'hB0C
`define CSR_MHPMCOUNTER13_ADDR 32'hB0D
`define CSR_MHPMCOUNTER14_ADDR 32'hB0E
`define CSR_MHPMCOUNTER15_ADDR 32'hB0F
`define CSR_MHPMCOUNTER16_ADDR 32'hB10
`define CSR_MHPMCOUNTER17_ADDR 32'hB11
`define CSR_MHPMCOUNTER18_ADDR 32'hB12
`define CSR_MHPMCOUNTER19_ADDR 32'hB13
`define CSR_MHPMCOUNTER20_ADDR 32'hB14
`define CSR_MHPMCOUNTER21_ADDR 32'hB15
`define CSR_MHPMCOUNTER22_ADDR 32'hB16
`define CSR_MHPMCOUNTER23_ADDR 32'hB17
`define CSR_MHPMCOUNTER24_ADDR 32'hB18
`define CSR_MHPMCOUNTER25_ADDR 32'hB19
`define CSR_MHPMCOUNTER26_ADDR 32'hB1A
`define CSR_MHPMCOUNTER27_ADDR 32'hB1B
`define CSR_MHPMCOUNTER28_ADDR 32'hB1C
`define CSR_MHPMCOUNTER29_ADDR 32'hB1D
`define CSR_MHPMCOUNTER30_ADDR 32'hB1E
`define CSR_MHPMCOUNTER31_ADDR 32'hB1F

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

`define CSR_MCYCLEH_ADDR        32'hB80
`define CSR_MINSTRETH_ADDR      32'hB82

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
// `define USE_ISS
`ifdef USE_ISS

`include "rvvi/imperasDV.svh" // located in $IMPERAS_HOME/ImpProprietary/include/host

module uvmt_cv32e40p_imperas_dv_wrap
  import uvm_pkg::*;
  import cv32e40p_pkg::*;
  import uvme_cv32e40p_pkg::*;
  import uvmt_cv32e40p_pkg::*;
  import rvviApiPkg::*;
  #(
    )

    (
        rvviTrace  rvvi // RVVI SystemVerilog Interface
    );

    trace2api #(
        .CMP_PC      (1),
        .CMP_INS     (1),
        .CMP_GPR     (1),
        .CMP_FPR     (0),
        .CMP_VR      (0),
        .CMP_CSR     (1)
    )
    trace2api(rvvi);

    trace2log       idv_trace2log(rvvi);
    trace2cov       idv_trace2cov(rvvi);

    string info_tag = "ImperasDV_wrap";

    ////////////////////////////////////////////////////////////////////////////
    // Adopted from:
    // ImperasDV/examples/openhwgroup_cv32e40x/systemverilog/cv32e40x_testbench.sv
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
    assign rvvi.clk            = `RVFI_IF.clk_i;
    assign rvvi.valid[0][0]    = `RVFI_IF.rvfi_valid;
    assign rvvi.order[0][0]    = `RVFI_IF.rvfi_order;
    assign rvvi.insn[0][0]     = `RVFI_IF.rvfi_insn;
    assign rvvi.trap[0][0]     = `RVFI_IF.rvfi_trap.trap;
    assign rvvi.intr[0][0]     = `RVFI_IF.rvfi_intr;
    assign rvvi.mode[0][0]     = `RVFI_IF.rvfi_mode;
    assign rvvi.ixl[0][0]      = `RVFI_IF.rvfi_ixl;
    assign rvvi.pc_rdata[0][0] = `RVFI_IF.rvfi_pc_rdata;
    //  assign rvvi.pc_wdata[0][0] = `RVFI_IF.rvfi_pc_wdata;

    `RVVI_SET_CSR( `CSR_MSTATUS_ADDR,       mstatus       )
    `RVVI_SET_CSR( `CSR_MISA_ADDR,          misa          )
    `RVVI_SET_CSR( `CSR_MIE_ADDR,           mie           )
    `RVVI_SET_CSR( `CSR_MTVEC_ADDR,         mtvec         )
    `RVVI_SET_CSR( `CSR_MCOUNTINHIBIT_ADDR, mcountinhibit )
    `RVVI_SET_CSR( `CSR_MSCRATCH_ADDR,      mscratch      )
    `RVVI_SET_CSR( `CSR_MEPC_ADDR,          mepc          )
    `RVVI_SET_CSR( `CSR_MCAUSE_ADDR,        mcause        )
    //  `RVVI_SET_CSR( `CSR_MTVAL_ADDR,         mtval         )
    `RVVI_SET_CSR( `CSR_MIP_ADDR,           mip           )
    //  `RVVI_SET_CSR( `CSR_MCYCLE_ADDR,        mcycle        )
    `RVVI_SET_CSR( `CSR_MINSTRET_ADDR,      minstret      )
    //  `RVVI_SET_CSR( `CSR_MCYCLEH_ADDR,       mcycleh       )
    //  `RVVI_SET_CSR( `CSR_MINSTRETH_ADDR,     minstreth     )
    `RVVI_SET_CSR( `CSR_MVENDORID_ADDR,     mvendorid     )
    `RVVI_SET_CSR( `CSR_MARCHID_ADDR,       marchid       )
    //  `RVVI_SET_CSR( `CSR_MIMPID_ADDR,        mimpid        )
    `RVVI_SET_CSR( `CSR_MHARTID_ADDR,       mhartid       )

    //  `RVVI_SET_CSR( `CSR_TSELECT_ADDR,       tselect       )
    `RVVI_SET_CSR( `CSR_DCSR_ADDR,          dcsr          )
    `RVVI_SET_CSR( `CSR_DPC_ADDR,           dpc           )
    `RVVI_SET_CSR_VEC(`CSR_DSCRATCH0_ADDR, dscratch, 0)
    `RVVI_SET_CSR_VEC(`CSR_DSCRATCH1_ADDR, dscratch, 1)
    `RVVI_SET_CSR_VEC(`CSR_TDATA1_ADDR, tdata, 1)
    `RVVI_SET_CSR_VEC(`CSR_TDATA2_ADDR, tdata, 2)
    `RVVI_SET_CSR( `CSR_TINFO_ADDR,         tinfo         )

    ////////////////////////////////////////////////////////////////////////////
    // Assign the RVVI GPR registers
    ////////////////////////////////////////////////////////////////////////////
    bit [31:0] XREG[32];
    genvar gi;
    generate
        for(gi=0; gi<32; gi++) begin
            assign rvvi.x_wdata[0][0][gi] = XREG[gi];
        end
    endgenerate

    always @(*) begin
        int i;
        for (i=1; i<32; i++) begin
            XREG[i] = 32'b0;
            // TODO: This current RVFI implementation will only allow a single destination
            //       register to be written. For some instructions this is not sufficient
            //       This code will need enhancing once the RVFI has the ability to describe
            //       multiple target register writes, for a single instruction
            if (`RVFI_IF.rvfi_rd_addr[0]==5'(i))
            XREG[i] = `RVFI_IF.rvfi_rd_wdata[0];
            if (`RVFI_IF.rvfi_rd_addr[1]==5'(i))
            XREG[i] = `RVFI_IF.rvfi_rd_wdata[1];
        end
    end

    assign rvvi.x_wb[0][0] = (1 << `RVFI_IF.rvfi_rd_addr[0] | 1 << `RVFI_IF.rvfi_rd_addr[1]); // TODO: originally rvfi_rd_addr

    ////////////////////////////////////////////////////////////////////////////
    // DEBUG REQUESTS,
    ////////////////////////////////////////////////////////////////////////////
    logic debug_req_i;
    assign debug_req_i = `DUT_PATH.debug_req_i;
    always @(debug_req_i) begin
        void'(rvvi.net_push("haltreq", debug_req_i));
    end

    ////////////////////////////////////////////////////////////////////////////
    // INTERRUPTS
    // assert when MIP or cause bit
    // negate when posedge clk && valid=1 && debug=0
    ////////////////////////////////////////////////////////////////////////////
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

    /////////////////////////////////////////////////////////////////////////////
    // REF control
    /////////////////////////////////////////////////////////////////////////////
    task ref_init;
    string test_program_elf;
    reg [31:0] hart_id;

    // Select processor name
    void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_NAME, "CV32E40P"));
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
        `uvm_info(info_tag, $sformatf("ImperasDV loading test_program %0s", test_program_elf), UVM_NONE)
        void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_VENDOR,  "openhwgroup.ovpworld.org"));
        void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_NAME,    "CVE4P"));
        void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_VARIANT, "CV32E40P"));
        if (!rvviRefInit(test_program_elf)) begin
            `uvm_fatal(info_tag, "rvviRefInit failed")
        end
        else begin
            `uvm_info(info_tag, "rvviRefInit() succeed", UVM_NONE)
        end
    end
    else begin
        `uvm_fatal(info_tag, "No test_program specified")
    end

    hart_id = 32'h0000_0000;

    void'(rvviRefCsrSetVolatile(hart_id, `CSR_CYCLE_ADDR        ));

    void'(rvviRefCsrSetVolatile(hart_id, `CSR_INSTRET_ADDR      ));

    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MCYCLE_ADDR       ));

    // cannot predict this register due to latency between
    // pending and taken
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MIP_ADDR          ));
    void'(rvviRefCsrSetVolatileMask(hart_id, `CSR_DCSR_ADDR, 'h8));

    // TODO silabs-hfegran: temp fix to work around issues
    rvviRefCsrCompareEnable(hart_id, `CSR_DCSR_ADDR,   RVVI_FALSE);
    // end TODO
    // define asynchronous grouping
    // Interrupts
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

    rvviRefNetGroupSet(rvviRefNetIndexGet("InstructionBusFault"), 2);

    // Debug
    rvviRefNetGroupSet(rvviRefNetIndexGet("haltreq"),             4);

    void'(rvviRefMemorySetVolatile('h15001000, 'h15001007)); //TODO: deal with int return value
  endtask // ref_init
endmodule : uvmt_cv32e40p_imperas_dv_wrap
`endif  // USE_ISS

`endif // __UVMT_CV32E40P_IMPERAS_DV_WRAP_SV__