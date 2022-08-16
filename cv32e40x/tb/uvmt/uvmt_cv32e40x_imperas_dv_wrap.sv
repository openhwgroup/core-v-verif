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

`ifndef __UVMT_CV32E40X_IMPERAS_DV_WRAP_SV__
`define __UVMT_CV32E40X_IMPERAS_DV_WRAP_SV__

`define DUT_PATH dut_wrap.cv32e40x_wrapper_i
`define RVFI_IF  `DUT_PATH.rvfi_instr_if_0_i

`define STRINGIFY(x) `"x`"

// CSR = (wdata & wmask) | (rdata & ~wmask & rmask)
`define VLG2API_CSR_SET(CSR_ADDR, CSR_NAME) \
    bit csr_``CSR_NAME``_wb; \
    wire [31:0] csr_``CSR_NAME``_w; \
    wire [31:0] csr_``CSR_NAME``_r; \
    assign csr_``CSR_NAME``_w = `DUT_PATH.rvfi_csr_``CSR_NAME``_if_0_i.rvfi_csr_wdata &   `DUT_PATH.rvfi_csr_``CSR_NAME``_if_0_i.rvfi_csr_wmask; \
    assign csr_``CSR_NAME``_r = `DUT_PATH.rvfi_csr_``CSR_NAME``_if_0_i.rvfi_csr_rdata & ~(`DUT_PATH.rvfi_csr_``CSR_NAME``_if_0_i.rvfi_csr_wmask) & `DUT_PATH.rvfi_csr_``CSR_NAME``_if_0_i.rvfi_csr_rmask; \
    assign rvvi.csr[0][0][``CSR_ADDR]    = csr_``CSR_NAME``_w | csr_``CSR_NAME``_r; \
    assign rvvi.csr_wb[0][0][``CSR_ADDR] = csr_``CSR_NAME``_wb; \
    always @(rvvi.csr[0][0][``CSR_ADDR]) begin \
        csr_``CSR_NAME``_wb = 1; \
        if (0) $display("CSR RD %0s val=%08X mask=%08X", `STRINGIFY(``CSR_NAME), `DUT_PATH.rvfi_csr_``CSR_NAME``_if_0_i.rvfi_csr_rdata,  `DUT_PATH.rvfi_csr_``CSR_NAME``_if_0_i.rvfi_csr_rmask); \
    end \
    always @(posedge rvvi.clk) begin \
        if (`RVFI_IF.rvfi_valid && csr_``CSR_NAME``_wb) begin \
            csr_``CSR_NAME``_wb = 0; \
        end \
    end 

// CSR definitions
// TODO: this information should already be available in a similar form elsewhere.
`define CSR_MSTATUS_ADDR       32'h300
`define CSR_MISA_ADDR          32'h301
`define CSR_MIE_ADDR           32'h304
`define CSR_MTVEC_ADDR         32'h305
`define CSR_MTVT_ADDR          32'h307 // only available when SMCLIC=1
`define CSR_MSTATUSH_ADDR      32'h310
`define CSR_MCOUNTINHIBIT_ADDR 32'h320
//[31:0] [31:0]  CSR_MHPMEVENT 32'h323..32'h33F
`define CSR_MSCRATCH_ADDR      32'h340
`define CSR_MEPC_ADDR          32'h341
`define CSR_MCAUSE_ADDR        32'h342
`define CSR_MTVAL_ADDR         32'h343
`define CSR_MIP_ADDR           32'h344
`define CSR_MNXTI_ADDR         32'h345 // only available when SMCLIC=1
`define CSR_MINTSTATUS_ADDR    32'h346 // only available when SMCLIC=1
`define CSR_MINTTHRESH_ADDR    32'h347 // only available when SMCLIC=1
`define CSR_MSCRATCHCSW_ADDR   32'h348 // only available when SMCLIC=1
`define CSR_MSCRATCHCSW1_ADDR  32'h349 // only available when SMCLIC=1
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
`define CSR_DPC_ADDR           32'h7B0
`define CSR_MCYCLE_ADDR        32'hB00
`define CSR_MINSTRET_ADDR      32'hB02

//[31:0] [31:0]  CSR_MHPMCOUNTER_ADDR 32'hB03..32'hB1F
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

`define CSR_MHPMCOUNTER3H_ADDR 32'hB83

`define CSR_MHPMEVENT3_ADDR    32'h323

`define CSR_MCYCLEH_ADDR       32'hB80
`define CSR_MINSTRETH_ADDR     32'hB82
//[31:0] [31:0]  CSR_MHPMCOUNTERH_ADDR 32'hB83..32'hB9F
`define CSR_MVENDORID_ADDR     32'hF11
`define CSR_MARCHID_ADDR       32'hF12
`define CSR_MIMPID_ADDR        32'hF13
`define CSR_MHARTID_ADDR       32'hF14
`define CSR_MCONFIGPTR_ADDR    32'hF15 // huh?
`define CSR_CYCLE_ADDR         32'hC00
`define CSR_INSTRET_ADDR       32'hC02
`define CSR_CYCLEH_ADDR        32'hC80
`define CSR_INSTRETH_ADDR      32'hC82

`define CSR_DCSR_ADDR          32'h7B0
`define CSR_DEPC_ADDR          32'h7B1
`define CSR_DSCRATCH0_ADDR     32'h7B2
`define CSR_DSCRATCH1_ADDR     32'h7B3

//[31:0]         CSR_MSECCFG_ADDR
//[31:0]         CSR_MSECCFGH_ADDR
//[15:0] [31:0]  CSR_PMPADDR_ADDR
//[ 3:0] [31:0]  CSR_PMPCFG_ADDR
//[31:0] [31:0]  CSR_HPMCOUNTERH_ADDR
//[31:0] [31:0]  CSR_HPMCOUNTER_ADDR
//[ 1:0] [31:0]  CSR_DSCRATCH_ADDR
//[ 3:0] [31:0]  CSR_TDATA_ADDR


///////////////////////////////////////////////////////////////////////////////
// Module wrapper for Imperas DV.

module uvmt_cv32e40x_imperas_dv_wrap
  import uvm_pkg::*;
  import uvme_cv32e40x_pkg::*;
  #(
   )

   (
    RVVI_VLG  rvvi // RVVI SystemVerilog Interface
   );

   VLG2API       #(.CMP_PC      (1),
                   .CMP_INS     (1),
                   .CMP_GPR     (1),
                   .CMP_FPR     (0),
                   .CMP_VR      (0),
                   .CMP_CSR     (1)
                   //.MISCOMPARES (1)
                 )
                 vlg2api(rvvi);

   VLG2LOG       vlg2log(rvvi);

   string info_tag = "ImperasDV_wrap";

   // Make the UVM environment configuration available to the Reference Model as needed.
   uvme_cv32e40x_cfg_c  uvm_env_cfg;

   initial begin
     @(rvvi.clk);
     void'(uvm_config_db#(uvme_cv32e40x_cfg_c)::get(null, "uvm_test_top.env", "cfg", uvm_env_cfg));
     if (!uvm_env_cfg) begin
      `uvm_fatal(info_tag, "Configuration handle is null")
     end
     else begin
      `uvm_info(info_tag, $sformatf("Found UVM environment configuration handle:\n%s", uvm_env_cfg.sprint()), UVM_DEBUG)
     end
   end

   ////////////////////////////////////////////////////////////////////////////
   // Adopted from:
   // ImperasDV/examples/openhwgroup_cv32e40x/systemverilog/cv32e40x_testbench.sv

   // TODO: do a proper job of binding this in
   assign rvvi.clk            = `RVFI_IF.clk;
   assign rvvi.valid[0][0]    = `RVFI_IF.rvfi_valid;
   assign rvvi.order[0][0]    = `RVFI_IF.rvfi_order;
   assign rvvi.insn[0][0]     = `RVFI_IF.rvfi_insn;
   assign rvvi.trap[0][0]     = `RVFI_IF.rvfi_trap;
   assign rvvi.intr[0][0]     = `RVFI_IF.rvfi_intr;
   assign rvvi.mode[0][0]     = `RVFI_IF.rvfi_mode;
   assign rvvi.ixl[0][0]      = `RVFI_IF.rvfi_ixl;
   assign rvvi.pc_rdata[0][0] = `RVFI_IF.rvfi_pc_rdata;
   assign rvvi.pc_wdata[0][0] = `RVFI_IF.rvfi_pc_wdata;

   `VLG2API_CSR_SET( `CSR_MSTATUS_ADDR,       mstatus       )
   `VLG2API_CSR_SET( `CSR_MISA_ADDR,          misa          )
   `VLG2API_CSR_SET( `CSR_MIE_ADDR,           mie           )
   `VLG2API_CSR_SET( `CSR_MTVEC_ADDR,         mtvec         )
   `VLG2API_CSR_SET( `CSR_MCOUNTINHIBIT_ADDR, mcountinhibit )
   `VLG2API_CSR_SET( `CSR_MSCRATCH_ADDR,      mscratch      )
   `VLG2API_CSR_SET( `CSR_MEPC_ADDR,          mepc          )
   `VLG2API_CSR_SET( `CSR_MCAUSE_ADDR,        mcause        )
   `VLG2API_CSR_SET( `CSR_MTVAL_ADDR,         mtval         )
   `VLG2API_CSR_SET( `CSR_MIP_ADDR,           mip           )
   `VLG2API_CSR_SET( `CSR_TSELECT_ADDR,       tselect       )
   `VLG2API_CSR_SET( `CSR_TINFO_ADDR,         tinfo         )
   `VLG2API_CSR_SET( `CSR_DCSR_ADDR,          dcsr          )
   `VLG2API_CSR_SET( `CSR_DPC_ADDR,           dpc           )
   `VLG2API_CSR_SET( `CSR_MCYCLE_ADDR,        mcycle        )
   `VLG2API_CSR_SET( `CSR_MINSTRET_ADDR,      minstret      )
   `VLG2API_CSR_SET( `CSR_MCYCLEH_ADDR,       mcycleh       )
   `VLG2API_CSR_SET( `CSR_MINSTRETH_ADDR,     minstreth     )
//   `VLG2API_CSR_SET( `CSR_CYCLE_ADDR,         cycle         )
//   `VLG2API_CSR_SET( `CSR_INSTRET_ADDR,       minstret      )
//   `VLG2API_CSR_SET( `CSR_CYCLEH_ADDR,        mcycleh       )
//   `VLG2API_CSR_SET( `CSR_INSTRETH_ADDR,      instreth      )
//   `VLG2API_CSR_SET( `CSR_MVENDORID_ADDR,     mvendorid     )
   `VLG2API_CSR_SET( `CSR_MARCHID_ADDR,       marchid       )
   `VLG2API_CSR_SET( `CSR_MIMPID_ADDR,        mimpid        )
   `VLG2API_CSR_SET( `CSR_MHARTID_ADDR,       mhartid       )

   bit [31:0] XREG[32];
   genvar gi;
   generate
       for(gi=0; gi<32; gi++)
           assign rvvi.x_wdata[0][0][gi] = XREG[gi];
   endgenerate

   always @(*) begin
       int i;

       for (i=1; i<32; i++) begin
           XREG[i] = 32'b0;
           if (`RVFI_IF.rvfi_rd1_addr==5'(i))            // TODO: originally rvfi_rd_addr
               XREG[i] = `RVFI_IF.rvfi_rd1_wdata;        // TODO: originally rvfi_rd_wdata
       end
   end

   assign rvvi.x_wb[0][0] = 1 << `RVFI_IF.rvfi_rd1_addr; // TODO: originally rvfi_rd_addr

   ////////////////////////////////////////////////////////////////////////////
   // DEBUG REQUESTS: pass to the reference.
   //                 Include some paranoid checks as well.
   // seems the halt has to be held high for N calls to simulator
   always @(posedge rvvi.clk) begin: pass_debug_req_to_ref
     static int pulse = 0;
     if (`DUT_PATH.debug_req_i) begin
       pulse = 5;
       void'(rvvi.net_push("haltreq", `DUT_PATH.debug_req_i));
       `uvm_info(info_tag, $sformatf("%t order=%0d haltreq=%08x pulse=%0d", 
           $time, `RVFI_IF.rvfi_order, `DUT_PATH.debug_req_i, pulse), UVM_DEBUG)
     end else begin
       if (pulse > 0) begin
         pulse--;
         if (pulse==0) void'(rvvi.net_push("haltreq", `DUT_PATH.debug_req_i));
           `uvm_info(info_tag, $sformatf("%t order=%0d haltreq=%08x pulse=%0d", 
               $time, `RVFI_IF.rvfi_order, `DUT_PATH.debug_req_i, pulse), UVM_DEBUG)
       end
     end
   end: pass_debug_req_to_ref

   ////////////////////////////////////////////////////////////////////////////
   // Non-Maskable INTERRUPTS
   bit ldstQ[$];
   int NMI_cause;
   always @(posedge rvvi.clk) begin: pass_nmi_to_ref
     bit nmi;
     bit ldst;
     NMI_cause = 0;

     if (`DUT_PATH.data_rvalid_i) begin
       `uvm_info(info_tag, $sformatf("%t %m Q size=%0d", $time, ldstQ.size()), UVM_DEBUG);
       if (ldstQ.size() > 0) begin
         ldst = ldstQ.pop_back();
         `uvm_info(info_tag, $sformatf("%t %m POP ldst=%0d", $time, ldst), UVM_DEBUG);
         if (ldst) begin
           NMI_cause = 1025; // Store
         end else begin
           NMI_cause = 1024; // Load
         end
       end else begin
         // Error attempting to pop a value when list is empty
         `uvm_info(info_tag, $sformatf("ERROR!!! pop Q empty"), UVM_DEBUG);
       end
     end

     // for each Load/Store push request into queue
     // for each valid pop from queue
     if (`DUT_PATH.data_req_o && `DUT_PATH.data_gnt_i) begin
       // push into queue
       `uvm_info(info_tag, $sformatf("%t %m PUSH ldst=%0d", $time, `DUT_PATH.data_we_o), UVM_DEBUG);
       ldstQ.push_front(`DUT_PATH.data_we_o);
     end

     if (`DUT_PATH.data_err_i && `DUT_PATH.data_rvalid_i) begin
       `uvm_info(info_tag, $sformatf("%t SET nmi - cause=%0d %0s", $time, NMI_cause, (ldst ? "Load" : "Store")), UVM_DEBUG);
       nmi = 1;
       // Need some decode logic
       void'(rvvi.net_push("nmi_cause", NMI_cause)); // Load/Store Error 
       void'(rvvi.net_push("nmi", 1));
     end else if (nmi) begin
       `uvm_info(info_tag, $sformatf("%t CLR nmi", $time), UVM_DEBUG);
       nmi = 0;
       void'(rvvi.net_push("nmi", 0));
     end
   end: pass_nmi_to_ref

//   always @(posedge rvvi.clk) begin: pass_nmi_to_ref
//      // `RVFI_IF.insn_nmi = 0;
//      if (`RVFI_IF.intr.intr && `RVFI_IF.valid) begin
//         // NMI detected
//         if ((cfg.nmi_load_fault_enabled && `RVFI_IF.intr.cause == cfg.nmi_load_fault_cause) ||
//            (cfg.nmi_store_fault_enabled && `RVFI_IF.intr.cause == cfg.nmi_store_fault_cause)) begin
//            void'(rvvi.net_push("nmi_cause", `RVFI_IF.intr.cause)); // Load/Store Error
//            void'(rvvi.net_push("nmi", 1));
//            //mon_trn.insn_nmi = 1;
//            //mon_trn.insn_nmi_cause = mon_trn.intr.cause;
//         end else begin
//            void'(rvvi.net_push("nmi", 0));
//         end
//         // External interrupt
//         //else begin
//         //   mon_trn.insn_interrupt    = 1;
//         //   mon_trn.insn_interrupt_id = { 1'b0, mon_trn.intr.cause };
//         //end
//      end else begin
//         void'(rvvi.net_push("nmi", 0));
//      end
//   end: pass_nmi_to_ref
   
   
   ////////////////////////////////////////////////////////////////////////////
   // External Exceptions
   // InstructionBusFault
   
   ////////////////////////////////////////////////////////////////////////////
   // INTERRUPTS
   always @(posedge rvvi.clk) begin: pass_irq_to_ref
     static bit [31:0] irq_in;
     static bit [31:0] irq_out;

     irq_in = `DUT_PATH.irq_i;

     if (irq_out != irq_in) begin
       // gate this with mip ?
       void'(rvvi.net_push("MSWInterrupt",        irq_in[ 3]));
       void'(rvvi.net_push("MTimerInterrupt",     irq_in[ 7]));
       void'(rvvi.net_push("MExternalInterrupt",  irq_in[11]));
       void'(rvvi.net_push("LocalInterrupt0",     irq_in[16]));
       void'(rvvi.net_push("LocalInterrupt1",     irq_in[17]));
       void'(rvvi.net_push("LocalInterrupt2",     irq_in[18]));
       void'(rvvi.net_push("LocalInterrupt3",     irq_in[19]));
       void'(rvvi.net_push("LocalInterrupt4",     irq_in[20]));
       void'(rvvi.net_push("LocalInterrupt5",     irq_in[21]));
       void'(rvvi.net_push("LocalInterrupt6",     irq_in[22]));
       void'(rvvi.net_push("LocalInterrupt7",     irq_in[23]));
       void'(rvvi.net_push("LocalInterrupt8",     irq_in[24]));
       void'(rvvi.net_push("LocalInterrupt9",     irq_in[25]));
       void'(rvvi.net_push("LocalInterrupt10",    irq_in[26]));
       void'(rvvi.net_push("LocalInterrupt11",    irq_in[27]));
       void'(rvvi.net_push("LocalInterrupt12",    irq_in[28]));
       void'(rvvi.net_push("LocalInterrupt13",    irq_in[29]));
       void'(rvvi.net_push("LocalInterrupt14",    irq_in[30]));
       void'(rvvi.net_push("LocalInterrupt15",    irq_in[31]));
       `uvm_info(info_tag, $sformatf("%t order=%0d irq_in=%08x", 
           $time, `RVFI_IF.rvfi_order, irq_in), UVM_DEBUG)
     end
     irq_out = irq_in;

   end: pass_irq_to_ref
   /*
   always_comb begin
     $display("mcause_rdata=%08X mask=%08X", `DUT_PATH.rvfi_csr_mcause_if_0_i.rvfi_csr_rdata, `DUT_PATH.rvfi_csr_mcause_if_0_i.rvfi_csr_rmask);
     $display("mcause_wdata=%08X mask=%08X", `DUT_PATH.rvfi_csr_mcause_if_0_i.rvfi_csr_wdata, `DUT_PATH.rvfi_csr_mcause_if_0_i.rvfi_csr_wmask);
     $display("rvvi.csr[0][0][CSR_MCAUSE_ADDR]=%08X", rvvi.csr[0][0][`CSR_MCAUSE_ADDR]);
     $display("rvvi.csr_wb[0][0][CSR_MCAUSE_ADDR]=%0d", rvvi.csr_wb[0][0][`CSR_MCAUSE_ADDR]);
   end
   always_comb begin
     $display("mstatus_rdata=%08X mask=%08X", `DUT_PATH.rvfi_csr_mstatus_if_0_i.rvfi_csr_rdata, `DUT_PATH.rvfi_csr_mstatus_if_0_i.rvfi_csr_rmask);
     $display("mstatus_wdata=%08X mask=%08X", `DUT_PATH.rvfi_csr_mstatus_if_0_i.rvfi_csr_wdata, `DUT_PATH.rvfi_csr_mstatus_if_0_i.rvfi_csr_wmask);
     $display("rvvi.csr[0][0][CSR_MSTATUS_ADDR]=%08X", rvvi.csr[0][0][`CSR_MSTATUS_ADDR]);
     $display("rvvi.csr_wb[0][0][CSR_MSTATUS_ADDR]=%0d", rvvi.csr_wb[0][0][`CSR_MSTATUS_ADDR]);
   end
   always_comb begin
     $display("irq=%08X", `DUT_PATH.irq_i);
   end
   always_comb begin
     $display("mip_rdata=%08X mask=%08X", `DUT_PATH.rvfi_csr_mip_if_0_i.rvfi_csr_rdata, `DUT_PATH.rvfi_csr_mip_if_0_i.rvfi_csr_rmask);
     $display("mip_wdata=%08X mask=%08X", `DUT_PATH.rvfi_csr_mip_if_0_i.rvfi_csr_wdata, `DUT_PATH.rvfi_csr_mip_if_0_i.rvfi_csr_wmask);
     $display("rvvi.csr[0][0][CSR_MIP_ADDR]=%08X", rvvi.csr[0][0][`CSR_MIP_ADDR]);
     $display("rvvi.csr_wb[0][0][CSR_MIP_ADDR]=%0d", rvvi.csr_wb[0][0][`CSR_MIP_ADDR]);
   end

   always_comb begin
     $display("mie_rdata=%08X mask=%08X", `DUT_PATH.rvfi_csr_mie_if_0_i.rvfi_csr_rdata, `DUT_PATH.rvfi_csr_mie_if_0_i.rvfi_csr_rmask);
     $display("mie_wdata=%08X mask=%08X", `DUT_PATH.rvfi_csr_mie_if_0_i.rvfi_csr_wdata, `DUT_PATH.rvfi_csr_mie_if_0_i.rvfi_csr_wmask);
     $display("rvvi.csr[0][0][CSR_MIE_ADDR]=%08X", rvvi.csr[0][0][`CSR_MIE_ADDR]);
     $display("rvvi.csr_wb[0][0][CSR_MIE_ADDR]=%0d", rvvi.csr_wb[0][0][`CSR_MIE_ADDR]);
   end
   */
   /*
   bit csr_mcause_wb;
   assign rvvi.csr[0][0][`CSR_MCAUSE_ADDR]    = `DUT_PATH.rvfi_csr_mcause_if_0_i.rvfi_csr_rdata;
   assign rvvi.csr_wb[0][0][`CSR_MCAUSE_ADDR] = csr_mcause_wb;
   always @(`DUT_PATH.rvfi_csr_mcause_if_0_i.rvfi_csr_rdata) begin
       csr_mcause_wb = 1;
       $display("change begin mcause");
   end
   always @(posedge rvvi.clk) begin : always_MCAUSE
       if (`RVFI_IF.rvfi_valid && csr_mcause_wb) begin
           csr_mcause_wb = 0;
           $display("change end mcause");
       end
   end
   */

  /////////////////////////////////////////////////////////////////////////////
  // REF control

  task ref_init;
    string test_program_elf;
    reg [31:0] hart_id;

    // Initialize REF and load the test-program into it's memory (do this before initializing the DUT).
    // TODO: is this the best place for this?
    if (!rvviVersionCheck(`RVVI_API_VERSION)) begin
      `uvm_fatal(info_tag, $sformatf("Expecting RVVI API version %0d.", `RVVI_API_VERSION))
    end
    // Test-program must have been compiled before we got here...
    if ($value$plusargs("elf_file=%s", test_program_elf)) begin
      `uvm_info(info_tag, $sformatf("ImperasDV loading test_program %0s", test_program_elf), UVM_NONE)
      //if (!rvviRefInit(test_program_elf, "openhwgroup.ovpworld.org", "CV32E40X_V0.2.0", 0, `RVVI_TRUE)) begin
      if (!rvviRefInit(test_program_elf, "openhwgroup.ovpworld.org", "CV32E40X", 0)) begin
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
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_CYCLEH_ADDR       ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_INSTRET_ADDR      ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_INSTRETH_ADDR     ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MCYCLE_ADDR       ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MINSTRET_ADDR     ));

    // TODO: deal with the MHPMCOUNTER CSRs properly.
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER3_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMCOUNTER3H_ADDR ));
    void'(rvviRefCsrSetVolatile(hart_id, `CSR_MHPMEVENT3_ADDR ));

    rvviRefCsrCompareEnable(hart_id, `CSR_MIP_ADDR,       `RVVI_FALSE);
    rvviRefCsrCompareEnable(hart_id, `CSR_MSTATUS_ADDR,   `RVVI_FALSE);
    rvviRefCsrCompareEnable(hart_id, `CSR_MEPC_ADDR,      `RVVI_FALSE);
    rvviRefCsrCompareEnable(hart_id, `CSR_MCAUSE_ADDR,    `RVVI_TRUE);

    rvviRefCsrCompareEnable(hart_id, `CSR_MISA_ADDR,      `RVVI_FALSE);

    rvviRefCsrCompareEnable(hart_id, `CSR_DCSR_ADDR,      `RVVI_FALSE);
    rvviRefCsrCompareEnable(hart_id, `CSR_DEPC_ADDR,      `RVVI_FALSE);
    rvviRefCsrCompareEnable(hart_id, `CSR_DSCRATCH0_ADDR, `RVVI_FALSE);
    rvviRefCsrCompareEnable(hart_id, `CSR_DSCRATCH1_ADDR, `RVVI_FALSE);
    rvviRefCsrCompareEnable(hart_id, `CSR_TDATA1_ADDR,    `RVVI_FALSE);
    rvviRefCsrCompareEnable(hart_id, `CSR_TDATA2_ADDR,    `RVVI_FALSE);
    rvviRefCsrCompareEnable(hart_id, `CSR_TINFO_ADDR,     `RVVI_FALSE);

    // Add IO regions of memory
    // According to silabs this range is 0x0080_0000 to 0x0080_0FFF
//    void'(rvviRefMemorySetVolatile('h00800040, 'h00800043)); //TODO: deal with int return value
    void'(rvviRefMemorySetVolatile('h00800000, 'h00800FFF)); //TODO: deal with int return value


    `uvm_info(info_tag, "ref_init() complete", UVM_NONE)
  endtask // ref_init

endmodule : uvmt_cv32e40x_imperas_dv_wrap

`endif // __UVMT_CV32E40X_IMPERAS_DV_WRAP_SV__

