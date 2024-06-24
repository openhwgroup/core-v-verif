// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2024 Dolphin Design
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

// This file specifies all interfaces used by the CV32E40P test bench (uvmt_cv32e40p_tb), related to RVVI.
// Most interfaces support tasks to allow control by the ENV or test cases.

`ifndef __UVMT_CV32E40P_TB_RVVI_IF_SV__
`define __UVMT_CV32E40P_TB_RVVI_IF_SV__


// core-v-verif simplify rvvi for coverage collection purpose
  `define DEF_CSR_PORTS(CSR_NAME) \
  input logic [(XLEN-1):0] csr_``CSR_NAME``_rmask, \
  input logic [(XLEN-1):0] csr_``CSR_NAME``_wmask, \
  input logic [(XLEN-1):0] csr_``CSR_NAME``_rdata, \
  input logic [(XLEN-1):0] csr_``CSR_NAME``_wdata,

  `define DEF_CSR_PORTS_VEC(CSR_NAME, VEC_SIZE) \
  input logic [(``VEC_SIZE``-1):0][(XLEN-1):0] csr_``CSR_NAME``_rmask, \
  input logic [(``VEC_SIZE``-1):0][(XLEN-1):0] csr_``CSR_NAME``_wmask, \
  input logic [(``VEC_SIZE``-1):0][(XLEN-1):0] csr_``CSR_NAME``_rdata, \
  input logic [(``VEC_SIZE``-1):0][(XLEN-1):0] csr_``CSR_NAME``_wdata,

  `define ASSIGN_CSR_N_WB(CSR_ADDR, CSR_NAME) \
    bit csr_``CSR_NAME``_wb; \
    wire [31:0] csr_``CSR_NAME``_w; \
    wire [31:0] csr_``CSR_NAME``_r; \
    assign csr_``CSR_NAME``_w = csr_``CSR_NAME``_wdata &   csr_``CSR_NAME``_wmask; \
    assign csr_``CSR_NAME``_r = csr_``CSR_NAME``_rdata & ~(csr_``CSR_NAME``_wmask); \
    assign csr[``CSR_ADDR]    = csr_``CSR_NAME``_w | csr_``CSR_NAME``_r; \
    assign csr_wb[``CSR_ADDR] = csr_``CSR_NAME``_wb; \
    always @(csr[``CSR_ADDR]) begin \
        csr_``CSR_NAME``_wb = 1; \
    end \
    always @(posedge clk) begin \
        if (valid && csr_``CSR_NAME``_wb) begin \
            csr_``CSR_NAME``_wb = 0; \
        end \
    end

  `define ASSIGN_CSR_N_WB_VEC(CSR_ADDR, CSR_NAME, CSR_ID) \
    bit csr_``CSR_NAME````CSR_ID``_wb; \
    wire [31:0] csr_``CSR_NAME````CSR_ID``_w; \
    wire [31:0] csr_``CSR_NAME````CSR_ID``_r; \
    assign csr_``CSR_NAME````CSR_ID``_w = csr_``CSR_NAME``_wdata[``CSR_ID] &   csr_``CSR_NAME``_wmask[``CSR_ID]; \
    assign csr_``CSR_NAME````CSR_ID``_r = csr_``CSR_NAME``_rdata[``CSR_ID] & ~(csr_``CSR_NAME``_wmask[``CSR_ID]); \
    assign csr[``CSR_ADDR]              = csr_``CSR_NAME````CSR_ID``_w | csr_``CSR_NAME````CSR_ID``_r; \
    assign csr_wb[``CSR_ADDR]           = csr_``CSR_NAME````CSR_ID``_wb; \
    always @(csr[``CSR_ADDR]) begin \
        csr_``CSR_NAME````CSR_ID``_wb = 1; \
    end \
    always @(posedge clk) begin \
        if (valid && csr_``CSR_NAME````CSR_ID``_wb) begin \
            csr_``CSR_NAME````CSR_ID``_wb = 0; \
        end \
    end

interface uvmt_cv32e40p_rvvi_if #(
  parameter int ILEN    = 32,
  parameter int XLEN    = 32
) (

  input                               clk,
  input                               valid,
  input logic [(ILEN-1):0]            insn,
  input                               trap,
  input logic [31:0]                  pc_rdata,
  input logic [31:0]                  wa_csr_mip,

  uvma_interrupt_if                   interrupt_if,
  uvma_debug_if                       debug_if,

  // Currently only define specific csrs for current usage
  `DEF_CSR_PORTS(lpstart0)
  `DEF_CSR_PORTS(lpend0)
  `DEF_CSR_PORTS(lpcount0)
  `DEF_CSR_PORTS(lpstart1)
  `DEF_CSR_PORTS(lpend1)
  `DEF_CSR_PORTS(lpcount1)
  `DEF_CSR_PORTS(mstatus)
  `DEF_CSR_PORTS(mie)
  `DEF_CSR_PORTS(mtvec)
  `DEF_CSR_PORTS(mcause)
  `DEF_CSR_PORTS(mip)
  `DEF_CSR_PORTS(dcsr)
  `DEF_CSR_PORTS_VEC(tdata,4)

  input logic [31:0]                  dm_halt_addr

);

  wire [31:0]                 valid_irq;
  wire [4095:0][32:0]         csr;
  wire [4095:0]               csr_wb;
  wire [4:0]                  csr_mcause_ecp_code;
  wire [2:0]                  csr_dcsr_cause;
  wire [31:0]                 csr_trig_pc;

  logic [31:0]                irq_onehot_priority;
  logic [31:0]                mtvec_base_addr;
  logic [31:0]                mip;

  // assign valid_irq            = csr[`CSR_MIP_ADDR] & csr[`CSR_MIE_ADDR]; // fixme: rvfi misses mip (pending rvfi fixes; workaround probe rtl signals - wa_csr_mip)
  assign valid_irq            = wa_csr_mip & csr[`CSR_MIE_ADDR];
  assign dbg_req              = debug_if.debug_req;
  assign mie                  = csr[`CSR_MSTATUS_ADDR][3];
  assign mip                  = csr[`CSR_MIP_ADDR];

  assign csr_mcause_irq       = csr[`CSR_MCAUSE_ADDR][31];
  assign csr_mcause_ecp_code  = csr[`CSR_MCAUSE_ADDR][4:0];
  assign csr_dcsr_ebreakm     = csr[`CSR_DCSR_ADDR][15];
  assign csr_dcsr_stepie      = csr[`CSR_DCSR_ADDR][11];
  assign csr_dcsr_cause       = csr[`CSR_DCSR_ADDR][8:6];
  assign csr_dcsr_step        = csr[`CSR_DCSR_ADDR][2];
  assign csr_trig_execute     = csr[`CSR_TDATA1_ADDR][2];
  assign csr_trig_pc          = csr[`CSR_TDATA2_ADDR];

  assign mtvec_base_addr      = {csr[`CSR_MTVEC_ADDR][31:8], 8'h0};

  // can be expanded. Currently only define for current usage
  `ASSIGN_CSR_N_WB(`CSR_LPSTART0_ADDR, lpstart0)
  `ASSIGN_CSR_N_WB(`CSR_LPEND0_ADDR, lpend0)
  `ASSIGN_CSR_N_WB(`CSR_LPCOUNT0_ADDR, lpcount0)
  `ASSIGN_CSR_N_WB(`CSR_LPSTART1_ADDR, lpstart1)
  `ASSIGN_CSR_N_WB(`CSR_LPEND1_ADDR, lpend1)
  `ASSIGN_CSR_N_WB(`CSR_LPCOUNT1_ADDR, lpcount1)
  `ASSIGN_CSR_N_WB(`CSR_MSTATUS_ADDR, mstatus)
  `ASSIGN_CSR_N_WB(`CSR_MIE_ADDR, mie)
  `ASSIGN_CSR_N_WB(`CSR_MTVEC_ADDR, mtvec)
  `ASSIGN_CSR_N_WB(`CSR_MCAUSE_ADDR, mcause)
  `ASSIGN_CSR_N_WB(`CSR_MIP_ADDR, mip)
  `ASSIGN_CSR_N_WB(`CSR_DCSR_ADDR, dcsr)
  `ASSIGN_CSR_N_WB_VEC(`CSR_TDATA1_ADDR, tdata, 1);
  `ASSIGN_CSR_N_WB_VEC(`CSR_TDATA2_ADDR, tdata, 2);

  // irq_onehot_priority assignment (refer cv32e40p user manual, section 10.2)
  // priority order (high->low) is irq[31]...irq[16], irq[11], irq[3], irq[7]
  always @(valid_irq) begin
    irq_onehot_priority = 0;
    for (int i = 31; i != 0; i--) begin
      if (valid_irq[i] && (i inside {31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16, 11,3,7})) begin
        if (i == 7 && valid_irq[3]) continue;
        else begin irq_onehot_priority[i] = valid_irq[i]; break; end
      end
    end
  end

endinterface


`endif // __UVMT_CV32E40P_TB_RVVI_IF_SV__
