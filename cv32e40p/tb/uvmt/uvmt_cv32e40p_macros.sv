//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVMT_CV32E40P_MACROS_SV__
`define __UVMT_CV32E40P_MACROS_SV__


// Create bind for RVFI CSR interface
`define RVFI_CSR_BIND(csr_name) \
  bind cv32e40p_tb_wrapper \
    uvma_rvfi_csr_if#(uvme_cv32e40p_pkg::XLEN) rvfi_csr_``csr_name``_if_0_i(.clk(clk_i), \
                                                                            .reset_n(rst_ni), \
                                                                            .rvfi_csr_rmask(rvfi_i.rvfi_csr_``csr_name``_rmask), \
                                                                            .rvfi_csr_wmask(rvfi_i.rvfi_csr_``csr_name``_wmask), \
                                                                            .rvfi_csr_rdata(rvfi_i.rvfi_csr_``csr_name``_rdata), \
                                                                            .rvfi_csr_wdata(rvfi_i.rvfi_csr_``csr_name``_wdata) \
    );

`define RVFI_CSR_IDX_BIND(csr_name,csr_suffix,idx) \
  bind cv32e40p_tb_wrapper \
    uvma_rvfi_csr_if#(uvme_cv32e40p_pkg::XLEN) rvfi_csr_``csr_name````idx````csr_suffix``_if_0_i( \
                                                                           .clk(clk_i), \
                                                                           .reset_n(rst_ni), \
                                                                           .rvfi_csr_rmask(rvfi_i.rvfi_csr_``csr_name````csr_suffix``_rmask[``idx``]), \
                                                                           .rvfi_csr_wmask(rvfi_i.rvfi_csr_``csr_name````csr_suffix``_wmask[``idx``]), \
                                                                           .rvfi_csr_rdata(rvfi_i.rvfi_csr_``csr_name````csr_suffix``_rdata[``idx``]), \
                                                                           .rvfi_csr_wdata(rvfi_i.rvfi_csr_``csr_name````csr_suffix``_wdata[``idx``]) \
    );

// Create uvm_config_db::set call for a CSR interface
`define RVFI_CSR_UVM_CONFIG_DB_SET(csr_name) \
  uvm_config_db#(virtual uvma_rvfi_csr_if)::set(.cntxt(null), \
                                                .inst_name("*.env.rvfi_agent"), \
                                                .field_name({"csr_", `"csr_name`", "_vif0"}), \
                                                .value(dut_wrap.cv32e40p_tb_wrapper_i.rvfi_csr_``csr_name``_if_0_i));

  
`define PORTMAP_CSR_RVFI_2_RVVI(CSR_NAME) \
  .csr_``CSR_NAME``_rmask  (dut_wrap.cv32e40p_tb_wrapper_i.rvfi_i.rvfi_csr_``CSR_NAME``_rmask), \
  .csr_``CSR_NAME``_wmask  (dut_wrap.cv32e40p_tb_wrapper_i.rvfi_i.rvfi_csr_``CSR_NAME``_wmask), \
  .csr_``CSR_NAME``_rdata  (dut_wrap.cv32e40p_tb_wrapper_i.rvfi_i.rvfi_csr_``CSR_NAME``_rdata), \
  .csr_``CSR_NAME``_wdata  (dut_wrap.cv32e40p_tb_wrapper_i.rvfi_i.rvfi_csr_``CSR_NAME``_wdata),


`define STRINGIFY(x) `"x`"

////////////////////////////////////////////////////////////////////////////
// CSR definitions
////////////////////////////////////////////////////////////////////////////
`define CSR_FFLAGS_ADDR        32'h001
`define CSR_FRM_ADDR           32'h002
`define CSR_FCSR_ADDR          32'h003
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
`define CSR_MSCONTEXT_ADDR     32'h7A9
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
`define CSR_LPSTART0_ADDR      32'hCC0
`define CSR_LPEND0_ADDR        32'hCC1
`define CSR_LPCOUNT0_ADDR      32'hCC2
`define CSR_LPSTART1_ADDR      32'hCC4
`define CSR_LPEND1_ADDR        32'hCC5
`define CSR_LPCOUNT1_ADDR      32'hCC6
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


`endif // __UVMT_CV32E40P_MACROS_SV__
