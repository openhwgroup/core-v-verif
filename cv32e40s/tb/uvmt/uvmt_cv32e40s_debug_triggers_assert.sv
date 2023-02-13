//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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

module uvmt_cv32e40s_debug_trigger_assert
  import uvm_pkg::*;
  import uvma_rvfi_pkg::*;
  import cv32e40s_pkg::*;
  (
    input logic [31:0] dm_halt_addr_i,

    input logic support_debug_mode_q,

    input logic support_if_instr_valid,
    input logic support_id_instr_valid,
    input logic support_ex_instr_valid,
    input logic support_wb_instr_valid,

    input logic [31:0] support_pc_if,
    input logic [31:0] support_pc_id,
    input logic [31:0] support_pc_ex,
    input logic [31:0] support_pc_wb,

    uvma_rvfi_instr_if rvfi_if,
    //uvma_clknrst_if clknrst_if,
    input clk,
    input reset_n,
    uvma_rvfi_csr_if rvfi_dcsr_if,
    uvma_rvfi_csr_if rvfi_dpc_if,
    //uvma_rvfi_csr_if csr_mepc,
    //uvma_rvfi_csr_if csr_mstatus,
    //uvma_rvfi_csr_if csr_mtvec,
    uvma_rvfi_csr_if rvfi_tdata1_if,
    uvma_rvfi_csr_if rvfi_tdata2_if,
    uvma_rvfi_csr_if rvfi_tinfo_if,
    uvma_rvfi_csr_if rvfi_tselect_if
    //uvmt_cv32e40s_debug_cov_assert_if debug_if
  );

/////////////////////////////////////////////////////////////////////////////////////////

  // Single clock, single reset design, use default clocking
  //default clocking @(posedge clknrst_if.clk); endclocking
  //default disable iff !(clknrst_if.reset_n);
  default clocking @(posedge clk); endclocking
  default disable iff !(reset_n);

  localparam MODE_M = 3;
  localparam MODE_U = 0;

  //DCP:
  logic [31:0] dpc;
  assign dpc = (rvfi_dpc_if.rvfi_csr_rdata & rvfi_dpc_if.rvfi_csr_rmask);

  //DCSR:
  logic [31:0] dcsr;
  assign dcsr = (rvfi_dcsr_if.rvfi_csr_rdata & rvfi_dcsr_if.rvfi_csr_rmask);


  //tdata1:
  logic [31:0] tdata1;
  assign tdata1 = (rvfi_tdata1_if.rvfi_csr_rdata & rvfi_tdata1_if.rvfi_csr_rmask);

  logic tdata1_m26_execute;
  assign tdata1_m26_execute = tdata1[2];

  logic tdata1_m26_store;
  assign tdata1_m26_store = tdata1[1];

  logic tdata1_m26_load;
  assign tdata1_m26_load = tdata1[0];

  logic [3:0] tdata1_m26_action;
  assign tdata1_m26_action = tdata1[15:12];

  logic [3:0] tdata1_m26_match;
  assign tdata1_m26_match = tdata1[10:7];

  logic [3:0] tdata1_type;
  assign tdata1_type = tdata1[31:28];

  logic tdata1_m26_mode_u_en;
  assign tdata1_m26_mode_u_en = tdata1[3];

  logic tdata1_m26_mode_m_en;
  assign tdata1_m26_mode_m_en = tdata1[6];


  //tdata2:
  logic [31:0] tdata2;
  assign tdata2 = (rvfi_tdata2_if.rvfi_csr_rdata & rvfi_tdata2_if.rvfi_csr_rmask);

  //tinfo
  logic [31:0] tinfo;
  assign tinfo = (rvfi_tinfo_if.rvfi_csr_rdata & rvfi_tinfo_if.rvfi_csr_rmask);

  //tselect
  logic [31:0] tselect;
  assign tselect = (rvfi_tselect_if.rvfi_csr_rdata & rvfi_tselect_if.rvfi_csr_rmask);

  //rvfi_mem_addr
  logic [31:0] mem_addr [128];

  generate
    for (genvar i = 0; i < 128; i++) begin
      assign mem_addr[i] = rvfi_if.rvfi_mem_addr[i*32+31:i*32];
    end
  endgenerate
/*
  logic trigger_match_mem;
  assign trigger_match_mem = (mem_addr[0] == tdata2 && rvfi_if.rvfi_mem_rmask[0][0])
  || (mem_addr[1] == tdata2 && rvfi_if.rvfi_mem_rmask[0][1])
  || (mem_addr[2] == tdata2 && rvfi_if.rvfi_mem_rmask[0][2])
  || (mem_addr[3] == tdata2 && rvfi_if.rvfi_mem_rmask[0][3])
  || (mem_addr[4] == tdata2 && rvfi_if.rvfi_mem_rmask[0][4])
  || (mem_addr[5] == tdata2 && rvfi_if.rvfi_mem_rmask[0][5])
  || (mem_addr[6] == tdata2 && rvfi_if.rvfi_mem_rmask[0][6])
  || (mem_addr[7] == tdata2 && rvfi_if.rvfi_mem_rmask[0][7])
  || (mem_addr[8] == tdata2 && rvfi_if.rvfi_mem_rmask[0][8])
  || (mem_addr[9] == tdata2 && rvfi_if.rvfi_mem_rmask[0][9])
  || (mem_addr[10] == tdata2 && rvfi_if.rvfi_mem_rmask[0][10])
  || (mem_addr[11] == tdata2 && rvfi_if.rvfi_mem_rmask[0][11])
  || (mem_addr[12] == tdata2 && rvfi_if.rvfi_mem_rmask[0][12])
  || (mem_addr[13] == tdata2 && rvfi_if.rvfi_mem_rmask[0][13])
  || (mem_addr[14] == tdata2 && rvfi_if.rvfi_mem_rmask[0][14])
  || (mem_addr[15] == tdata2 && rvfi_if.rvfi_mem_rmask[0][15])
  || (mem_addr[16] == tdata2 && rvfi_if.rvfi_mem_rmask[0][16])
  || (mem_addr[17] == tdata2 && rvfi_if.rvfi_mem_rmask[0][17])
  || (mem_addr[18] == tdata2 && rvfi_if.rvfi_mem_rmask[0][18])
  || (mem_addr[19] == tdata2 && rvfi_if.rvfi_mem_rmask[0][19])
  || (mem_addr[20] == tdata2 && rvfi_if.rvfi_mem_rmask[0][20])
  || (mem_addr[21] == tdata2 && rvfi_if.rvfi_mem_rmask[0][21])
  || (mem_addr[22] == tdata2 && rvfi_if.rvfi_mem_rmask[0][22])
  || (mem_addr[23] == tdata2 && rvfi_if.rvfi_mem_rmask[0][23])
  || (mem_addr[24] == tdata2 && rvfi_if.rvfi_mem_rmask[0][24])
  || (mem_addr[25] == tdata2 && rvfi_if.rvfi_mem_rmask[0][25])
  || (mem_addr[26] == tdata2 && rvfi_if.rvfi_mem_rmask[0][26])
  || (mem_addr[27] == tdata2 && rvfi_if.rvfi_mem_rmask[0][27])
  || (mem_addr[28] == tdata2 && rvfi_if.rvfi_mem_rmask[0][28])
  || (mem_addr[29] == tdata2 && rvfi_if.rvfi_mem_rmask[0][29])
  || (mem_addr[30] == tdata2 && rvfi_if.rvfi_mem_rmask[0][30])
  || (mem_addr[31] == tdata2 && rvfi_if.rvfi_mem_rmask[0][31])
  || (mem_addr[32] == tdata2 && rvfi_if.rvfi_mem_rmask[1][0])
  || (mem_addr[33] == tdata2 && rvfi_if.rvfi_mem_rmask[1][1])
  || (mem_addr[34] == tdata2 && rvfi_if.rvfi_mem_rmask[1][2])
  || (mem_addr[35] == tdata2 && rvfi_if.rvfi_mem_rmask[1][3])
  || (mem_addr[36] == tdata2 && rvfi_if.rvfi_mem_rmask[1][4])
  || (mem_addr[37] == tdata2 && rvfi_if.rvfi_mem_rmask[1][5])
  || (mem_addr[38] == tdata2 && rvfi_if.rvfi_mem_rmask[1][6])
  || (mem_addr[39] == tdata2 && rvfi_if.rvfi_mem_rmask[1][7])
  || (mem_addr[40] == tdata2 && rvfi_if.rvfi_mem_rmask[1][8])
  || (mem_addr[41] == tdata2 && rvfi_if.rvfi_mem_rmask[1][9])
  || (mem_addr[42] == tdata2 && rvfi_if.rvfi_mem_rmask[1][10])
  || (mem_addr[43] == tdata2 && rvfi_if.rvfi_mem_rmask[1][11])
  || (mem_addr[44] == tdata2 && rvfi_if.rvfi_mem_rmask[1][12])
  || (mem_addr[45] == tdata2 && rvfi_if.rvfi_mem_rmask[1][13])
  || (mem_addr[46] == tdata2 && rvfi_if.rvfi_mem_rmask[1][14])
  || (mem_addr[47] == tdata2 && rvfi_if.rvfi_mem_rmask[1][15])
  || (mem_addr[48] == tdata2 && rvfi_if.rvfi_mem_rmask[1][16])
  || (mem_addr[49] == tdata2 && rvfi_if.rvfi_mem_rmask[1][17])
  || (mem_addr[50] == tdata2 && rvfi_if.rvfi_mem_rmask[1][18])
  || (mem_addr[51] == tdata2 && rvfi_if.rvfi_mem_rmask[1][19])
  || (mem_addr[52] == tdata2 && rvfi_if.rvfi_mem_rmask[1][20])
  || (mem_addr[53] == tdata2 && rvfi_if.rvfi_mem_rmask[1][21])
  || (mem_addr[54] == tdata2 && rvfi_if.rvfi_mem_rmask[1][22])
  || (mem_addr[55] == tdata2 && rvfi_if.rvfi_mem_rmask[1][23])
  || (mem_addr[56] == tdata2 && rvfi_if.rvfi_mem_rmask[1][24])
  || (mem_addr[57] == tdata2 && rvfi_if.rvfi_mem_rmask[1][25])
  || (mem_addr[58] == tdata2 && rvfi_if.rvfi_mem_rmask[1][26])
  || (mem_addr[59] == tdata2 && rvfi_if.rvfi_mem_rmask[1][27])
  || (mem_addr[60] == tdata2 && rvfi_if.rvfi_mem_rmask[1][28])
  || (mem_addr[61] == tdata2 && rvfi_if.rvfi_mem_rmask[1][29])
  || (mem_addr[62] == tdata2 && rvfi_if.rvfi_mem_rmask[1][30])
  || (mem_addr[63] == tdata2 && rvfi_if.rvfi_mem_rmask[1][31])
  || (mem_addr[64] == tdata2 && rvfi_if.rvfi_mem_rmask[2][0])
  || (mem_addr[65] == tdata2 && rvfi_if.rvfi_mem_rmask[2][1])
  || (mem_addr[66] == tdata2 && rvfi_if.rvfi_mem_rmask[2][2])
  || (mem_addr[67] == tdata2 && rvfi_if.rvfi_mem_rmask[2][3])
  || (mem_addr[68] == tdata2 && rvfi_if.rvfi_mem_rmask[2][4])
  || (mem_addr[69] == tdata2 && rvfi_if.rvfi_mem_rmask[2][5])
  || (mem_addr[70] == tdata2 && rvfi_if.rvfi_mem_rmask[2][6])
  || (mem_addr[71] == tdata2 && rvfi_if.rvfi_mem_rmask[2][7])
  || (mem_addr[72] == tdata2 && rvfi_if.rvfi_mem_rmask[2][8])
  || (mem_addr[73] == tdata2 && rvfi_if.rvfi_mem_rmask[2][9])
  || (mem_addr[74] == tdata2 && rvfi_if.rvfi_mem_rmask[2][10])
  || (mem_addr[75] == tdata2 && rvfi_if.rvfi_mem_rmask[2][11])
  || (mem_addr[76] == tdata2 && rvfi_if.rvfi_mem_rmask[2][12])
  || (mem_addr[77] == tdata2 && rvfi_if.rvfi_mem_rmask[2][13])
  || (mem_addr[78] == tdata2 && rvfi_if.rvfi_mem_rmask[2][14])
  || (mem_addr[79] == tdata2 && rvfi_if.rvfi_mem_rmask[2][15])
  || (mem_addr[80] == tdata2 && rvfi_if.rvfi_mem_rmask[2][16])
  || (mem_addr[81] == tdata2 && rvfi_if.rvfi_mem_rmask[2][17])
  || (mem_addr[82] == tdata2 && rvfi_if.rvfi_mem_rmask[2][18])
  || (mem_addr[83] == tdata2 && rvfi_if.rvfi_mem_rmask[2][19])
  || (mem_addr[84] == tdata2 && rvfi_if.rvfi_mem_rmask[2][20])
  || (mem_addr[85] == tdata2 && rvfi_if.rvfi_mem_rmask[2][21])
  || (mem_addr[86] == tdata2 && rvfi_if.rvfi_mem_rmask[2][22])
  || (mem_addr[87] == tdata2 && rvfi_if.rvfi_mem_rmask[2][23])
  || (mem_addr[88] == tdata2 && rvfi_if.rvfi_mem_rmask[2][24])
  || (mem_addr[89] == tdata2 && rvfi_if.rvfi_mem_rmask[2][25])
  || (mem_addr[90] == tdata2 && rvfi_if.rvfi_mem_rmask[2][26])
  || (mem_addr[91] == tdata2 && rvfi_if.rvfi_mem_rmask[2][27])
  || (mem_addr[92] == tdata2 && rvfi_if.rvfi_mem_rmask[2][28])
  || (mem_addr[93] == tdata2 && rvfi_if.rvfi_mem_rmask[2][29])
  || (mem_addr[94] == tdata2 && rvfi_if.rvfi_mem_rmask[2][30])
  || (mem_addr[95] == tdata2 && rvfi_if.rvfi_mem_rmask[2][31])
  || (mem_addr[96] == tdata2 && rvfi_if.rvfi_mem_rmask[3][0])
  || (mem_addr[97] == tdata2 && rvfi_if.rvfi_mem_rmask[3][1])
  || (mem_addr[98] == tdata2 && rvfi_if.rvfi_mem_rmask[3][2])
  || (mem_addr[99] == tdata2 && rvfi_if.rvfi_mem_rmask[3][3])
  || (mem_addr[100] == tdata2 && rvfi_if.rvfi_mem_rmask[3][4])
  || (mem_addr[101] == tdata2 && rvfi_if.rvfi_mem_rmask[3][5])
  || (mem_addr[102] == tdata2 && rvfi_if.rvfi_mem_rmask[3][6])
  || (mem_addr[103] == tdata2 && rvfi_if.rvfi_mem_rmask[3][7])
  || (mem_addr[104] == tdata2 && rvfi_if.rvfi_mem_rmask[3][8])
  || (mem_addr[105] == tdata2 && rvfi_if.rvfi_mem_rmask[3][9])
  || (mem_addr[106] == tdata2 && rvfi_if.rvfi_mem_rmask[3][10])
  || (mem_addr[107] == tdata2 && rvfi_if.rvfi_mem_rmask[3][11])
  || (mem_addr[108] == tdata2 && rvfi_if.rvfi_mem_rmask[3][12])
  || (mem_addr[109] == tdata2 && rvfi_if.rvfi_mem_rmask[3][13])
  || (mem_addr[110] == tdata2 && rvfi_if.rvfi_mem_rmask[3][14])
  || (mem_addr[111] == tdata2 && rvfi_if.rvfi_mem_rmask[3][15])
  || (mem_addr[112] == tdata2 && rvfi_if.rvfi_mem_rmask[3][16])
  || (mem_addr[113] == tdata2 && rvfi_if.rvfi_mem_rmask[3][17])
  || (mem_addr[114] == tdata2 && rvfi_if.rvfi_mem_rmask[3][18])
  || (mem_addr[115] == tdata2 && rvfi_if.rvfi_mem_rmask[3][19])
  || (mem_addr[116] == tdata2 && rvfi_if.rvfi_mem_rmask[3][20])
  || (mem_addr[117] == tdata2 && rvfi_if.rvfi_mem_rmask[3][21])
  || (mem_addr[118] == tdata2 && rvfi_if.rvfi_mem_rmask[3][22])
  || (mem_addr[119] == tdata2 && rvfi_if.rvfi_mem_rmask[3][23])
  || (mem_addr[120] == tdata2 && rvfi_if.rvfi_mem_rmask[3][24])
  || (mem_addr[121] == tdata2 && rvfi_if.rvfi_mem_rmask[3][25])
  || (mem_addr[122] == tdata2 && rvfi_if.rvfi_mem_rmask[3][26])
  || (mem_addr[123] == tdata2 && rvfi_if.rvfi_mem_rmask[3][27])
  || (mem_addr[124] == tdata2 && rvfi_if.rvfi_mem_rmask[3][28])
  || (mem_addr[125] == tdata2 && rvfi_if.rvfi_mem_rmask[3][29])
  || (mem_addr[126] == tdata2 && rvfi_if.rvfi_mem_rmask[3][30])
  || (mem_addr[127] == tdata2 && rvfi_if.rvfi_mem_rmask[3][31]);
*/

  //-Verify that core enters debug mode on breakpoint addr (if, or load/store)
  //-Current PC is saved to DPC (next instruction)
  //-Cause of debug must be saved to DCSR (cause=2) (next instruction)
  //-PC is updated to value on dm_haltaddr_i input (next instruction?)
  //-Core starts executing debug code (next instruction in debug)

  //Verification plan point 1:

  property p_tinfo(trigger_type);
    rvfi_if.rvfi_valid
    && tdata1_type == trigger_type
    |->
    tinfo[trigger_type];
  endproperty

  generate
    for (genvar t = 0; t < 16; t++) begin
      a_dt_tinfo: assert property(
        p_tinfo(t)
      );
    end
  endgenerate

  a_load_store_op: cover property(
    rvfi_if.rvfi_valid
    && rvfi_if.rvfi_insn[6:0] == 7'h23
    ##[1:$]
    rvfi_if.rvfi_valid
    && rvfi_if.rvfi_insn[6:0] == 7'h3
  );

  //EXECUTE:

  //TODO: add covers
  a_dt_enter_dbg_breakpoint_execute: assert property(

    //Execute instruction that enter debug mode:
    //TODO: ta hensyn til at man kan ha flere aksesseringer
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode
    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)

    && tdata1_m26_execute
    && tdata1_m26_action == 4'h1
    && ((tdata1_m26_mode_m_en && rvfi_if.rvfi_mode == MODE_M) || (tdata1_m26_mode_u_en && rvfi_if.rvfi_mode == MODE_U))

    && ((tdata1_m26_match == 4'h0 && rvfi_if.rvfi_pc_rdata == tdata2))

    ##1 rvfi_if.rvfi_valid[->1]

    |->
    //Verify that we enter debug mode
    rvfi_if.rvfi_dbg_mode
  );

  a_dt_enter_dbg_breakpoint_execute2: assert property(

    //Execute instruction that enter debug mode:
    //TODO: ta hensyn til at man kan ha flere aksesseringer
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode
    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)

    && tdata1_m26_execute
    && tdata1_m26_action == 4'h1
    && ((tdata1_m26_mode_m_en && rvfi_if.rvfi_mode == MODE_M) || (tdata1_m26_mode_u_en && rvfi_if.rvfi_mode == MODE_U))

    && ((tdata1_m26_match == 4'h2 && rvfi_if.rvfi_pc_rdata >= tdata2))

    ##1 rvfi_if.rvfi_valid[->1]

    |->
    //Verify that we enter debug mode
    rvfi_if.rvfi_dbg_mode
  );

  a_dt_enter_dbg_breakpoint_execute3: assert property(

    //Execute instruction that enter debug mode:
    //TODO: ta hensyn til at man kan ha flere aksesseringer
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode
    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)

    && tdata1_m26_execute
    && tdata1_m26_action == 4'h1
    && ((tdata1_m26_mode_m_en && rvfi_if.rvfi_mode == MODE_M) || (tdata1_m26_mode_u_en && rvfi_if.rvfi_mode == MODE_U))

    && ((tdata1_m26_match == 4'h3 && rvfi_if.rvfi_pc_rdata < tdata2))

    ##1 rvfi_if.rvfi_valid[->1]

    |->
    //Verify that we enter debug mode
    rvfi_if.rvfi_dbg_mode
  );

  //LOAD:

  //TODO: add covers
  a_dt_enter_dbg_breakpoint_load: assert property(

    //Execute instruction that enter debug mode:
    //TODO: ta hensyn til at man kan ha flere aksesseringer
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && !rvfi_if.rvfi_dbg_mode
    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)

    && tdata1_m26_load
    && tdata1_m26_action == 4'h1
    && ((tdata1_m26_mode_m_en && rvfi_if.rvfi_mode == MODE_M) || (tdata1_m26_mode_u_en && rvfi_if.rvfi_mode == MODE_U))

    && mem_addr[0] != '0
    && rvfi_if.rvfi_insn[6:0] == 7'h3
    && ((tdata1_m26_match == 0 && mem_addr[0] == tdata2))

    ##1 rvfi_if.rvfi_valid[->1]

    |->
    //Verify that we enter debug mode
    rvfi_if.rvfi_dbg_mode
  );

  a_dt_enter_dbg_breakpoint_load2: assert property(

    //Execute instruction that enter debug mode:
    //TODO: ta hensyn til at man kan ha flere aksesseringer
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && !rvfi_if.rvfi_dbg_mode
    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)

    && tdata1_m26_load
    && tdata1_m26_action == 4'h1
    && ((tdata1_m26_mode_m_en && rvfi_if.rvfi_mode == MODE_M) || (tdata1_m26_mode_u_en && rvfi_if.rvfi_mode == MODE_U))

    && mem_addr[0] != '0
    && rvfi_if.rvfi_insn[6:0] == 7'h3
    && ((tdata1_m26_match == 2 && mem_addr[0] >= tdata2))

    ##1 rvfi_if.rvfi_valid[->1]

    |->
    //Verify that we enter debug mode
    rvfi_if.rvfi_dbg_mode
  );

  a_dt_enter_dbg_breakpoint_load3: assert property(

    //Execute instruction that enter debug mode:
    //TODO: ta hensyn til at man kan ha flere aksesseringer
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && !rvfi_if.rvfi_dbg_mode
    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)

    && tdata1_m26_load
    && tdata1_m26_action == 4'h1
    && ((tdata1_m26_mode_m_en && rvfi_if.rvfi_mode == MODE_M) || (tdata1_m26_mode_u_en && rvfi_if.rvfi_mode == MODE_U))

    && mem_addr[0] != '0
    && rvfi_if.rvfi_insn[6:0] == 7'h3
    && ((tdata1_m26_match == 3 && mem_addr[0] < tdata2))

    ##1 rvfi_if.rvfi_valid[->1]

    |->
    //Verify that we enter debug mode
    rvfi_if.rvfi_dbg_mode
  );

  //STORE:

  //TODO: add covers
  a_dt_enter_dbg_breakpoint_store: assert property(
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && !rvfi_if.rvfi_dbg_mode
    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)

    && tdata1_m26_store
    && tdata1_m26_action == 4'h1
    && ((tdata1_m26_mode_m_en && rvfi_if.rvfi_mode == MODE_M) || (tdata1_m26_mode_u_en && rvfi_if.rvfi_mode == MODE_U))

    && mem_addr[0] != '0
    && rvfi_if.rvfi_insn[6:0] == 7'h23
    && ((tdata1_m26_match == 0 && mem_addr[0] == tdata2))

    ##1 rvfi_if.rvfi_valid[->1]

    |->
    //Verify that we enter debug mode
    rvfi_if.rvfi_dbg_mode
  );

  a_dt_enter_dbg_breakpoint_store2: assert property(
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && !rvfi_if.rvfi_dbg_mode
    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)

    && tdata1_m26_store
    && tdata1_m26_action == 4'h1
    && ((tdata1_m26_mode_m_en && rvfi_if.rvfi_mode == MODE_M) || (tdata1_m26_mode_u_en && rvfi_if.rvfi_mode == MODE_U))

    && mem_addr[0] != '0
    && rvfi_if.rvfi_insn[6:0] == 7'h23
    && ((tdata1_m26_match == 2 && mem_addr[0] >= tdata2))

    ##1 rvfi_if.rvfi_valid[->1]

    |->
    //Verify that we enter debug mode
    rvfi_if.rvfi_dbg_mode
  );

  a_dt_enter_dbg_breakpoint_store3: assert property(
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && !rvfi_if.rvfi_dbg_mode
    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)

    && tdata1_m26_store
    && tdata1_m26_action == 4'h1
    && ((tdata1_m26_mode_m_en && rvfi_if.rvfi_mode == MODE_M) || (tdata1_m26_mode_u_en && rvfi_if.rvfi_mode == MODE_U))

    && mem_addr[0] != '0
    && rvfi_if.rvfi_insn[6:0] == 7'h23
    && ((tdata1_m26_match == 3 && mem_addr[0] < tdata2))

    ##1 rvfi_if.rvfi_valid[->1]

    |->
    //Verify that we enter debug mode
    rvfi_if.rvfi_dbg_mode
  );




  logic [31:0] support_pc_q1;
  logic [31:0] enter_debug_PC;
  logic pc_dm_addr_match_half_sticky;

  always @(posedge clk) begin
      if (support_wb_instr_valid) begin
      support_pc_q1 <= support_pc_wb;

      end else if(support_ex_instr_valid) begin
      support_pc_q1 <= support_pc_ex;

      end else if(support_id_instr_valid) begin
      support_pc_q1 <= support_pc_id;

      end else begin
      support_pc_q1 <= support_pc_if;
      end

    if(support_pc_if == dm_halt_addr_i && $rose(support_debug_mode_q)) begin //Nå vet vi at vi har entered debug.
      pc_dm_addr_match_half_sticky = 1;
      enter_debug_PC = support_pc_q1;
    end
    if (rvfi_if.rvfi_valid) begin
      pc_dm_addr_match_half_sticky <= 0;
    end
  end


  a_dt_debug_state_initialization: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && $rose(rvfi_if.rvfi_dbg_mode)
    |->
    dcsr[8:6] == rvfi_if.rvfi_dbg
    && rvfi_if.rvfi_pc_rdata == dm_halt_addr_i
    && dpc == enter_debug_PC
  );

  //Verification plan point 2:

  //Disable breakpoing addr to tdata1 - verify that core does not enter debug mode on breakpoint addr

  //Machine mode, user mode

  a_dt_debug_state_initialization_1: assert property (
    rvfi_if.rvfi_valid
    && rvfi_if.rvfi_mode == MODE_M
    && !tdata1_m26_mode_m_en
    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)
    ##1 rvfi_if.rvfi_valid[->1]
    |->
    rvfi_if.rvfi_dbg != 3'h2
  );

  a_dt_debug_state_initialization_2: assert property (
    rvfi_if.rvfi_valid
    && rvfi_if.rvfi_mode == MODE_U
    && !tdata1_m26_mode_u_en
    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)
    ##1 rvfi_if.rvfi_valid[->1]
    |->
    rvfi_if.rvfi_dbg != 3'h2
  );

  //Execute, load, store:

  a_dt_debug_state_initialization_execute: assert property (
    rvfi_if.rvfi_valid

    && pc_dm_addr_match_half_sticky //Istedenfor sticky_bit: (<, =>, ==) avhengig av match verdi.
    //Kan også bruke ikke-minneoperasjons sjekk. //TODO: dersom vi endrer denne, må vi endre den over også.

    && !tdata1_m26_execute

    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)
    ##1 rvfi_if.rvfi_valid[->1]
    |->
    rvfi_if.rvfi_dbg != 3'h2
  );


  a_dt_debug_state_initialization_load: assert property (
    rvfi_if.rvfi_valid

    && rvfi_if.rvfi_mem_rmask > '0

    && (((rvfi_if.rvfi_mem_rdata & rvfi_if.rvfi_mem_rmask) == tdata2 && tdata1_m26_match == '0)
    || ((rvfi_if.rvfi_mem_rdata & rvfi_if.rvfi_mem_rmask) >= tdata2 && tdata1_m26_match == 4'h2)
    || ((rvfi_if.rvfi_mem_rdata & rvfi_if.rvfi_mem_rmask) < tdata2 && tdata1_m26_match == 4'h3))

    && !tdata1_m26_load

    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)
    ##1 rvfi_if.rvfi_valid[->1]
    |->
    rvfi_if.rvfi_dbg != 3'h2
  );

  a_dt_debug_state_initialization_store: assert property ( //TODO: add covers for all assertions!
    rvfi_if.rvfi_valid

    && rvfi_if.rvfi_mem_wmask > '0

    && (((rvfi_if.rvfi_mem_wdata & rvfi_if.rvfi_mem_wmask) == tdata2 && tdata1_m26_match == '0)
    || ((rvfi_if.rvfi_mem_wdata & rvfi_if.rvfi_mem_wmask) >= tdata2 && tdata1_m26_match == 4'h2)
    || ((rvfi_if.rvfi_mem_wdata & rvfi_if.rvfi_mem_wmask) < tdata2 && tdata1_m26_match == 4'h3))

    && !tdata1_m26_store

    && (tdata1_type == 4'h2 || tdata1_type == 4'h6)
    ##1 rvfi_if.rvfi_valid[->1]
    |->
    rvfi_if.rvfi_dbg != 3'h2
  );

  //Verification plan point 3:
//Have 0 triggers, access any trigger register (tdata1, tdata2, tdata3)
//and
// 1) check that illegal instruction exception occurs. csr_wcs --> trap.
//TODO: må teste dette!

  a_dt_0_triggers_tdata1_access: assert property (
    rvfi_if.rvfi_valid
    && uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS == '0
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[14:12] != '0
    && (rvfi_if.rvfi_insn[31:20] == 12'h7A0 //tselect ??
    || rvfi_if.rvfi_insn[31:20] == 12'h7A1 //tdata1
    || rvfi_if.rvfi_insn[31:20] == 12'h7A2 //tdata2
    || rvfi_if.rvfi_insn[31:20] == 12'h7A3 //tdata3
    || rvfi_if.rvfi_insn[31:20] == 12'h7A4 //tinfo ??
    || rvfi_if.rvfi_insn[31:20] == 12'h7A4) //tcontrol ??
    |->
    rvfi_if.rvfi_trap.trap
    && rvfi_if.rvfi_trap.exception
    && rvfi_if.rvfi_trap.exception_cause == 6'h2
  );

// 2) Check that no triggers ever fire. rvfi_dbg != 2
// 3) Check that "tselect" is 0. tselect == 0

  a_dt_0_triggers_tselect_is_0_and_no_triggering: assert property (
    rvfi_if.rvfi_valid
    && uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS == '0
    |->
    tselect == '0
    && rvfi_if.rvfi_dbg != 3'h2
  );

  //Verification plan point 4: //TODO: må enable flere triggere!
//For all number of triggers, use tselect to exercise each trigger with each supported type.
//(Also try writing to higher "tselect" than supported and check that a supported number is read back.)
//Make the triggers fire and check that debug mode is entered.
//Check also that the four context registers trap when accessed.





endmodule : uvmt_cv32e40s_debug_trigger_assert
