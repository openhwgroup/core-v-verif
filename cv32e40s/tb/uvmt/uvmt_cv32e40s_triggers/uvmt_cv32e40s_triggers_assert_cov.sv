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

//The assertions written in this file are denoted with a number.
//You will find this number in the file vplan_coverage.txt,
//and they describe what vplan tasks the assertions aim to cover.

module uvmt_cv32e40s_triggers_assert_cov
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import cv32e40s_rvfi_pkg::*;

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
    uvma_clknrst_if clknrst_if,

    uvma_rvfi_csr_if dcsr,
    uvma_rvfi_csr_if dpc,
    uvma_rvfi_csr_if tdata1,
    uvma_rvfi_csr_if tdata2,
    uvma_rvfi_csr_if tdata3,
    uvma_rvfi_csr_if tinfo,
    uvma_rvfi_csr_if tselect,
    uvma_rvfi_csr_if tcontrol

  );

  default clocking @(posedge clknrst_if.clk); endclocking
  default disable iff !(clknrst_if.reset_n);

  //Privilege levels of the core
  localparam CORE_MODE_M = 3;
  localparam CORE_MODE_U = 0;

  string info_tag = "TRIGGER ASSERT: ";

  //Reads and writes of CSR values
  logic [31:0] dcsr_r;
  logic [31:0] dpc_r;
  logic [31:0] tdata1_r;
  logic [31:0] tdata2_r;
  logic [31:0] tdata3_r;
  logic [31:0] tinfo_r;
  logic [31:0] tselect_r;
  logic [31:0] tcontrol_r;

  logic [31:0] dcsr_w;
  logic [31:0] dpc_w;
  logic [31:0] tdata1_w;
  logic [31:0] tdata2_w;
  logic [31:0] tdata3_w;
  logic [31:0] tinfo_w;
  logic [31:0] tselect_w;
  logic [31:0] tcontrol_w;

  assign dcsr_r = (dcsr.rvfi_csr_rdata & dcsr.rvfi_csr_rmask);
  assign dpc_r = (dpc.rvfi_csr_rdata & dpc.rvfi_csr_rmask);
  assign tdata1_r = (tdata1.rvfi_csr_rdata & tdata1.rvfi_csr_rmask);
  assign tdata2_r = (tdata2.rvfi_csr_rdata & tdata2.rvfi_csr_rmask);
  assign tdata3_r = (tdata3.rvfi_csr_rdata & tdata3.rvfi_csr_rmask);
  assign tinfo_r = (tinfo.rvfi_csr_rdata & tinfo.rvfi_csr_rmask);
  assign tselect_r = (tselect.rvfi_csr_rdata & tselect.rvfi_csr_rmask);
  assign tcontrol_r = (tcontrol.rvfi_csr_rdata & tcontrol.rvfi_csr_rmask);

  assign dcsr_w = (dcsr.rvfi_csr_wdata & dcsr.rvfi_csr_wmask);
  assign dpc_w = (dpc.rvfi_csr_wdata & dpc.rvfi_csr_wmask);
  assign tdata1_w = (tdata1.rvfi_csr_wdata & tdata1.rvfi_csr_wmask);
  assign tdata2_w = (tdata2.rvfi_csr_wdata & tdata2.rvfi_csr_wmask);
  assign tdata3_w = (tdata3.rvfi_csr_wdata & tdata3.rvfi_csr_wmask);
  assign tinfo_w = (tinfo.rvfi_csr_wdata & tinfo.rvfi_csr_wmask);
  assign tselect_w = (tselect.rvfi_csr_wdata & tselect.rvfi_csr_wmask);
  assign tcontrol_w = (tcontrol.rvfi_csr_wdata & tcontrol.rvfi_csr_wmask);

  //Local parameters:

  //tdata1 types:
  localparam MCONTROL = 4'h2;
  localparam ETRIGGER = 4'h5;
  localparam MCONTROL6 = 4'h6;
  localparam DISABLED = 4'hF;

  //common tdata1 mcontrol and mcontrol6 values:
  localparam DMODE = 27;
  localparam LOAD = 0;
  localparam STORE = 1;
  localparam EXECUTE = 2;
  localparam U_MODE = 3;
  localparam S_MODE = 4;
  localparam M_MODE = 6;
  localparam LSB_MATCH = 7;
  localparam MSB_MATCH = 10;
  localparam CHAIN = 11;
  localparam LSB_ACTION = 12;
  localparam MSB_ACTION = 15;
  localparam LSB_TYPE = 28;
  localparam MSB_TYPE = 31;

  //tdata1 mcontrol:
  localparam MSB_MASKMAX = 26;
  localparam LSB_MASKMAX = 21;
  localparam M2_HIT = 20;
  localparam M2_SELECT = 19;
  localparam M2_TIMING = 18;
  localparam MSB_SIZELO = 17;
  localparam LSB_SIZELO = 16;

  //tdata1 mcontrol6:
  localparam M6_VS = 24;
  localparam M6_VU = 23;
  localparam M6_HIT = 22;
  localparam M6_SELECT = 21;
  localparam M6_TIMING = 20;
  localparam MSB_SIZE = 19;
  localparam LSB_SIZE = 16;

  //tdata1 etriggers:
  localparam ET_HIT = 26;
  localparam ET_VS = 12;
  localparam ET_VU = 11;
  localparam ET_S = 7;
  localparam ET_MSB_ACTION = 5;
  localparam ET_LSB_ACTION = 0;

  //tdata1 disabled:
  localparam DIS_MSB_DATA = 26;
  localparam DIS_LSB_DATA = 0;

  //tdata2:
  localparam ET2_DATA_31 = 31;
  localparam ET2_DATA_26 = 26;
  localparam ET2_DATA_23 = 23;
  localparam ET2_DATA_12 = 12;
  localparam ET2_DATA_10 = 10;
  localparam ET2_DATA_9 = 9;
  localparam ET2_DATA_6 = 6;
  localparam ET2_DATA_4 = 4;
  localparam ET2_DATA_0 = 0;

  //tcontrol:
  localparam MPTE = 7;
  localparam MTE = 3;

  //Actions:
  localparam ENTER_DBG_ON_MATCH = 1;

  //Trigger match specifications:
  localparam MATCH_WHEN_EQUAL = 0;
  localparam MATCH_WHEN_GREATER_OR_EQUAL = 2;
  localparam MATCH_WHEN_LESSER = 3;

  //Instruction:
  localparam MSB_OPCODE = 6;
  localparam LSB_OPCODE = 0;
  localparam FUNCT3_13 = 13;
  localparam LSB_FUNCT3 = 12;
  localparam MSB_CSR = 31;
  localparam LSB_CSR = 20;

  //CSR operations:
  localparam CSR_WRITE = 2'b01;
  localparam CSR_CLEAR = 2'b11;
  localparam NO_CSR_WSC = 2'b00;

  //Exceptions:
  localparam INSTR_ACCESS_FAULT = 6'h1;
  localparam INSTR_PARITY_CHECKSUM_FAULT = 6'h19;
  localparam INSTR_BUS_FAULT = 6'h18;
  localparam ILLEGAL_INSTR = 6'h2;

  //CSR addresses:
  localparam ADDR_TSELECT = 12'h7A0;
  localparam ADDR_TDATA1 = 12'h7A1;
  localparam ADDR_TDATA2 = 12'h7A2;
  localparam ADDR_TDATA3 = 12'h7A3;
  localparam ADDR_TINFO = 12'h7A4;
  localparam ADDR_TCONTROL = 12'h7A5;
  localparam ADDR_MCONTEXT = 12'h7A8;
  localparam ADDR_MSCONTEXT = 12'h7AA;
  localparam ADDR_HCONTEXT = 12'h6A8;
  localparam ADDR_SCONTEXT = 12'h5A8;

  //Cause of entering debug:
  localparam TRIGGER_MATCH = 2;

  //DCSR:
  localparam MSB_CAUSE = 8;
  localparam LSB_CAUSE = 6;

  //Hardwired to zero:
  localparam HW_ZERO_31 = 31;
  localparam HW_ZERO_26 = 26;
  localparam HW_ZERO_25 = 25;
  localparam HW_ZERO_16 = 16;
  localparam HW_ZERO_14 = 14;
  localparam HW_ZERO_13 = 13;
  localparam HW_ZERO_10 = 10;
  localparam HW_ZERO_8 = 8;
  localparam HW_ZERO_7 = 7;
  localparam HW_ZERO_6 = 6;
  localparam HW_ZERO_5 = 5;
  localparam HW_ZERO_4 = 4;
  localparam HW_ZERO_3 = 3;
  localparam HW_ZERO_2 = 2;
  localparam HW_ZERO_1 = 1;
  localparam HW_ZERO_0 = 0;

  //tdata1 default value
  localparam TDATA1_DEFAULT = 32'hF800_0000;


  logic [3:0][31:0] tdata1_arry;
  logic [3:0][31:0] tdata2_arry;

  always @(posedge clknrst_if.clk, negedge clknrst_if.reset_n ) begin
    if(!clknrst_if.reset_n) begin
      tdata1_arry[0] = TDATA1_DEFAULT;
      tdata1_arry[1] = TDATA1_DEFAULT;
      tdata1_arry[2] = TDATA1_DEFAULT;
      tdata1_arry[3] = TDATA1_DEFAULT;
      tdata2_arry = '0;

    end else if (rvfi_if.rvfi_valid) begin
      case(tselect_r)
        32'h0:
          begin
            tdata1_arry[0] = tdata1_r;
            tdata2_arry[0] = tdata2_r;
          end
        32'h1:
          begin
            tdata1_arry[1] = tdata1_r;
            tdata2_arry[1] = tdata2_r;
          end
        32'h2:
          begin
            tdata1_arry[2] = tdata1_r;
            tdata2_arry[2] = tdata2_r;
          end
        32'h3:
          begin
            tdata1_arry[3] = tdata1_r;
            tdata2_arry[3] = tdata2_r;
          end
      endcase
    end
  end

  logic [31:0] support_pc_q1;
  logic [31:0] enter_debug_PC;
  logic pc_dm_addr_match_half_sticky;

  always @(posedge clknrst_if.clk) begin
      if (support_wb_instr_valid) begin
      support_pc_q1 <= support_pc_wb;

      end else if(support_ex_instr_valid) begin
      support_pc_q1 <= support_pc_ex;

      end else if(support_id_instr_valid) begin
      support_pc_q1 <= support_pc_id;

      end else begin
      support_pc_q1 <= support_pc_if;
      end

    if(support_pc_if == dm_halt_addr_i && $rose(support_debug_mode_q)) begin //TODO! Nå vet vi at vi har entered debug.
      pc_dm_addr_match_half_sticky = 1;
      enter_debug_PC = support_pc_q1;
    end
    if (rvfi_if.rvfi_valid) begin
      pc_dm_addr_match_half_sticky <= 0;
    end
  end

  //P12-P13: 3) 4) 5) 6) TODO! Endre dennne!
  a_dt_debug_state_initialization: assert property (
    //Make sure we have entered debug mode
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && $rose(rvfi_if.rvfi_dbg_mode)
    |->
    //Verify the correct consequence of entering debug mode
    dcsr_r[MSB_CAUSE:LSB_CAUSE] == rvfi_if.rvfi_dbg
    && rvfi_if.rvfi_pc_rdata == dm_halt_addr_i
    && dpc_r == enter_debug_PC
  ) else `uvm_error(info_tag, "TODO!\n");

  //P16-P17: 1)
  a_dt_0_triggers_tdata1_access: assert property (
    //Make sure there are no triggers
    uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS == '0

    //Make sure there is CSR instruction that tries to access a trigger register
    && rvfi_if.rvfi_valid
    && rvfi_if.rvfi_insn[MSB_OPCODE:LSB_OPCODE] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[FUNCT3_13:LSB_FUNCT3] != NO_CSR_WSC
    && (rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_TSELECT
    || rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_TDATA1
    || rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_TDATA2
    || rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_TDATA3
    || rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_TINFO
    || rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_TCONTROL)

    //Make sure the following exceptions have not occurred
    //(as these exceptions have a higher priority than illegal instruction)
    && rvfi_if.rvfi_trap.exception_cause != INSTR_ACCESS_FAULT
    && rvfi_if.rvfi_trap.exception_cause != INSTR_PARITY_CHECKSUM_FAULT
    && rvfi_if.rvfi_trap.exception_cause != INSTR_BUS_FAULT

    |->
    //Verify that the instruction is traped as an illegal instruction
    rvfi_if.rvfi_trap.trap
    && rvfi_if.rvfi_trap.exception
    && (rvfi_if.rvfi_trap.exception_cause == ILLEGAL_INSTR)
  ) else `uvm_error(info_tag, "TODO!\n");

  //2) 3)
  a_dt_0_triggers_tselect_is_0_and_no_triggering: assert property (
    //Make sure there are no triggers
    uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS == '0

    //Make sure an instruction has been retired
    && rvfi_if.rvfi_valid
    |->
    //Verify that we never enter debug due to a trigger match and that tselect is set to zero
    rvfi_if.rvfi_dbg != TRIGGER_MATCH
    && !tselect_r
  ) else `uvm_error(info_tag, "TODO!\n");

  //P18-P19: 1)
  //Property that checks that trigger number t is set to the type <tdata1_type>
  property p_all_trigger(tselect_trigger_i, tdata1_type);
    tselect_r == tselect_trigger_i
    && tdata1_r[MSB_TYPE:LSB_TYPE] == tdata1_type;
  endproperty

  //Verify that all the triggers can be of type MCONTROL, ETRIGGER, MCONTROL6, or DISABLED
  generate
    for (genvar tselect_trigger_i = 0; tselect_trigger_i < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS; tselect_trigger_i++) begin

      a_trigger_i_has_type_mcontrol: cover property(
        p_all_trigger(tselect_trigger_i, MCONTROL)
      );

      a_trigger_i_has_type_etrigger: cover property(
        p_all_trigger(tselect_trigger_i, ETRIGGER)
      );

      a_trigger_i_has_type_mcontrol6: cover property(
        p_all_trigger(tselect_trigger_i, MCONTROL6)
      );

      a_trigger_i_has_type_disable: cover property(
        p_all_trigger(tselect_trigger_i, DISABLED)
      );

    end
  endgenerate

  //3)
  a_dt_tselect_higher_than_dbg_num_triggers: assert property(
    //Make sure we access TSELECT
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && rvfi_if.rvfi_insn[MSB_OPCODE:LSB_OPCODE] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[FUNCT3_13:LSB_FUNCT3] != NO_CSR_WSC
    && rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_TSELECT

    |->
    //Verify that TSELECT never has a value equal to or higher than the number of triggers
    rvfi_if.rvfi_rd1_wdata < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS
  ) else `uvm_error(info_tag, "TODO!\n");

  //4)
  a_dt_access_context: assert property (
    //Make sure we access the context registers
    rvfi_if.rvfi_valid
    && rvfi_if.rvfi_insn[MSB_OPCODE:LSB_OPCODE] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[FUNCT3_13:LSB_FUNCT3] != NO_CSR_WSC
    && (rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_MCONTEXT
    || rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_MSCONTEXT
    || rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_HCONTEXT
    || rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_SCONTEXT)

    |->
    //Verify that it leads to a trap
    rvfi_if.rvfi_trap.trap
  ) else `uvm_error(info_tag, "TODO!\n");

  //P20-P21: 4) & P26-P27: 2)
  //mcontrol
  a_dt_tie_offs_tdata1_mcontrol: assert property (
    //Make sure the trigger displayed in tdata1 is set to type MCONTROL
    rvfi_if.rvfi_valid
    && tdata1_r[MSB_TYPE:LSB_TYPE] == MCONTROL

    |->
    //Verify that the following fields are tied off:
    tdata1_r[DMODE]
    && !tdata1_r[MSB_MASKMAX:LSB_MASKMAX]
    && !tdata1_r[M2_HIT]
    && !tdata1_r[M2_SELECT]
    && !tdata1_r[M2_TIMING]
    && !tdata1_r[MSB_SIZELO:LSB_SIZELO]
    && tdata1_r[MSB_ACTION:LSB_ACTION] == ENTER_DBG_ON_MATCH
    && !tdata1_r[CHAIN]
    && !tdata1_r[HW_ZERO_5]
    && !tdata1_r[S_MODE]
  ) else `uvm_error(info_tag, "TODO!\n");

  //etrigger
  a_dt_tie_offs_tdata1_etrigger: assert property (
    //Make sure the trigger displayed in tdata1 is set to type ETRIGGER
    rvfi_if.rvfi_valid
    && tdata1_r[MSB_TYPE:LSB_TYPE] == ETRIGGER

    |->
    //Verify that the following fields are tied off:
    tdata1_r[DMODE]
    && !tdata1_r[ET_HIT]
    && !tdata1_r[HW_ZERO_25:HW_ZERO_13]
    && !tdata1_r[ET_VS]
    && !tdata1_r[ET_VU]
    && !tdata1_r[HW_ZERO_10]
    && !tdata1_r[HW_ZERO_8]
    && !tdata1_r[ET_S]
    && tdata1_r[ET_MSB_ACTION:ET_LSB_ACTION] == ENTER_DBG_ON_MATCH
  ) else `uvm_error(info_tag, "TODO!\n");

  //mcontrol6
  a_dt_tie_offs_tdata1_mcontrol6: assert property (
    //Make sure the trigger displayed in tdata1 is set to type MCONTROL6
    rvfi_if.rvfi_valid
    && tdata1_r[MSB_TYPE:LSB_TYPE] == MCONTROL6

    |->
    //Verify that the following fields are tied off:
    tdata1_r[DMODE]
    && !tdata1_r[HW_ZERO_26:HW_ZERO_25]
    && !tdata1_r[M6_VS]
    && !tdata1_r[M6_VU]
    && !tdata1_r[M6_HIT]
    && !tdata1_r[M6_SELECT]
    && !tdata1_r[M6_TIMING]
    && !tdata1_r[MSB_SIZE:LSB_SIZE]
    && tdata1_r[MSB_ACTION:LSB_ACTION] == ENTER_DBG_ON_MATCH
    && !tdata1_r[CHAIN]
    && !tdata1_r[HW_ZERO_5]
    && !tdata1_r[S_MODE]
  ) else `uvm_error(info_tag, "TODO!\n");

  //disabled
  a_dt_tie_offs_tdata1_disabled: assert property (
    //Make sure the trigger displayed in tdata1 is set to type DISABLED
    rvfi_if.rvfi_valid
    && tdata1_r[MSB_TYPE:LSB_TYPE] == DISABLED

    |->
    //Verify that the following fields are tied off:
    tdata1_r[DMODE]
    && !tdata1_r[DIS_MSB_DATA:DIS_LSB_DATA]
  ) else `uvm_error(info_tag, "TODO!\n");

  a_dt_tie_offs_tdata3: assert property (
    rvfi_if.rvfi_valid
    |->
    //Verify that tdata3 is tied to 0
    !tdata3_r
  ) else `uvm_error(info_tag, "TODO!\n");

  a_dt_tie_offs_tinfo: assert property (
    rvfi_if.rvfi_valid
    |->
    //Verify that the upper bits of tinfo is tied to 0
    !tinfo_r[HW_ZERO_31:HW_ZERO_16]
  ) else `uvm_error(info_tag, "TODO!\n");

  a_dt_tie_offs_tcontrol: assert property (
    rvfi_if.rvfi_valid
    |->
    //Verify that the following fields of tcontrol are tied off:
    !tcontrol_r[HW_ZERO_31:HW_ZERO_8]
    && !tcontrol_r[HW_ZERO_6:HW_ZERO_4]
    && !tcontrol_r[HW_ZERO_2:HW_ZERO_0]
  ) else `uvm_error(info_tag, "TODO!\n");

  //P29-P30 1):
  a_dt_tdata1_types: assert property (
    rvfi_if.rvfi_valid
    |->
    //Verify that the tdata1 types are only one of the following:
    tdata1_r[MSB_TYPE:LSB_TYPE] == MCONTROL
    || tdata1_r[MSB_TYPE:LSB_TYPE] == ETRIGGER
    || tdata1_r[MSB_TYPE:LSB_TYPE] == MCONTROL6
    || tdata1_r[MSB_TYPE:LSB_TYPE] == DISABLED
  ) else `uvm_error(info_tag, "TODO!\n");

  //P31-P32: 1)
  a_dt_access_csr_not_dbg_mode: assert property (
    //Make sure we access tdata1, tdata2 or tdata3 in non-debug mode
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode
    && rvfi_if.rvfi_insn[MSB_OPCODE:LSB_OPCODE] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[FUNCT3_13:LSB_FUNCT3] != NO_CSR_WSC
    && (rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_TDATA1
    || rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_TDATA2
    || rvfi_if.rvfi_insn[MSB_CSR:LSB_CSR] == ADDR_TDATA3)

    |->
    //Verify that they are not written to
    !tdata1.rvfi_csr_wmask
    && !tdata2.rvfi_csr_wmask
    && !tdata3.rvfi_csr_wmask
  ) else `uvm_error(info_tag, "TODO!\n");

  //2)
  a_dt_dmode: assert property (
    //Make sure we write to the dmode bit of tdata1
    rvfi_if.rvfi_valid
    && rvfi_if.rvfi_dbg_mode
    && !rvfi_if.rvfi_trap.trap
    && tdata1.rvfi_csr_wmask[DMODE]

    |->
    //Verify that dmode is WARL 0x1
    tdata1_w[DMODE]
  ) else `uvm_error(info_tag, "TODO!\n");


  //P33-P34: 1)
  a_dt_0_triggers_tinfo: assert property (
    //Make sure there are no triggers
    uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS == '0
    && rvfi_if.rvfi_valid

    |->
    //Verify that tinfo is zero
    !tinfo_r
  ) else `uvm_error(info_tag, "TODO!\n");

  //2)
  a_dt_triggers_tinfo: assert property (
    //Make sure there are triggers
    uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS != '0
    && rvfi_if.rvfi_valid

    |->
    //Verify that only the tinfo bits corresponding to the supported tdata1 types are set to 1
    !tinfo_r[HW_ZERO_1:HW_ZERO_0]
    && tinfo_r[MCONTROL]
    && !tinfo_r[HW_ZERO_4:HW_ZERO_3]
    && tinfo_r[ETRIGGER]
    && tinfo_r[MCONTROL6]
    && !tinfo_r[HW_ZERO_14:HW_ZERO_7]
    && tinfo_r[DISABLED]
    && !tinfo_r[HW_ZERO_31:HW_ZERO_16]
  ) else `uvm_error(info_tag, "TODO!\n");

  //P37-P38: 2)
  //Verify that the WARL fields of the following CSR are as expected
  a_dt_warl_tselect: assert property (
    rvfi_if.rvfi_valid
    && |tselect.rvfi_csr_wmask != 0
    |->
    tselect_w < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS
    || tselect_w == '0 //(when there are no triggers)
  ) else `uvm_error(info_tag, "TODO!\n");

  a_dt_warl_tdata1_general: assert property (
    rvfi_if.rvfi_valid
    && |tdata1.rvfi_csr_wmask != 0
    |->
    (tdata1_w[MSB_TYPE:LSB_TYPE] == MCONTROL
    || tdata1_w[MSB_TYPE:LSB_TYPE] == ETRIGGER
    || tdata1_w[MSB_TYPE:LSB_TYPE] == MCONTROL6
    || tdata1_w[MSB_TYPE:LSB_TYPE] == DISABLED)
    && tdata1_w[DMODE]
  ) else `uvm_error(info_tag, "TODO!\n");

  a_dt_warl_tdata1_m2: assert property (
    rvfi_if.rvfi_valid
    && |tdata1.rvfi_csr_wmask != 0
    && tdata1_w[MSB_TYPE:LSB_TYPE] == MCONTROL
    |->
    !tdata1_w[MSB_MASKMAX:LSB_MASKMAX]
    && !tdata1_w[M2_HIT]
    && !tdata1_w[M2_SELECT]
    && !tdata1_w[M2_TIMING]
    && !tdata1_w[MSB_SIZELO:LSB_SIZELO]
    && tdata1_w[MSB_ACTION:LSB_ACTION] == ENTER_DBG_ON_MATCH
    && !tdata1_w[CHAIN]
    && (tdata1_w[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL
    || tdata1_w[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL
    || tdata1_w[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER)
    && !tdata1_w[HW_ZERO_5]
    && !tdata1_w[S_MODE]
  ) else `uvm_error(info_tag, "TODO!\n");

  a_dt_warl_tdata1_etrigger: assert property (
    rvfi_if.rvfi_valid
    && |tdata1.rvfi_csr_wmask != 0
    && tdata1_w[MSB_TYPE:LSB_TYPE] == ETRIGGER
    |->
    !tdata1_w[ET_HIT]
    && !tdata1_w[HW_ZERO_25:HW_ZERO_13]
    && !tdata1_w[ET_VS]
    && !tdata1_w[ET_VU]
    && !tdata1_w[HW_ZERO_10]
    && !tdata1_w[HW_ZERO_8]
    && !tdata1_w[ET_S]
    && tdata1_w[ET_MSB_ACTION:ET_LSB_ACTION] == ENTER_DBG_ON_MATCH
  ) else `uvm_error(info_tag, "TODO!\n");

  a_dt_warl_tdata1_m6: assert property (
    rvfi_if.rvfi_valid
    && |tdata1.rvfi_csr_wmask != 0
    && tdata1_w[MSB_TYPE:LSB_TYPE] == MCONTROL6
    |->
    !tdata1_w[HW_ZERO_26:HW_ZERO_25]
    && !tdata1_w[M6_VS]
    && !tdata1_w[M6_VU]
    && !tdata1_w[M6_HIT]
    && !tdata1_w[M6_SELECT]
    && !tdata1_w[M6_TIMING]
    && !tdata1_w[MSB_SIZE:LSB_SIZE]
    && tdata1_w[MSB_ACTION:LSB_ACTION] == ENTER_DBG_ON_MATCH
    && !tdata1_w[CHAIN]
    && (tdata1_w[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL
    || tdata1_w[MSB_MATCH:LSB_MATCH] ==  MATCH_WHEN_GREATER_OR_EQUAL
    || tdata1_w[MSB_MATCH:LSB_MATCH] ==  MATCH_WHEN_LESSER)
    && !tdata1_w[HW_ZERO_5]
    && !tdata1_w[S_MODE]
  ) else `uvm_error(info_tag, "TODO!\n");

  a_dt_warl_tdata1_disabled: assert property (
    rvfi_if.rvfi_valid
    && |tdata1.rvfi_csr_wmask != 0
    && tdata1_w[MSB_TYPE:LSB_TYPE] == DISABLED
    |->
    !tdata1_w[DIS_MSB_DATA:DIS_LSB_DATA]
  ) else `uvm_error(info_tag, "TODO!\n");

  a_dt_warl_tdata2_etrigger: assert property (
    rvfi_if.rvfi_valid
    && |tdata2.rvfi_csr_wmask != 0
    && tdata1_w[MSB_TYPE:LSB_TYPE] == ETRIGGER
    |->
    !tdata2_w[ET2_DATA_31:ET2_DATA_26]
    && !tdata2_w[ET2_DATA_23:ET2_DATA_12]
    && !tdata2_w[ET2_DATA_10:ET2_DATA_9]
    && !tdata2_w[ET2_DATA_6]
    && !tdata2_w[ET2_DATA_4]
    && !tdata2_w[ET2_DATA_0]
  ) else `uvm_error(info_tag, "TODO!\n");

  a_dt_warl_tdata3: assert property (
    rvfi_if.rvfi_valid
    && |tdata3.rvfi_csr_wmask != 0
    |->
    !tdata3_w
  ) else `uvm_error(info_tag, "TODO!\n");

  a_dt_warl_tinfo: assert property (
    rvfi_if.rvfi_valid
    && |tinfo.rvfi_csr_wmask != 0
    |->
    !tinfo_w[31:16]
  ) else `uvm_error(info_tag, "TODO!\n");

  a_dt_warl_tcontrol: assert property (
    rvfi_if.rvfi_valid
    && |tcontrol.rvfi_csr_wmask != 0
    |->
    !tcontrol_w[HW_ZERO_31:HW_ZERO_8]
    && !tcontrol_w[MPTE]
    && !tcontrol_w[HW_ZERO_6:HW_ZERO_4]
    && !tcontrol_w[MTE]
    && !tcontrol_w[HW_ZERO_2:HW_ZERO_0]
  ) else `uvm_error(info_tag, "TODO!\n");


  //The following assertions cover the verification tasks:
  //P12-P13: 1) 2)
  //P14-P15: 1)
  //P18-P19: 2)
  //P20-P21: 1) 2) 3)
  //P22-P23: 1)
  //P24-P25: 1) 2)
  //P26-P27: 1)
  //P37-P38: 1)

  //Abbreviations:
  //exe = execute
  //m = machine
  //u = user
  //eq = equal
  //geq = greater or equal
  //l = lesser
  //bX = byte number X

  //Execute:
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] exe_eq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] exe_eq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] exe_geq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] exe_geq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] exe_l_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] exe_l_u;

  //Load:
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b0_eq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b0_eq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b0_geq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b0_geq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b0_l_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b0_l_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b1_eq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b1_eq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b1_geq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b1_geq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b1_l_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b1_l_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b2_eq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b2_eq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b2_geq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b2_geq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b2_l_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b2_l_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b3_eq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b3_eq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b3_geq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b3_geq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b3_l_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] load_b3_l_u;

  //Store:
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b0_eq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b0_eq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b0_geq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b0_geq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b0_l_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b0_l_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b1_eq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b1_eq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b1_geq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b1_geq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b1_l_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b1_l_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b2_eq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b2_eq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b2_geq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b2_geq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b2_l_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b2_l_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b3_eq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b3_eq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b3_geq_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b3_geq_u;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b3_l_m;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM:0] store_b3_l_u;

  //Set all possible ways of entering debug mode due to trigger match:
  generate
    for (genvar t = 0; t < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS; t++) begin

      //Execute:
      assign exe_eq_m[t] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && (tdata1_arry[t][EXECUTE]) && (tdata1_arry[t][M_MODE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_pc_rdata == tdata2_arry[t]);
      assign exe_eq_u[t] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && (tdata1_arry[t][EXECUTE]) && (tdata1_arry[t][U_MODE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_pc_rdata == tdata2_arry[t]);

      assign exe_geq_m[t] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && (tdata1_arry[t][EXECUTE]) && (tdata1_arry[t][M_MODE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_pc_rdata >= tdata2_arry[t]);
      assign exe_geq_u[t] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && (tdata1_arry[t][EXECUTE]) && (tdata1_arry[t][U_MODE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_pc_rdata >= tdata2_arry[t]);

      assign exe_l_m[t] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && (tdata1_arry[t][EXECUTE]) && (tdata1_arry[t][M_MODE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_pc_rdata < tdata2_arry[t]);
      assign exe_l_u[t] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && (tdata1_arry[t][EXECUTE]) && (tdata1_arry[t][U_MODE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_pc_rdata < tdata2_arry[t]);

      //Make sure we check all possible memory entries:
      for (genvar m = 0; m < NMEM; m++) begin
        //Load:
        //Byte 0:

        assign load_b0_eq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32] == tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4];
        assign load_b0_eq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32] == tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4];

        assign load_b0_geq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32] >= tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4];
        assign load_b0_geq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32] >= tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4];

        assign load_b0_l_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32] < tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4];
        assign load_b0_l_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32] < tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4];

        //Byte +1:
        assign load_b1_eq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+1 == tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+1];
        assign load_b1_eq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+1 == tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+1];

        assign load_b1_geq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+1 >= tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+1];
        assign load_b1_geq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+1 >= tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+1];

        assign load_b1_l_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+1 < tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+1];
        assign load_b1_l_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+1 < tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+1];

        //Byte +2:
        assign load_b2_eq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+2 == tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+2];
        assign load_b2_eq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+2 == tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+2];

        assign load_b2_geq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+2 >= tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+2];
        assign load_b2_geq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+2 >= tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+2];

        assign load_b2_l_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+2 < tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+2];
        assign load_b2_l_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+2 < tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+2];

        //Byte +3:
        assign load_b3_eq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+3 == tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+3];
        assign load_b3_eq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+3 == tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+3];

        assign load_b3_geq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+3 >= tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+3];
        assign load_b3_geq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+3 >= tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+3];

        assign load_b3_l_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+3 < tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+3];
        assign load_b3_l_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][LOAD] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+3 < tdata2_arry[t]) && rvfi_if.rvfi_mem_rmask[m*4+3];

        //Store:
        //Byte 0:
        assign store_b0_eq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32] == tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4];
        assign store_b0_eq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32] == tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4];

        assign store_b0_geq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32] >= tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4];
        assign store_b0_geq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32] >= tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4];

        assign store_b0_l_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32] < tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4];
        assign store_b0_l_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32] < tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4];

        //Byte +1:
        assign store_b1_eq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+1 == tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+1];
        assign store_b1_eq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+1 == tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+1];

        assign store_b1_geq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+1 >= tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+1];
        assign store_b1_geq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+1 >= tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+1];

        assign store_b1_l_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+1 < tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+1];
        assign store_b1_l_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+1 < tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+1];

        //Byte +2:
        assign store_b2_eq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+2 == tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+2];
        assign store_b2_eq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+2 == tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+2];

        assign store_b2_geq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+2 >= tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+2];
        assign store_b2_geq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+2 >= tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+2];

        assign store_b2_l_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+2 < tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+2];
        assign store_b2_l_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+2 < tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+2];

        //Byte +3:
        assign store_b3_eq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+3 == tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+3];
        assign store_b3_eq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+3 == tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+3];

        assign store_b3_geq_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+3 >= tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+3];
        assign store_b3_geq_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+3 >= tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+3];

        assign store_b3_l_m[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][M_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_M) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+3 < tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+3];
        assign store_b3_l_u[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == MCONTROL6)) && tdata1_arry[t][STORE] && tdata1_arry[t][U_MODE] && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (rvfi_if.rvfi_mode == CORE_MODE_U) && (rvfi_if.rvfi_mem_addr[m*32+31:m*32]+3 < tdata2_arry[t]) && rvfi_if.rvfi_mem_wmask[m*4+3];
      end
    end
  endgenerate

  property p_exe_enter_debug_due_to_x(x);
    //Enter debug mode due to situation <x>
    |x
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode

    //Check out the next valid instruction
    ##1 rvfi_if.rvfi_valid[->1]

    |->
    //Verify that the next instruction is executed from the debug handler
    rvfi_if.rvfi_dbg_mode;
  endproperty


  property p_load_enter_debug_due_to_x(x);
    //Enter debug mode due to a load operation accessing a matching address in situation <x>
    |x
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode
    && |rvfi_if.rvfi_mem_rmask

    //Make sure the exception does not affect the core's behavior
    && !rvfi_if.rvfi_trap.exception

    //Check out the next valid instruction
    ##1 rvfi_if.rvfi_valid[->1]

    |->
    //Verify that the next instruction is executed from the debug handler
    rvfi_if.rvfi_dbg_mode;
  endproperty


  property p_store_enter_debug_due_to_x(x);
    //Enter debug mode due to a store operation accessing a matching address in situation <x>
    |x
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode
    && |rvfi_if.rvfi_mem_wmask

    //Make sure the exception does not affect the core's behavior
    && !rvfi_if.rvfi_trap.exception

    //Check out the next valid instruction
    ##1 rvfi_if.rvfi_valid[->1]

    |->
    //Verify that the next instruction is executed from the debug handler
    rvfi_if.rvfi_dbg_mode;
  endproperty


  generate
    for (genvar t = 0; t < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS; t++) begin

      //Verify that we enter debug mode when <x> occurs, for both address and memory matching:

      a_dt_enter_dbg_exe: assert property(

        p_exe_enter_debug_due_to_x(exe_eq_m[t])
        and p_exe_enter_debug_due_to_x(exe_eq_u[t])

        and p_exe_enter_debug_due_to_x(exe_geq_m[t])
        and p_exe_enter_debug_due_to_x(exe_geq_u[t])

        and p_exe_enter_debug_due_to_x(exe_l_m[t])
        and p_exe_enter_debug_due_to_x(exe_l_u[t])
      ) else `uvm_error(info_tag, "TODO!\n");

      a_dt_enter_dbg_load: assert property(

        //Byte 0:
        p_load_enter_debug_due_to_x(load_b0_eq_m[t])
        and p_load_enter_debug_due_to_x(load_b0_eq_u[t])

        and p_load_enter_debug_due_to_x(load_b0_geq_m[t])
        and p_load_enter_debug_due_to_x(load_b0_geq_u[t])

        and p_load_enter_debug_due_to_x(load_b0_l_m[t])
        and p_load_enter_debug_due_to_x(load_b0_l_u[t])

        //Byte +1:
        and p_load_enter_debug_due_to_x(load_b1_eq_m[t])
        and p_load_enter_debug_due_to_x(load_b1_eq_u[t])

        and p_load_enter_debug_due_to_x(load_b1_geq_m[t])
        and p_load_enter_debug_due_to_x(load_b1_geq_u[t])

        and p_load_enter_debug_due_to_x(load_b1_l_m[t])
        and p_load_enter_debug_due_to_x(load_b1_l_u[t])

        //Byte +2:
        and p_load_enter_debug_due_to_x(load_b2_eq_m[t])
        and p_load_enter_debug_due_to_x(load_b2_eq_u[t])

        and p_load_enter_debug_due_to_x(load_b2_geq_m[t])
        and p_load_enter_debug_due_to_x(load_b2_geq_u[t])

        and p_load_enter_debug_due_to_x(load_b2_l_m[t])
        and p_load_enter_debug_due_to_x(load_b2_l_u[t])

        //Byte +3:
        and p_load_enter_debug_due_to_x(load_b3_eq_m[t])
        and p_load_enter_debug_due_to_x(load_b3_eq_u[t])

        and p_load_enter_debug_due_to_x(load_b3_geq_m[t])
        and p_load_enter_debug_due_to_x(load_b3_geq_u[t])

        and p_load_enter_debug_due_to_x(load_b3_l_m[t])
        and p_load_enter_debug_due_to_x(load_b3_l_u[t])

      ) else `uvm_error(info_tag, "TODO!\n");

      a_dt_enter_dbg_store: assert property(

        //Byte 0:
        p_store_enter_debug_due_to_x(store_b0_eq_m[t])
        and p_store_enter_debug_due_to_x(store_b0_eq_u[t])

        and p_store_enter_debug_due_to_x(store_b0_geq_m[t])
        and p_store_enter_debug_due_to_x(store_b0_geq_u[t])

        and p_store_enter_debug_due_to_x(store_b0_l_m[t])
        and p_store_enter_debug_due_to_x(store_b0_l_u[t])

        //Byte +1:
        and p_store_enter_debug_due_to_x(store_b1_eq_m[t])
        and p_store_enter_debug_due_to_x(store_b1_eq_u[t])

        and p_store_enter_debug_due_to_x(store_b1_geq_m[t])
        and p_store_enter_debug_due_to_x(store_b1_geq_u[t])

        and p_store_enter_debug_due_to_x(store_b1_l_m[t])
        and p_store_enter_debug_due_to_x(store_b1_l_u[t])

        //Byte +2:
        and p_store_enter_debug_due_to_x(store_b2_eq_m[t])
        and p_store_enter_debug_due_to_x(store_b2_eq_u[t])

        and p_store_enter_debug_due_to_x(store_b2_geq_m[t])
        and p_store_enter_debug_due_to_x(store_b2_geq_u[t])

        and p_store_enter_debug_due_to_x(store_b2_l_m[t])
        and p_store_enter_debug_due_to_x(store_b2_l_u[t])

        //Byte +3:
        and p_store_enter_debug_due_to_x(store_b3_eq_m[t])
        and p_store_enter_debug_due_to_x(store_b3_eq_u[t])

        and p_store_enter_debug_due_to_x(store_b3_geq_m[t])
        and p_store_enter_debug_due_to_x(store_b3_geq_u[t])

        and p_store_enter_debug_due_to_x(store_b3_l_m[t])
        and p_store_enter_debug_due_to_x(load_b3_l_u[t])

      ) else `uvm_error(info_tag, "TODO!\n");

    end
  endgenerate


  a_dt_enter_dbg_reason: assert property (
    //Make sure we enter debug mode due to a trigger match
    rvfi_if.rvfi_valid
    && rvfi_if.rvfi_trap.debug
    && rvfi_if.rvfi_trap.debug_cause == TRIGGER_MATCH

    |->
    //Verify that we do not enter debug mode due to triggers unless either of these situations occurs:
    |exe_eq_m
    || |exe_eq_u
    || |exe_geq_m
    || |exe_geq_u
    || |exe_l_m
    || |exe_l_u
    || |load_b0_eq_m
    || |load_b0_eq_u
    || |load_b0_geq_m
    || |load_b0_geq_u
    || |load_b0_l_m
    || |load_b0_l_u
    || |load_b1_eq_m
    || |load_b1_eq_u
    || |load_b1_geq_m
    || |load_b1_geq_u
    || |load_b1_l_m
    || |load_b1_l_u
    || |load_b2_eq_m
    || |load_b2_eq_u
    || |load_b2_geq_m
    || |load_b2_geq_u
    || |load_b2_l_m
    || |load_b2_l_u
    || |load_b3_eq_m
    || |load_b3_eq_u
    || |load_b3_geq_m
    || |load_b3_geq_u
    || |load_b3_l_m
    || |load_b3_l_u
    || |store_b0_eq_m
    || |store_b0_eq_u
    || |store_b0_geq_m
    || |store_b0_geq_u
    || |store_b0_l_m
    || |store_b0_l_u
    || |store_b1_eq_m
    || |store_b1_eq_u
    || |store_b1_geq_m
    || |store_b1_geq_u
    || |store_b1_l_m
    || |store_b1_l_u
    || |store_b2_eq_m
    || |store_b2_eq_u
    || |store_b2_geq_m
    || |store_b2_geq_u
    || |store_b2_l_m
    || |store_b2_l_u
    || |store_b3_eq_m
    || |store_b3_eq_u
    || |store_b3_geq_m
    || |store_b3_geq_u
    || |store_b3_l_m
    || |store_b3_l_u
  ) else `uvm_error(info_tag, "TODO!\n");

endmodule : uvmt_cv32e40s_triggers_assert_cov

