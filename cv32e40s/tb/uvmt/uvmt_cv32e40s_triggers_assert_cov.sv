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
    input logic wb_valid,
    input logic [5:0] wb_exception_code,
    input logic [31:0] wb_tdata1,
    input logic [31:0] wb_tdata2,
    input logic [31:0] wb_tselect,
    input privlvl_t priv_lvl,
    input logic wb_dbg_mode,
    input logic wb_last_op,
    input logic wb_exception,

    uvma_rvfi_instr_if rvfi_if,
    uvma_clknrst_if clknrst_if,

    uvma_rvfi_csr_if tdata1,
    uvma_rvfi_csr_if tdata2,
    uvma_rvfi_csr_if tdata3,
    uvma_rvfi_csr_if tinfo,
    uvma_rvfi_csr_if tselect,
    uvma_rvfi_csr_if tcontrol
  );

  default clocking @(posedge clknrst_if.clk); endclocking
  default disable iff !(clknrst_if.reset_n);

  string info_tag = "TRIGGER ASSERT: ";

  //Reads and writes of CSR values
  logic [31:0] tdata1_r;
  logic [31:0] tdata2_r;
  logic [31:0] tdata3_r;
  logic [31:0] tinfo_r;
  logic [31:0] tselect_r;
  logic [31:0] tcontrol_r;

  logic [31:0] tdata1_w;
  logic [31:0] tdata2_w;
  logic [31:0] tdata3_w;
  logic [31:0] tinfo_w;
  logic [31:0] tselect_w;
  logic [31:0] tcontrol_w;

  assign tdata1_r = tdata1.read();
  assign tdata2_r = tdata2.read();
  assign tdata3_r = tdata3.read();
  assign tinfo_r = tinfo.read();
  assign tselect_r = tselect.read();
  assign tcontrol_r = tcontrol.read();

  assign tdata1_w = tdata1.write();
  assign tdata2_w = tdata2.write();
  assign tdata3_w = tdata3.write();
  assign tinfo_w = tinfo.write();
  assign tselect_w = tselect.write();
  assign tcontrol_w = tcontrol.write();

  //Local parameters:

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
  localparam M2_MSB_SIZELO = 17;
  localparam M2_LSB_SIZELO = 16;

  //tdata1 mcontrol6:
  localparam M6_VS = 24;
  localparam M6_VU = 23;
  localparam M6_HIT = 22;
  localparam M6_SELECT = 21;
  localparam M6_TIMING = 20;
  localparam M6_MSB_SIZE = 19;
  localparam M6_LSB_SIZE = 16;

  //tdata1 etriggers:
  localparam ET_HIT = 26;
  localparam ET_VS = 12;
  localparam ET_VU = 11;
  localparam ET_M_MODE = 9;
  localparam ET_S = 7;
  localparam ET_U_MODE = 6;
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

  //Cause of entering debug:
  localparam TRIGGER_MATCH = 2;

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

    end else if (wb_valid) begin
      case(wb_tselect)
        32'h0:
          begin
            tdata1_arry[0] = wb_tdata1;
            tdata2_arry[0] = wb_tdata2;
          end
        32'h1:
          begin
            tdata1_arry[1] = wb_tdata1;
            tdata2_arry[1] = wb_tdata2;
          end
        32'h2:
          begin
            tdata1_arry[2] = wb_tdata1;
            tdata2_arry[2] = wb_tdata2;
          end
        32'h3:
          begin
            tdata1_arry[3] = wb_tdata1;
            tdata2_arry[3] = wb_tdata2;
          end
      endcase
    end
  end

/*
- Vplan:
Verify that core enters debug mode when the trigger matches on instruction address. NB! According to spec, the tdataN registers can only be written from debug mode, as m-mode writes are ignored.

Enter debug mode by any of the above methods.
Write (randomized) breakpoint addr to tdata2 and enable breakpoint in tdata1[2]
Exit debug mode (dret instruction)
Verify that core enters debug mode on breakpoint addr
Current PC is saved to DPC
Cause of debug must be saved to DCSR (cause=2)
PC is updated to value on dm_haltaddr_i input
Core starts executing debug code

- Assertion verifikasjon:
1) Verify that core enters debug mode when the trigger matches on instruction address
2) Verify that core enters debug mode on breakpoint addr
3) Current PC is saved to DPC
4) Cause of debug must be saved to DCSR (cause=2)
5) PC is updated to value on dm_haltaddr_i input
6) Core starts executing debug code
*/

//1) & 2) see a_dt_enter_dbg_*
//3) - 6): Debug assertions uvmt_cv32e40s_debug_assert.sv

/*
- Vplan:
Have 0 triggers, access any trigger register and check that illegal instruction exception occurs.
Check that no triggers ever fire. Check that "tselect" is 0.

- Assertion verifikasjon:
1) Have 0 triggers, access any trigger register and check that illegal instruction exception occurs
2) Have 0 triggers, No trigger ever fires
3) Have 0 triggers, tselect is 0
*/

  //1)
  a_dt_0_triggers_tdata1_access: assert property (
    uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS == '0

    && (rvfi_if.is_csr_instr(ADDR_TSELECT)
    || rvfi_if.is_csr_instr(ADDR_TDATA1)
    || rvfi_if.is_csr_instr(ADDR_TDATA2)
    || rvfi_if.is_csr_instr(ADDR_TDATA3)
    || rvfi_if.is_csr_instr(ADDR_TINFO)
    || rvfi_if.is_csr_instr(ADDR_TCONTROL))

    |->
    rvfi_if.rvfi_trap.trap
    && rvfi_if.rvfi_trap.exception
    && (rvfi_if.rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)

  ) else `uvm_error(info_tag, "There are no triggers, but accessing trigger SCRs does not cause exceptions.\n");

  //2)
  a_dt_0_triggers_no_triggering: assert property (
    uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS == '0
    && rvfi_if.rvfi_valid
    |->
    rvfi_if.rvfi_dbg != TRIGGER_MATCH

  ) else `uvm_error(info_tag, "There are no triggers, but debug cause indicate a trigger match.\n");

  //3)
  a_dt_0_triggers_tselect_is_0: assert property (
    uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS == '0
    && rvfi_if.rvfi_valid
    |->
    !tselect_r

  ) else `uvm_error(info_tag, "There are no triggers, but tselect is not set to zero.\n");


  /*
- Vplan:
For all number of triggers, use tselect to exercise each trigger with each supported type.
(Also try writing to higher "tselect" than supported and check that a supported number is read back.)
Make the triggers fire and check that debug mode is entered. Check also that the four context registers trap when accessed.

- Assertion verifikasjon:
1) For all number of triggers, use tselect to exercise each trigger with each supported type
2) Make the triggers fire and check that debug mode is entered.
3) Writing to higher "tselect" than supported, check that a supported number is read back
4) Check also that the four context registers trap when accessed.

  */

  //1)
  property p_all_trigger(tselect_trigger_i, tdata1_type);
    tselect_r == tselect_trigger_i
    && tdata1_r[MSB_TYPE:LSB_TYPE] == tdata1_type;
  endproperty

  generate
    for (genvar tselect_trigger_i = 0; tselect_trigger_i < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS; tselect_trigger_i++) begin

      c_trigger_i_has_type_mcontrol: cover property(
        p_all_trigger(tselect_trigger_i, TTYPE_MCONTROL)
      );

      c_trigger_i_has_type_etrigger: cover property(
        p_all_trigger(tselect_trigger_i, TTYPE_ETRIGGER)
      );

      c_trigger_i_has_type_mcontrol6: cover property(
        p_all_trigger(tselect_trigger_i, TTYPE_MCONTROL6)
      );

      c_trigger_i_has_type_disable: cover property(
        p_all_trigger(tselect_trigger_i, TTYPE_DISABLED)
      );

    end
  endgenerate

  //2) see a_dt_enter_dbg_*

  //3)
  a_dt_tselect_higher_than_dbg_num_triggers: assert property(
    rvfi_if.is_csr_instr(ADDR_TSELECT)
    |->
    rvfi_if.rvfi_rd1_wdata < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS
  ) else `uvm_error(info_tag, "The CSR tselect is set to equal or higher than the number of trigger.\n");

  //4)
  a_dt_access_context: assert property (
    (rvfi_if.is_csr_instr(ADDR_MCONTEXT)
    || rvfi_if.is_csr_instr(ADDR_MSCONTEXT)
    || rvfi_if.is_csr_instr(ADDR_HCONTEXT)
    || rvfi_if.is_csr_instr(ADDR_SCONTEXT))

    |->
    rvfi_if.rvfi_trap.trap
  ) else `uvm_error(info_tag, "Accessing context registers does not trap.\n");


/*
- Vplan:
Configure triggers for load/store/execute and combinations of them, configure tdata2,
cause triggers to fire and check that debug mode is entered correctly.
Also check that the tied fields are tied. All of these configurations must be crossed, also against match conditions.

- Assertion verifikasjon:
1) Hvis load er høy, sørg for at man trigger riktig dersom man har load operasjon
2) Hvis store er høy, sørg for at man trigger riktig dersom man har store operasjon
3) Hvis execute er høy, sørg for at man trigger riktig dersom man har execute operasjon
4) check that the tied fields are tied
*/

  //1) - 3) see a_dt_enter_dbg_*

  //4)
  //mcontrol
  a_dt_tie_offs_tdata1_mcontrol: assert property (
    rvfi_if.rvfi_valid
    && tdata1_r[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL

    |->
    tdata1_r[DMODE]
    && !tdata1_r[MSB_MASKMAX:LSB_MASKMAX]
    && !tdata1_r[M2_HIT]
    && !tdata1_r[M2_SELECT]
    && !tdata1_r[M2_TIMING]
    && !tdata1_r[M2_MSB_SIZELO:M2_LSB_SIZELO]
    && tdata1_r[MSB_ACTION:LSB_ACTION] == ENTER_DBG_ON_MATCH
    && !tdata1_r[CHAIN]
    && !tdata1_r[HW_ZERO_5]
    && !tdata1_r[S_MODE]
  ) else `uvm_error(info_tag, "There is a problem with tdata1-mcontrol's tied off fields.\n");

  //etrigger
  a_dt_tie_offs_tdata1_etrigger: assert property (
    rvfi_if.rvfi_valid
    && tdata1_r[MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER

    |->
    tdata1_r[DMODE]
    && !tdata1_r[ET_HIT]
    && !tdata1_r[HW_ZERO_25:HW_ZERO_13]
    && !tdata1_r[ET_VS]
    && !tdata1_r[ET_VU]
    && !tdata1_r[HW_ZERO_10]
    && !tdata1_r[HW_ZERO_8]
    && !tdata1_r[ET_S]
    && tdata1_r[ET_MSB_ACTION:ET_LSB_ACTION] == ENTER_DBG_ON_MATCH
  ) else `uvm_error(info_tag, "There is a problem with tdata1-etrigger's tied off fields.\n");

  //mcontrol6
  a_dt_tie_offs_tdata1_mcontrol6: assert property (
    rvfi_if.rvfi_valid
    && tdata1_r[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6

    |->
    tdata1_r[DMODE]
    && !tdata1_r[HW_ZERO_26:HW_ZERO_25]
    && !tdata1_r[M6_VS]
    && !tdata1_r[M6_VU]
    && !tdata1_r[M6_HIT]
    && !tdata1_r[M6_SELECT]
    && !tdata1_r[M6_TIMING]
    && !tdata1_r[M6_MSB_SIZE:M6_LSB_SIZE]
    && tdata1_r[MSB_ACTION:LSB_ACTION] == ENTER_DBG_ON_MATCH
    && !tdata1_r[CHAIN]
    && !tdata1_r[HW_ZERO_5]
    && !tdata1_r[S_MODE]
  ) else `uvm_error(info_tag, "There is a problem with tdata1-mcontrol6's tied off fields.\n");

  //disabled
  a_dt_tie_offs_tdata1_disabled: assert property (
    rvfi_if.rvfi_valid
    && tdata1_r[MSB_TYPE:LSB_TYPE] == TTYPE_DISABLED

    |->
    tdata1_r[DMODE]
    && !tdata1_r[DIS_MSB_DATA:DIS_LSB_DATA]
  ) else `uvm_error(info_tag, "There is a problem with tdata1-disabled's tied off fields.\n");

  a_dt_tie_offs_tdata3: assert property (
    rvfi_if.rvfi_valid
    |->
    !tdata3_r
  ) else `uvm_error(info_tag, "There is a problem with tdata3's tied off fields.\n");

  a_dt_tie_offs_tinfo: assert property (
    rvfi_if.rvfi_valid
    |->
    !tinfo_r[HW_ZERO_31:HW_ZERO_16]
  ) else `uvm_error(info_tag, "There is a problem with tinfo's tied off fields.\n");

  a_dt_tie_offs_tcontrol: assert property (
    rvfi_if.rvfi_valid
    |->
    !tcontrol_r[HW_ZERO_31:HW_ZERO_8]
    && !tcontrol_r[HW_ZERO_6:HW_ZERO_4]
    && !tcontrol_r[HW_ZERO_2:HW_ZERO_0]
  ) else `uvm_error(info_tag, "There is a problem with tcontrol's tied off fields.\n");

/*
- Vplan:
Have triggers configured to be able to match, but enable/disable their corresponding mode bit, check that the trigger is either able to fire or is blocked from firing accordingly. Also check the tied values.

- Assertion verifikasjon:
1) but enable/disable their corresponding mode bit, check that the trigger is either able to fire or is blocked from firing accordingly, using different match configurations.
2) Also check the tied values. (P20-P21: 4))
*/

  //1) see a_dt_enter_dbg_*
  //2) see a_dt_tie_offs_*

/*
- Vplan:
Check that these types can be selected, and check that no other types can be selected. (Functionality of these types should be handled by other items in this plan.) Check also that the default is "15".

- Assertion verifikasjon:
1) Sjekk at tdata1 type kun kan være 2, 6, 5 eller 15
*/

  //1)
  a_dt_tdata1_types: assert property (
    rvfi_if.rvfi_valid
    |->
    tdata1_r[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL
    || tdata1_r[MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER
    || tdata1_r[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6
    || tdata1_r[MSB_TYPE:LSB_TYPE] == TTYPE_DISABLED
  ) else `uvm_error(info_tag, "tdata1 type is neither mcontrol, etrigger, mcontrol6 or disabled.\n");

/*
- Vplan:
Try to write tdata registers outside of debug mode, check that it traps. Try changing "tdata1.dmode" and check that it is WARL (0x1). Cross the above checks with all supported types.

- Assertion verifikasjon:
1) write tdata registers outside of debug mode, check that it traps. This verification point is wrong, see https://github.com/openhwgroup/core-v-verif/issues/1664
2) Try changing "tdata1.dmode" and check that it is WARL (0x1)
*/

  //1)
  a_dt_access_csr_not_dbg_mode: assert property (
    !rvfi_if.rvfi_dbg_mode
    && (rvfi_if.is_csr_instr(ADDR_TDATA1)
    || rvfi_if.is_csr_instr(ADDR_TDATA2)
    || rvfi_if.is_csr_instr(ADDR_TDATA3))

    |->
    !tdata1.rvfi_csr_wmask
    && !tdata2.rvfi_csr_wmask
    && !tdata3.rvfi_csr_wmask
  ) else `uvm_error(info_tag, "Writing tdata1, tdata2 or tdata3 in non-debug mode succeeds.\n");

  //2)
  a_dt_dmode: assert property (
    rvfi_if.rvfi_valid
    && rvfi_if.rvfi_dbg_mode
    && !rvfi_if.rvfi_trap.trap
    && tdata1.rvfi_csr_wmask[DMODE]

    |->
    tdata1_w[DMODE]
  ) else `uvm_error(info_tag, "Setting tdata1's dmode bit to 0 succeeds.\n");

/*
- Vplan:
When num triggers is 0, check that "tinfo" is 0.
For any other num triggers, check that "tinfo.info" is "1" for the three supported types, and that the remaining bits are 0.

- Assertion verifikasjon:
1) When num triggers is 0, check that "tinfo" is 0.
2) For any other num triggers, check that "tinfo.info" is "1" for the three supported types, and that the remaining bits are 0.
*/

  //1)
  a_dt_0_triggers_tinfo: assert property (
    uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS == '0
    && rvfi_if.rvfi_valid
    |->
    !tinfo_r
  ) else `uvm_error(info_tag, "There are no triggers, but tinfo is not set to zero.\n");

  //2)
  a_dt_triggers_tinfo: assert property (
    uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS != '0
    && rvfi_if.rvfi_valid
    |->
    !tinfo_r[HW_ZERO_1:HW_ZERO_0]
    && tinfo_r[TTYPE_MCONTROL]
    && !tinfo_r[HW_ZERO_4:HW_ZERO_3]
    && tinfo_r[TTYPE_ETRIGGER]
    && tinfo_r[TTYPE_MCONTROL6]
    && !tinfo_r[HW_ZERO_14:HW_ZERO_7]
    && tinfo_r[TTYPE_DISABLED]
    && !tinfo_r[HW_ZERO_31:HW_ZERO_16]
  ) else `uvm_error(info_tag, "tinfo does not indicated that only tdata type mcontrol, etrigger, mcontrol6 and disabled are allowed.\n");

/*
- Vplan: Etrigger!!
Configure "tdata1" and "tdata2" to fire on exceptions, try both individual and multiple exceptions in addition to supported and unsupported. Exercise scenarios that would trigger or not trigger according to the configuration and check that debug mode is either entered or not entered accordingly, and that the entry goes correctly (pc, dpc, cause, etc).

- Assertion verifikasjon:
1) Verify that we enter debug when triggering the enabled exceptions
2) Verify that we do not enter debug when triggering unenabled exceptions
*/

//1)
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] instr_access_fault_m_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] instr_access_fault_u_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] illegal_instr_m_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] illegal_instr_u_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] breakpoint_m_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] breakpoint_u_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] load_access_fault_m_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] load_access_fault_u_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] store_AMO_access_fault_m_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] store_AMO_access_fault_u_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] uecall_m_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] uecall_u_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] mecall_m_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] mecall_u_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] instr_bus_fault_m_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] instr_bus_fault_u_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] instr_integrity_fault_m_hit;
logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] instr_integrity_fault_u_hit;


  function logic set_tdatas_etrigger_state(int tdata_nr, int priv_lvl, logic [10:0] exception_cause); //TODO: funksjoner fungerer ikke...
    set_tdatas_etrigger_state = (tdata1_arry[tdata_nr][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER)
      && tdata1_arry[tdata_nr][priv_lvl]
      && tdata2_arry[tdata_nr][exception_cause];
  endfunction

  function logic wb_is_mmode();
    wb_is_mmode = wb_valid
      && (priv_lvl == PRIV_LVL_M);
  endfunction

  function logic wb_is_umode();
    wb_is_umode = wb_valid
      && (priv_lvl == PRIV_LVL_U);
  endfunction

  function logic wb_is_exception(logic [10:0] cause);
    wb_is_exception = wb_valid
      && (wb_exception)
      && (wb_exception_code == cause);
  endfunction


  generate
    for (genvar t = 0; t < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS; t++) begin
      //assign instr_access_fault_m_hit[t]     = (wb_is_mmode() && set_tdatas_etrigger_state(t, ET_M_MODE, EXC_CAUSE_INSTR_FAULT) && wb_is_exception(EXC_CAUSE_INSTR_FAULT));
      assign instr_access_fault_m_hit[t]     = (priv_lvl == PRIV_LVL_M) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_M_MODE]) && (tdata2_arry[t][EXC_CAUSE_INSTR_FAULT]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_INSTR_FAULT);
      //assign instr_access_fault_u_hit[t]     = wb_is_umode() && set_tdatas_etrigger_state(t, ET_U_MODE, EXC_CAUSE_INSTR_FAULT) && wb_is_exception(EXC_CAUSE_INSTR_FAULT);
      assign instr_access_fault_u_hit[t]     = (priv_lvl == PRIV_LVL_U) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_U_MODE]) && (tdata2_arry[t][EXC_CAUSE_INSTR_FAULT]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_INSTR_FAULT);
      //assign illegal_instr_m_hit[t]          = wb_is_mmode() && set_tdatas_etrigger_state(t, ET_M_MODE, EXC_CAUSE_ILLEGAL_INSN) && wb_is_exception(EXC_CAUSE_ILLEGAL_INSN);
      assign illegal_instr_m_hit[t]          = (priv_lvl == PRIV_LVL_M) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_M_MODE]) && (tdata2_arry[t][EXC_CAUSE_ILLEGAL_INSN]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_ILLEGAL_INSN);
      //assign illegal_instr_u_hit[t]          = wb_is_umode() && set_tdatas_etrigger_state(t, ET_U_MODE, EXC_CAUSE_ILLEGAL_INSN) && wb_is_exception(EXC_CAUSE_ILLEGAL_INSN);
      assign illegal_instr_u_hit[t]          = (priv_lvl == PRIV_LVL_U) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_U_MODE]) && (tdata2_arry[t][EXC_CAUSE_ILLEGAL_INSN]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_ILLEGAL_INSN);
      //assign breakpoint_m_hit[t]             = wb_is_mmode() && set_tdatas_etrigger_state(t, ET_M_MODE, EXC_CAUSE_BREAKPOINT) && wb_is_exception(EXC_CAUSE_BREAKPOINT);
      assign breakpoint_m_hit[t]             = (priv_lvl == PRIV_LVL_M) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_M_MODE]) && (tdata2_arry[t][EXC_CAUSE_BREAKPOINT]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_BREAKPOINT);
      //assign breakpoint_u_hit[t]             = wb_is_umode() && set_tdatas_etrigger_state(t, ET_U_MODE, EXC_CAUSE_BREAKPOINT) && wb_is_exception(EXC_CAUSE_BREAKPOINT);
      assign breakpoint_u_hit[t]             = (priv_lvl == PRIV_LVL_U) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_U_MODE]) && (tdata2_arry[t][EXC_CAUSE_BREAKPOINT]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_BREAKPOINT);
      //assign load_access_fault_m_hit[t]      = wb_is_mmode() && set_tdatas_etrigger_state(t, ET_M_MODE, EXC_CAUSE_LOAD_FAULT) && wb_is_exception(EXC_CAUSE_LOAD_FAULT);
      assign load_access_fault_m_hit[t]      = (priv_lvl == PRIV_LVL_M) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_M_MODE]) && (tdata2_arry[t][EXC_CAUSE_LOAD_FAULT]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_LOAD_FAULT);
      //assign load_access_fault_u_hit[t]      = wb_is_umode() && set_tdatas_etrigger_state(t, ET_U_MODE, EXC_CAUSE_LOAD_FAULT) && wb_is_exception(EXC_CAUSE_LOAD_FAULT);
      assign load_access_fault_u_hit[t]      = (priv_lvl == PRIV_LVL_U) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_U_MODE]) && (tdata2_arry[t][EXC_CAUSE_LOAD_FAULT]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_LOAD_FAULT);
      //assign store_AMO_access_fault_m_hit[t] = wb_is_mmode() && set_tdatas_etrigger_state(t, ET_M_MODE, EXC_CAUSE_STORE_FAULT) && wb_is_exception(EXC_CAUSE_STORE_FAULT);
      assign store_AMO_access_fault_m_hit[t] = (priv_lvl == PRIV_LVL_M) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_M_MODE]) && (tdata2_arry[t][EXC_CAUSE_STORE_FAULT]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_STORE_FAULT);
      //assign store_AMO_access_fault_u_hit[t] = wb_is_umode() && set_tdatas_etrigger_state(t, ET_U_MODE, EXC_CAUSE_STORE_FAULT) && wb_is_exception(EXC_CAUSE_STORE_FAULT);
      assign store_AMO_access_fault_u_hit[t] = (priv_lvl == PRIV_LVL_U) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_U_MODE]) && (tdata2_arry[t][EXC_CAUSE_STORE_FAULT]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_STORE_FAULT);
      //assign uecall_m_hit[t]                 = wb_is_mmode() && set_tdatas_etrigger_state(t, ET_M_MODE, EXC_CAUSE_ECALL_UMODE) && wb_is_exception(EXC_CAUSE_ECALL_UMODE);
      assign uecall_m_hit[t]                 = (priv_lvl == PRIV_LVL_M) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_M_MODE]) && (tdata2_arry[t][EXC_CAUSE_ECALL_UMODE]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_ECALL_UMODE);
      //assign uecall_u_hit[t]                 = wb_is_umode() && set_tdatas_etrigger_state(t, ET_U_MODE, EXC_CAUSE_ECALL_UMODE) && wb_is_exception(EXC_CAUSE_ECALL_UMODE);
      assign uecall_u_hit[t]                 = (priv_lvl == PRIV_LVL_U) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_U_MODE]) && (tdata2_arry[t][EXC_CAUSE_ECALL_UMODE]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_ECALL_UMODE);
      //assign mecall_m_hit[t]                 = wb_is_mmode() && set_tdatas_etrigger_state(t, ET_M_MODE, EXC_CAUSE_ECALL_MMODE) && wb_is_exception(EXC_CAUSE_ECALL_MMODE);
      assign mecall_m_hit[t]                 = (priv_lvl == PRIV_LVL_M) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_M_MODE]) && (tdata2_arry[t][EXC_CAUSE_ECALL_MMODE]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_ECALL_MMODE);
      //assign mecall_u_hit[t]                 = wb_is_umode() && set_tdatas_etrigger_state(t, ET_U_MODE, EXC_CAUSE_ECALL_MMODE) && wb_is_exception(EXC_CAUSE_ECALL_MMODE);
      assign mecall_u_hit[t]                 = (priv_lvl == PRIV_LVL_U) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_U_MODE]) && (tdata2_arry[t][EXC_CAUSE_ECALL_MMODE]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_ECALL_MMODE);
      //assign instr_bus_fault_m_hit[t]        = wb_is_mmode() && set_tdatas_etrigger_state(t, ET_M_MODE, EXC_CAUSE_INSTR_BUS_FAULT) && wb_is_exception(EXC_CAUSE_INSTR_BUS_FAULT);
      assign instr_bus_fault_m_hit[t]        = (priv_lvl == PRIV_LVL_M) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_M_MODE]) && (tdata2_arry[t][EXC_CAUSE_INSTR_BUS_FAULT]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_INSTR_BUS_FAULT);
      //assign instr_bus_fault_u_hit[t]        = wb_is_umode() && set_tdatas_etrigger_state(t, ET_U_MODE, EXC_CAUSE_INSTR_BUS_FAULT) && wb_is_exception(EXC_CAUSE_INSTR_BUS_FAULT);
      assign instr_bus_fault_u_hit[t]        = (priv_lvl == PRIV_LVL_U) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_U_MODE]) && (tdata2_arry[t][EXC_CAUSE_INSTR_BUS_FAULT]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_INSTR_BUS_FAULT);
      //assign instr_integrity_fault_m_hit[t]  = wb_is_mmode() && set_tdatas_etrigger_state(t, ET_M_MODE, EXC_CAUSE_INSTR_INTEGRITY_FAULT) && wb_is_exception(EXC_CAUSE_INSTR_INTEGRITY_FAULT);
      assign instr_integrity_fault_m_hit[t]  = (priv_lvl == PRIV_LVL_M) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_M_MODE]) && (tdata2_arry[t][EXC_CAUSE_INSTR_INTEGRITY_FAULT]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_INSTR_INTEGRITY_FAULT);
      //assign instr_integrity_fault_u_hit[t]  = wb_is_umode() && set_tdatas_etrigger_state(t, ET_U_MODE, EXC_CAUSE_INSTR_INTEGRITY_FAULT) && wb_is_exception(EXC_CAUSE_INSTR_INTEGRITY_FAULT);
      assign instr_integrity_fault_u_hit[t]  = (priv_lvl == PRIV_LVL_U) && (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER) && (tdata1_arry[t][ET_U_MODE]) && (tdata2_arry[t][EXC_CAUSE_INSTR_INTEGRITY_FAULT]) && (wb_valid) && (wb_exception) && (wb_exception_code == EXC_CAUSE_INSTR_INTEGRITY_FAULT);
    end
  endgenerate


  property p_wb_enter_debug_due_to_x(x);
    |x
    && wb_valid
    && !wb_dbg_mode
    && wb_last_op
    ##1 1 //rvfi_valid || !rvfi_valid
    ##1 rvfi_if.rvfi_valid[->1]
    |->
    rvfi_if.rvfi_dbg_mode;
  endproperty


  generate
    for (genvar t = 0; t < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS; t++) begin

      a_dt_enter_dbg_etrigger_m_instr_access_fault: assert property(
        p_wb_enter_debug_due_to_x(instr_access_fault_m_hit[t])
      ) else `uvm_error(info_tag, "The exception \"instruction access fault\" in machine mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_u_instr_access_fault: assert property(
        p_wb_enter_debug_due_to_x(instr_access_fault_u_hit[t])
      ) else `uvm_error(info_tag, "The exception \"instruction access fault\" in user mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_m_illegal_instr: assert property(
        p_wb_enter_debug_due_to_x(illegal_instr_m_hit[t])
      ) else `uvm_error(info_tag, "The exception \"illegal instruction\" in machine mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_u_illegal_instr: assert property(
        p_wb_enter_debug_due_to_x(illegal_instr_u_hit[t])
      ) else `uvm_error(info_tag, "The exception \"illegal instruction\" in user mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_m_breakpoint: assert property(
        p_wb_enter_debug_due_to_x(breakpoint_m_hit[t])
      ) else `uvm_error(info_tag, "The exception \"breakpoint\" in machine mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_u_breakpoint: assert property(
        p_wb_enter_debug_due_to_x(breakpoint_u_hit[t])
      ) else `uvm_error(info_tag, "The exception \"breakpoint\" in user mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_m_load_access_fault: assert property(
        p_wb_enter_debug_due_to_x(load_access_fault_m_hit[t])
      ) else `uvm_error(info_tag, "The exception \"load access fault\" in machine mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_u_load_access_fault: assert property(
        p_wb_enter_debug_due_to_x(load_access_fault_u_hit[t])
      ) else `uvm_error(info_tag, "The exception \"load access fault\" in user mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_m_store_AMO_access_fault: assert property(
        p_wb_enter_debug_due_to_x(store_AMO_access_fault_m_hit[t])
      ) else `uvm_error(info_tag, "The exception \"store/AMO access fault\" in machine mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_u_store_AMO_access_fault: assert property(
        p_wb_enter_debug_due_to_x(store_AMO_access_fault_u_hit[t])
      ) else `uvm_error(info_tag, "The exception \"store/AMO access fault\" in user mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_m_uecall: assert property(
        p_wb_enter_debug_due_to_x(uecall_m_hit[t])
      ) else `uvm_error(info_tag, "The exception \"environment call from user mode\" in machine mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_u_uecall: assert property(
        p_wb_enter_debug_due_to_x(uecall_u_hit[t])
      ) else `uvm_error(info_tag, "The exception \"environment call from user mode\" in user mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_m_mecall: assert property(
        p_wb_enter_debug_due_to_x(mecall_m_hit[t])
      ) else `uvm_error(info_tag, "The exception \"environment call from machine mode\" in machine mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_u_mecall: assert property(
        p_wb_enter_debug_due_to_x(mecall_u_hit[t])
      ) else `uvm_error(info_tag, "The exception \"environment call from machine mode\" in user mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_m_instr_bus_fault: assert property(
        p_wb_enter_debug_due_to_x(instr_bus_fault_m_hit[t])
      ) else `uvm_error(info_tag, "The exception \"instruction bus fault\" in machine mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_u_instr_bus_fault: assert property(
        p_wb_enter_debug_due_to_x(instr_bus_fault_u_hit[t])
      ) else `uvm_error(info_tag, "The exception \"instruction bus fault\" in user mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_m_instr_integrity_fault: assert property(
        p_wb_enter_debug_due_to_x(instr_integrity_fault_m_hit[t])
      ) else `uvm_error(info_tag, "The exception \"instruction parity/checksum (integrity) fault\" in machine mode does not send the core into debug mode.\n");

      a_dt_enter_dbg_etrigger_u_instr_integrity_fault: assert property(
        p_wb_enter_debug_due_to_x(instr_integrity_fault_u_hit[t])
      ) else `uvm_error(info_tag, "The exception \"instruction parity/checksum (integrity) fault\" in user mode does not send the core into debug mode.\n");

    end
  endgenerate

  //2) see a_dt_enter_dbg_reason

/*
- Vplan:
Configure an exception trigger, use the privmode bits to disable/enable the trigger, exercise the trigger conditions, check that it fires/not accordingly. Also check the WARL fields.

- Assertion verifikasjon:
1) Configure an exception trigger, use the privmode bits to disable/enable the trigger, exercise the trigger conditions, check that it fires/not accordingly.
2) Check the WARL fields
*/

  //1) see a_dt_enter_dbg_*

  //2)
  a_dt_warl_tselect: assert property (
    rvfi_if.rvfi_valid
    && |tselect.rvfi_csr_wmask != 0
    |->
    tselect_w < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS
    || tselect_w == '0 //(when there are no triggers)
  ) else `uvm_error(info_tag, "There is a problem with tselect's WARL fields.\n");

  a_dt_warl_tdata1_general: assert property (
    rvfi_if.rvfi_valid
    && |tdata1.rvfi_csr_wmask != 0
    |->
    (tdata1_w[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL
    || tdata1_w[MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER
    || tdata1_w[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6
    || tdata1_w[MSB_TYPE:LSB_TYPE] == TTYPE_DISABLED)
    && tdata1_w[DMODE]
  ) else `uvm_error(info_tag, "There is a problem with tdata1's general WARL fields.\n");

  a_dt_warl_tdata1_m2: assert property (
    rvfi_if.rvfi_valid
    && |tdata1.rvfi_csr_wmask != 0
    && tdata1_w[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL
    |->
    !tdata1_w[MSB_MASKMAX:LSB_MASKMAX]
    && !tdata1_w[M2_HIT]
    && !tdata1_w[M2_SELECT]
    && !tdata1_w[M2_TIMING]
    && !tdata1_w[M2_MSB_SIZELO:M2_LSB_SIZELO]
    && tdata1_w[MSB_ACTION:LSB_ACTION] == ENTER_DBG_ON_MATCH
    && !tdata1_w[CHAIN]
    && (tdata1_w[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL
    || tdata1_w[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL
    || tdata1_w[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER)
    && !tdata1_w[HW_ZERO_5]
    && !tdata1_w[S_MODE]
  ) else `uvm_error(info_tag, "There is a problem with tdata1-mcontrol's WARL fields.\n");

  a_dt_warl_tdata1_etrigger: assert property (
    rvfi_if.rvfi_valid
    && |tdata1.rvfi_csr_wmask != 0
    && tdata1_w[MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER
    |->
    !tdata1_w[ET_HIT]
    && !tdata1_w[HW_ZERO_25:HW_ZERO_13]
    && !tdata1_w[ET_VS]
    && !tdata1_w[ET_VU]
    && !tdata1_w[HW_ZERO_10]
    && !tdata1_w[HW_ZERO_8]
    && !tdata1_w[ET_S]
    && tdata1_w[ET_MSB_ACTION:ET_LSB_ACTION] == ENTER_DBG_ON_MATCH
  ) else `uvm_error(info_tag, "There is a problem with tdata1-etrigger's WARL fields.\n");

  a_dt_warl_tdata1_m6: assert property (
    rvfi_if.rvfi_valid
    && |tdata1.rvfi_csr_wmask != 0
    && tdata1_w[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6
    |->
    !tdata1_w[HW_ZERO_26:HW_ZERO_25]
    && !tdata1_w[M6_VS]
    && !tdata1_w[M6_VU]
    && !tdata1_w[M6_HIT]
    && !tdata1_w[M6_SELECT]
    && !tdata1_w[M6_TIMING]
    && !tdata1_w[M6_MSB_SIZE:M6_LSB_SIZE]
    && tdata1_w[MSB_ACTION:LSB_ACTION] == ENTER_DBG_ON_MATCH
    && !tdata1_w[CHAIN]
    && (tdata1_w[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL
    || tdata1_w[MSB_MATCH:LSB_MATCH] ==  MATCH_WHEN_GREATER_OR_EQUAL
    || tdata1_w[MSB_MATCH:LSB_MATCH] ==  MATCH_WHEN_LESSER)
    && !tdata1_w[HW_ZERO_5]
    && !tdata1_w[S_MODE]
  ) else `uvm_error(info_tag, "There is a problem with tdata1-mcontrol6's WARL fields.\n");

  a_dt_warl_tdata1_disabled: assert property (
    rvfi_if.rvfi_valid
    && |tdata1.rvfi_csr_wmask != 0
    && tdata1_w[MSB_TYPE:LSB_TYPE] == TTYPE_DISABLED
    |->
    !tdata1_w[DIS_MSB_DATA:DIS_LSB_DATA]
  ) else `uvm_error(info_tag, "There is a problem with tdata1-disabled's WARL fields.\n");

  a_dt_warl_tdata2_etrigger: assert property (
    rvfi_if.rvfi_valid
    && |tdata2.rvfi_csr_wmask != 0
    && tdata1_w[MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER
    |->
    !tdata2_w[ET2_DATA_31:ET2_DATA_26]
    && !tdata2_w[ET2_DATA_23:ET2_DATA_12]
    && !tdata2_w[ET2_DATA_10:ET2_DATA_9]
    && !tdata2_w[ET2_DATA_6]
    && !tdata2_w[ET2_DATA_4]
    && !tdata2_w[ET2_DATA_0]
  ) else `uvm_error(info_tag, "There is a problem with tdata1-etrigger's WARL fields.\n");

  a_dt_warl_tdata3: assert property (
    rvfi_if.rvfi_valid
    && |tdata3.rvfi_csr_wmask != 0
    |->
    !tdata3_w
  ) else `uvm_error(info_tag, "There is a problem with tdata3's WARL fields.\n");

  a_dt_warl_tinfo: assert property (
    rvfi_if.rvfi_valid
    && |tinfo.rvfi_csr_wmask != 0
    |->
    !tinfo_w[31:16]
  ) else `uvm_error(info_tag, "There is a problem with tinfo's WARL fields.\n");

  a_dt_warl_tcontrol: assert property (
    rvfi_if.rvfi_valid
    && |tcontrol.rvfi_csr_wmask != 0
    |->
    !tcontrol_w[HW_ZERO_31:HW_ZERO_8]
    && !tcontrol_w[MPTE]
    && !tcontrol_w[HW_ZERO_6:HW_ZERO_4]
    && !tcontrol_w[MTE]
    && !tcontrol_w[HW_ZERO_2:HW_ZERO_0]
  ) else `uvm_error(info_tag, "There is a problem with tcontrol's WARL fields.\n");

/*
  - Assertion verifikasjon:
1) Verify that we enter debug when triggering the enabled exceptions
2) Verify that we do not enter debug when triggering unenabled exceptions
*/


  //Abbreviations:
  //exe = execute
  //m = machine
  //u = user
  //eq = equal
  //geq = greater or equal
  //l = lesser
  //bX = byte number X

  //Execute:
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] exe_eq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] exe_eq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] exe_geq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] exe_geq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] exe_l_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0] exe_l_u_hit;

  //Load:
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b0_eq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b0_eq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b0_geq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b0_geq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b0_l_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b0_l_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b1_eq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b1_eq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b1_geq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b1_geq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b1_l_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b1_l_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b2_eq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b2_eq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b2_geq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b2_geq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b2_l_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b2_l_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b3_eq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b3_eq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b3_geq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b3_geq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b3_l_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] load_b3_l_u_hit;

  //Store:
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b0_eq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b0_eq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b0_geq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b0_geq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b0_l_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b0_l_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b1_eq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b1_eq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b1_geq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b1_geq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b1_l_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b1_l_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b2_eq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b2_eq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b2_geq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b2_geq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b2_l_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b2_l_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b3_eq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b3_eq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b3_geq_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b3_geq_u_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b3_l_m_hit;
  logic [uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS-1:0][NMEM-1:0] store_b3_l_u_hit;

  function logic set_tdata1_mctrl_state(int tdata_nr, int instr_type, int match_type, int priv_lvl);

    set_tdata1_mctrl_state = ((tdata1_arry[tdata_nr][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[tdata_nr][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6))
      && tdata1_arry[tdata_nr][instr_type]
      && (tdata1_arry[tdata_nr][MSB_MATCH:LSB_MATCH] == match_type)
      && tdata1_arry[tdata_nr][priv_lvl];
  endfunction

  function logic eq_tdata2(logic [31:0] sig, int tdata2_nr);
    eq_tdata2 = (sig == tdata2_arry[tdata2_nr]);
  endfunction

  function logic geq_tdata2(logic [31:0] sig, int tdata2_nr);
    geq_tdata2 = (sig >= tdata2_arry[tdata2_nr]);
  endfunction

  function logic l_tdata2(logic [31:0] sig, int tdata2_nr);
    l_tdata2 = (sig < tdata2_arry[tdata2_nr]);
  endfunction

  //function automatic logic get_mem_rmask_byte(int mem_txn, int byte_pos);
  function logic get_mem_rmask_byte(int mem_txn, int byte_pos);
    get_mem_rmask_byte = (|((rvfi_if.get_mem_rmask(mem_txn)) & ({0001} << byte_pos)));
    //logic [3:0] byte_to_check = ({0001} << byte_pos);
    //logic [3:0] rmask = (rvfi_if.get_mem_rmask(mem_txn));
    //logic is_byte_read = |((rvfi_if.get_mem_rmask(mem_txn)) & ({0001} << byte_pos));
    //return is_byte_read;
  endfunction


  //Set all possible ways of entering debug mode due to trigger match:
  generate
    for (genvar t = 0; t < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS; t++) begin

      //Execute:
      //assign exe_eq_m_hit[t] = set_tdata1_mctrl_state(t, EXECUTE, MATCH_WHEN_EQUAL, M_MODE) && rvfi_if.is_mmode() && eq_tdata2(rvfi_if.rvfi_pc_rdata, t);
      assign exe_eq_m_hit[t] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][EXECUTE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.rvfi_pc_rdata == tdata2_arry[t]);

      //assign exe_eq_u_hit[t] = set_tdata1_mctrl_state(t, EXECUTE, MATCH_WHEN_EQUAL, U_MODE) && rvfi_if.is_umode() && eq_tdata2(rvfi_if.rvfi_pc_rdata, t);
      assign exe_eq_u_hit[t] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][EXECUTE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.rvfi_pc_rdata == tdata2_arry[t]);

      //assign exe_geq_m_hit[t] = set_tdata1_mctrl_state(t, EXECUTE, MATCH_WHEN_GREATER_OR_EQUAL, M_MODE) && rvfi_if.is_mmode() && geq_tdata2(rvfi_if.rvfi_pc_rdata, t);
      assign exe_geq_m_hit[t] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][EXECUTE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.rvfi_pc_rdata >= tdata2_arry[t]);

      //assign exe_geq_u_hit[t] = set_tdata1_mctrl_state(t, EXECUTE, MATCH_WHEN_GREATER_OR_EQUAL, U_MODE) && rvfi_if.is_umode() && geq_tdata2(rvfi_if.rvfi_pc_rdata, t);
      assign exe_geq_u_hit[t] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][EXECUTE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.rvfi_pc_rdata >= tdata2_arry[t]);

      //assign exe_l_m_hit[t] = set_tdata1_mctrl_state(t, EXECUTE, MATCH_WHEN_LESSER, M_MODE) && rvfi_if.is_mmode() && l_tdata2(rvfi_if.rvfi_pc_rdata, t);
      assign exe_l_m_hit[t] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][EXECUTE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.rvfi_pc_rdata < tdata2_arry[t]);

      //assign exe_l_u_hit[t] = set_tdata1_mctrl_state(t, EXECUTE, MATCH_WHEN_LESSER, U_MODE) && rvfi_if.is_umode() && l_tdata2(rvfi_if.rvfi_pc_rdata, t);
      assign exe_l_u_hit[t] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][EXECUTE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.rvfi_pc_rdata < tdata2_arry[t]);

      //Make sure we check all possible memory entries:
      for (genvar m = 0; m < NMEM; m++) begin
        //Load:
        //Byte 0:
        //assign load_b0_eq_m_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, M_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_mmode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 0);
        assign load_b0_eq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m) == tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 0)));
        //assign load_b0_eq_u_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, U_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_umode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 0);
        assign load_b0_eq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m) == tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 0)));

        //assign load_b0_geq_m_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, M_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_mmode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 0);
        assign load_b0_geq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m) >= tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 0)));
        //assign load_b0_geq_u_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, U_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_umode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 0);
        assign load_b0_geq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m) >= tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 0)));

        //assign load_b0_l_m_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, M_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_mmode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 0);
        assign load_b0_l_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m) < tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 0)));
        //assign load_b0_l_u_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, U_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_umode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 0);
        assign load_b0_l_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m) < tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 0)));

        //Byte +1:
        //assign load_b1_eq_m_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, M_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_mmode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 1);
        assign load_b1_eq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+1 == tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 1)));
        //assign load_b1_eq_u_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, U_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_umode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 1);
        assign load_b1_eq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+1 == tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 1)));

        //assign load_b1_geq_m_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, M_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_mmode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 1);
        assign load_b1_geq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+1 >= tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 1)));
        //assign load_b1_geq_u_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, U_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_umode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 1);
        assign load_b1_geq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+1 >= tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 1)));

        //assign load_b1_l_m_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, M_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_mmode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 1);
        assign load_b1_l_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+1 < tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 1)));
        //assign load_b1_l_u_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, U_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_umode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 1);
        assign load_b1_l_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+1 < tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 1)));

        //Byte +2:
        //assign load_b2_eq_m_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, M_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_mmode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 2);
        assign load_b2_eq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+2 == tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 2)));
        //assign load_b2_eq_u_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, U_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_umode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 2);
        assign load_b2_eq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+2 == tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 2)));

        //assign load_b2_geq_m_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, M_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_mmode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 2);
        assign load_b2_geq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+2 >= tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 2)));
        //assign load_b2_geq_u_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, U_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_umode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 2);
        assign load_b2_geq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+2 >= tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 2)));

        //assign load_b2_l_m_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, M_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_mmode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 2);
        assign load_b2_l_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+2 < tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 2)));
        //assign load_b2_l_u_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, U_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_umode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 2);
        assign load_b2_l_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+2 < tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 2)));

        //Byte +3:
        //assign load_b3_eq_m_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, M_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_mmode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 3);
        assign load_b3_eq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+3 == tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 3)));
        //assign load_b3_eq_u_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, U_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_umode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 3);
        assign load_b3_eq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+3 == tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 3)));

        //assign load_b3_geq_m_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, M_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_mmode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 3);
        assign load_b3_geq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+3 >= tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 3)));
        //assign load_b3_geq_u_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, U_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_umode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 3);
        assign load_b3_geq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+3 >= tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 3)));

        //assign load_b3_l_m_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, M_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_mmode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 3);
        assign load_b3_l_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+3 < tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 3)));
        //assign load_b3_l_u_hit[t][m] = set_tdata1_mctrl_state(t, LOAD, U_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_umode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 3);
        assign load_b3_l_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][LOAD]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+3 < tdata2_arry[t]) && (|((rvfi_if.get_mem_rmask(m)) & ({0001} << 3)));

        //Store:
        //Byte 0:
        //assign store_b0_eq_m_hit[t][m] = set_tdata1_mctrl_state(t, STORE, M_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_mmode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 0);
        assign store_b0_eq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m) == tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 0)));
        //assign store_b0_eq_u_hit[t][m] = set_tdata1_mctrl_state(t, STORE, U_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_umode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 0);
        assign store_b0_eq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m) == tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 0)));

        //assign store_b0_geq_m_hit[t][m] = set_tdata1_mctrl_state(t, STORE, M_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_mmode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 0);
        assign store_b0_geq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m) >= tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 0)));
        //assign store_b0_geq_u_hit[t][m] = set_tdata1_mctrl_state(t, STORE, U_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_umode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 0);
        assign store_b0_geq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m) >= tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 0)));

        //assign store_b0_l_m_hit[t][m] = set_tdata1_mctrl_state(t, STORE, M_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_mmode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 0);
        assign store_b0_l_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m) < tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 0)));
        //assign store_b0_l_u_hit[t][m] = set_tdata1_mctrl_state(t, STORE, U_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_umode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 0);
        assign store_b0_l_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m) < tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 0)));

        //Byte +1:
        //assign store_b1_eq_m_hit[t][m] = set_tdata1_mctrl_state(t, STORE, M_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_mmode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 1);
        assign store_b1_eq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+1 == tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 1)));
        //assign store_b1_eq_u_hit[t][m] = set_tdata1_mctrl_state(t, STORE, U_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_umode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 1);
        assign store_b1_eq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+1 == tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 1)));

        //assign store_b1_geq_m_hit[t][m] = set_tdata1_mctrl_state(t, STORE, M_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_mmode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 1);
        assign store_b1_geq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+1 >= tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 1)));
        //assign store_b1_geq_u_hit[t][m] = set_tdata1_mctrl_state(t, STORE, U_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_umode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 1);
        assign store_b1_geq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+1 >= tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 1)));

        //assign store_b1_l_m_hit[t][m] = set_tdata1_mctrl_state(t, STORE, M_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_mmode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 1);
        assign store_b1_l_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+1 < tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 1)));
        //assign store_b1_l_u_hit[t][m] = set_tdata1_mctrl_state(t, STORE, U_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_umode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 1);
        assign store_b1_l_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+1 < tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 1)));

        //Byte +2:
        //assign store_b2_eq_m_hit[t][m] = set_tdata1_mctrl_state(t, STORE, M_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_mmode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 2);
        assign store_b2_eq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+2 == tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 2)));
        //assign store_b2_eq_u_hit[t][m] = set_tdata1_mctrl_state(t, STORE, U_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_umode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 2);
        assign store_b2_eq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+2 == tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 2)));

        //assign store_b2_geq_m_hit[t][m] = set_tdata1_mctrl_state(t, STORE, M_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_mmode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 2);
        assign store_b2_geq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+2 >= tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 2)));
        //assign store_b2_geq_u_hit[t][m] = set_tdata1_mctrl_state(t, STORE, U_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_umode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 2);
        assign store_b2_geq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+2 >= tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 2)));

        //assign store_b2_l_m_hit[t][m] = set_tdata1_mctrl_state(t, STORE, M_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_mmode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 2);
        assign store_b2_l_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+2 < tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 2)));
        //assign store_b2_l_u_hit[t][m] = set_tdata1_mctrl_state(t, STORE, U_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_umode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 2);
        assign store_b2_l_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+2 < tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 2)));

        //Byte +3:
        //assign store_b3_eq_m_hit[t][m] = set_tdata1_mctrl_state(t, STORE, M_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_mmode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 3);
        assign store_b3_eq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+3 == tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 3)));
        //assign store_b3_eq_u_hit[t][m] = set_tdata1_mctrl_state(t, STORE, U_MODE, MATCH_WHEN_EQUAL) && rvfi_if.is_umode() && eq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 3);
        assign store_b3_eq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+3 == tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 3)));

        //assign store_b3_geq_m_hit[t][m] = set_tdata1_mctrl_state(t, STORE, M_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_mmode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 3);
        assign store_b3_geq_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+3 >= tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 3)));
        //assign store_b3_geq_u_hit[t][m] = set_tdata1_mctrl_state(t, STORE, U_MODE, MATCH_WHEN_GREATER_OR_EQUAL) && rvfi_if.is_umode() && geq_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 3);
        assign store_b3_geq_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+3 >= tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 3)));

        //assign store_b3_l_m_hit[t][m] = set_tdata1_mctrl_state(t, STORE, M_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_mmode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 3);
        assign store_b3_l_m_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][M_MODE]) && rvfi_if.is_mmode() && (rvfi_if.get_mem_addr(m)+3 < tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 3)));
        //assign store_b3_l_u_hit[t][m] = set_tdata1_mctrl_state(t, STORE, U_MODE, MATCH_WHEN_LESSER) && rvfi_if.is_umode() && l_tdata2(rvfi_if.get_mem_addr(m), t) && get_mem_rmask_byte(m, 3);
        assign store_b3_l_u_hit[t][m] = ((tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL) || (tdata1_arry[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)) && (tdata1_arry[t][STORE]) && (tdata1_arry[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER) && (tdata1_arry[t][U_MODE]) && rvfi_if.is_umode() && (rvfi_if.get_mem_addr(m)+3 < tdata2_arry[t]) && (|((rvfi_if.get_mem_wmask(m)) & ({0001} << 3)));

      end
    end
  endgenerate

  property p_enter_debug_due_to_x(x);
    |x
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode

    ##1 rvfi_if.rvfi_valid[->1]

    |->
    rvfi_if.rvfi_dbg_mode;
  endproperty


  property p_load_enter_debug_due_to_x(x);
    |x
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode
    && |rvfi_if.rvfi_mem_rmask

    && !rvfi_if.rvfi_trap.exception

    ##1 rvfi_if.rvfi_valid[->1]

    |->
    rvfi_if.rvfi_dbg_mode;
  endproperty


  property p_store_enter_debug_due_to_x(x);
    |x
    && rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode
    && |rvfi_if.rvfi_mem_wmask

    && !rvfi_if.rvfi_trap.exception

    ##1 rvfi_if.rvfi_valid[->1]

    |->
    rvfi_if.rvfi_dbg_mode;
  endproperty

  //1)
  generate
    for (genvar t = 0; t < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS; t++) begin

      //Execution
      a_dt_enter_dbg_exe_eq_m: assert property(
        p_enter_debug_due_to_x(exe_eq_m_hit[t])
      ) else `uvm_error(info_tag, "The PC equals tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_exe_eq_u: assert property(
        p_enter_debug_due_to_x(exe_eq_u_hit[t])
      ) else `uvm_error(info_tag, "The PC equals tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_exe_geq_m: assert property(
        p_enter_debug_due_to_x(exe_geq_m_hit[t])
      ) else `uvm_error(info_tag, "The PC is greater or equal to tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_exe_geq_u: assert property(
        p_enter_debug_due_to_x(exe_geq_u_hit[t])
      ) else `uvm_error(info_tag, "The PC is greater or equal to tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_exe_l_m: assert property(
        p_enter_debug_due_to_x(exe_l_m_hit[t])
      ) else `uvm_error(info_tag, "The PC is lesser than tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_exe_l_u: assert property(
        p_enter_debug_due_to_x(exe_l_u_hit[t])
      ) else `uvm_error(info_tag, "The PC is lesser than tdata2 in user mode but does not send the core into debug mode.\n");

      //Load:
      //Byte 0:
      a_dt_enter_dbg_load_b0_eq_m: assert property(
        p_load_enter_debug_due_to_x(load_b0_eq_m_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 0's address equals tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b0_eq_u: assert property(
        p_load_enter_debug_due_to_x(load_b0_eq_u_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 0's address equals tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b0_geq_m: assert property(
        p_load_enter_debug_due_to_x(load_b0_geq_m_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 0's address is greater or equal to tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b0_geq_u: assert property(
        p_load_enter_debug_due_to_x(load_b0_geq_u_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 0's address is greater or equal to tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b0_l_m: assert property(
        p_load_enter_debug_due_to_x(load_b0_l_m_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 0's address is lesser than tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b0_l_u: assert property(
        p_load_enter_debug_due_to_x(load_b0_l_u_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 0's address is lesser than tdata2 in user mode but does not send the core into debug mode.\n");

      //Byte +1:
      a_dt_enter_dbg_load_b1_eq_m: assert property(
        p_load_enter_debug_due_to_x(load_b1_eq_m_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 1's address equals tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b1_eq_u: assert property(
        p_load_enter_debug_due_to_x(load_b1_eq_u_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 1's address equals tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b1_geq_m: assert property(
        p_load_enter_debug_due_to_x(load_b1_geq_m_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 1's address is greater or equal to tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b1_geq_u: assert property(
        p_load_enter_debug_due_to_x(load_b1_geq_u_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 1's address is greater or equal to tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b1_l_m: assert property(
        p_load_enter_debug_due_to_x(load_b1_l_m_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 1's address is lesser than tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b1_l_u: assert property(
        p_load_enter_debug_due_to_x(load_b1_l_u_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 1's address is lesser than tdata2 in user mode but does not send the core into debug mode.\n");


      //Byte +2:
      a_dt_enter_dbg_load_b2_eq_m: assert property(
        p_load_enter_debug_due_to_x(load_b2_eq_m_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 2's address equals tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b2_eq_u: assert property(
        p_load_enter_debug_due_to_x(load_b2_eq_u_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 2's address equals tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b2_geq_m: assert property(
        p_load_enter_debug_due_to_x(load_b2_geq_m_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 2's address is greater or equal to tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b2_geq_u: assert property(
        p_load_enter_debug_due_to_x(load_b2_geq_u_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 2's address is greater or equal to tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b2_l_m: assert property(
        p_load_enter_debug_due_to_x(load_b2_l_m_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 2's address is lesser than tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b2_l_u: assert property(
        p_load_enter_debug_due_to_x(load_b2_l_u_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 2's address is lesser than tdata2 in user mode but does not send the core into debug mode.\n");


      //Byte +3:
      a_dt_enter_dbg_load_b3_eq_m: assert property(
        p_load_enter_debug_due_to_x(load_b3_eq_m_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 3's address equals tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b3_eq_u: assert property(
        p_load_enter_debug_due_to_x(load_b3_eq_u_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 3's address equals tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b3_geq_m: assert property(
        p_load_enter_debug_due_to_x(load_b3_geq_m_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 3's address is greater or equal to tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b3_geq_u: assert property(
        p_load_enter_debug_due_to_x(load_b3_geq_u_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 3's address is greater or equal to tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b3_l_m: assert property(
        p_load_enter_debug_due_to_x(load_b3_l_m_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 3's address is lesser than tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_load_b3_l_u: assert property(
        p_load_enter_debug_due_to_x(load_b3_l_u_hit[t])
      ) else `uvm_error(info_tag, "The loaded byte nr. 3's address is lesser than tdata2 in user mode but does not send the core into debug mode.\n");

      //Store:
      //Byte 0:
      a_dt_enter_dbg_store_b0_eq_m: assert property(
        p_store_enter_debug_due_to_x(store_b0_eq_m_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 0's address equals tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b0_eq_u: assert property(
        p_store_enter_debug_due_to_x(store_b0_eq_u_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 0's address equals tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b0_geq_m: assert property(
        p_store_enter_debug_due_to_x(store_b0_geq_m_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 0's address is greater or equal to tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b0_geq_u: assert property(
        p_store_enter_debug_due_to_x(store_b0_geq_u_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 0's address is greater or equal to tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b0_l_m: assert property(
        p_store_enter_debug_due_to_x(store_b0_l_m_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 0's address is lesser than tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b0_l_u: assert property(
        p_store_enter_debug_due_to_x(store_b0_l_u_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 0's address is lesser than tdata2 in user mode but does not send the core into debug mode.\n");

      //Byte +1:
      a_dt_enter_dbg_store_b1_eq_m: assert property(
        p_store_enter_debug_due_to_x(store_b1_eq_m_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 1's address equals tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b1_eq_u: assert property(
        p_store_enter_debug_due_to_x(store_b1_eq_u_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 1's address equals tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b1_geq_m: assert property(
        p_store_enter_debug_due_to_x(store_b1_geq_m_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 1's address is greater or equal to tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b1_geq_u: assert property(
        p_store_enter_debug_due_to_x(store_b1_geq_u_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 1's address is greater or equal to tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b1_l_m: assert property(
        p_store_enter_debug_due_to_x(store_b1_l_m_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 1's address is lesser than tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b1_l_u: assert property(
        p_store_enter_debug_due_to_x(store_b1_l_u_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 1's address is lesser than tdata2 in user mode but does not send the core into debug mode.\n");


      //Byte +2:
      a_dt_enter_dbg_store_b2_eq_m: assert property(
        p_store_enter_debug_due_to_x(store_b2_eq_m_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 2's address equals tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b2_eq_u: assert property(
        p_store_enter_debug_due_to_x(store_b2_eq_u_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 2's address equals tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b2_geq_m: assert property(
        p_store_enter_debug_due_to_x(store_b2_geq_m_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 2's address is greater or equal to tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b2_geq_u: assert property(
        p_store_enter_debug_due_to_x(store_b2_geq_u_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 2's address is greater or equal to tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b2_l_m: assert property(
        p_store_enter_debug_due_to_x(store_b2_l_m_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 2's address is lesser than tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b2_l_u: assert property(
        p_store_enter_debug_due_to_x(store_b2_l_u_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 2's address is lesser than tdata2 in user mode but does not send the core into debug mode.\n");


      //Byte +3:
      a_dt_enter_dbg_store_b3_eq_m: assert property(
        p_store_enter_debug_due_to_x(store_b3_eq_m_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 3's address equals tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b3_eq_u: assert property(
        p_store_enter_debug_due_to_x(store_b3_eq_u_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 3's address equals tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b3_geq_m: assert property(
        p_store_enter_debug_due_to_x(store_b3_geq_m_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 3's address is greater or equal to tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b3_geq_u: assert property(
        p_store_enter_debug_due_to_x(store_b3_geq_u_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 3's address is greater or equal to tdata2 in user mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b3_l_m: assert property(
        p_store_enter_debug_due_to_x(store_b3_l_m_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 3's address is lesser than tdata2 in machine mode but does not send the core into debug mode.\n");

      a_dt_enter_dbg_store_b3_l_u: assert property(
        p_store_enter_debug_due_to_x(store_b3_l_u_hit[t])
      ) else `uvm_error(info_tag, "The stored byte nr. 3's address is lesser than tdata2 in user mode but does not send the core into debug mode.\n");

    end
  endgenerate


  //2)
  a_dt_enter_dbg_reason: assert property (
    rvfi_if.rvfi_valid
    && rvfi_if.rvfi_trap.debug
    && rvfi_if.rvfi_trap.debug_cause == TRIGGER_MATCH

    |->
    //mcontrol or mcontrol6:
    |exe_eq_m_hit
    || |exe_eq_u_hit
    || |exe_geq_m_hit
    || |exe_geq_u_hit
    || |exe_l_m_hit
    || |exe_l_u_hit
    || |load_b0_eq_m_hit
    || |load_b0_eq_u_hit
    || |load_b0_geq_m_hit
    || |load_b0_geq_u_hit
    || |load_b0_l_m_hit
    || |load_b0_l_u_hit
    || |load_b1_eq_m_hit
    || |load_b1_eq_u_hit
    || |load_b1_geq_m_hit
    || |load_b1_geq_u_hit
    || |load_b1_l_m_hit
    || |load_b1_l_u_hit
    || |load_b2_eq_m_hit
    || |load_b2_eq_u_hit
    || |load_b2_geq_m_hit
    || |load_b2_geq_u_hit
    || |load_b2_l_m_hit
    || |load_b2_l_u_hit
    || |load_b3_eq_m_hit
    || |load_b3_eq_u_hit
    || |load_b3_geq_m_hit
    || |load_b3_geq_u_hit
    || |load_b3_l_m_hit
    || |load_b3_l_u_hit
    || |store_b0_eq_m_hit
    || |store_b0_eq_u_hit
    || |store_b0_geq_m_hit
    || |store_b0_geq_u_hit
    || |store_b0_l_m_hit
    || |store_b0_l_u_hit
    || |store_b1_eq_m_hit
    || |store_b1_eq_u_hit
    || |store_b1_geq_m_hit
    || |store_b1_geq_u_hit
    || |store_b1_l_m_hit
    || |store_b1_l_u_hit
    || |store_b2_eq_m_hit
    || |store_b2_eq_u_hit
    || |store_b2_geq_m_hit
    || |store_b2_geq_u_hit
    || |store_b2_l_m_hit
    || |store_b2_l_u_hit
    || |store_b3_eq_m_hit
    || |store_b3_eq_u_hit
    || |store_b3_geq_m_hit
    || |store_b3_geq_u_hit
    || |store_b3_l_m_hit
    || |store_b3_l_u_hit

    //etrigger:
    || |instr_access_fault_m_hit
    || |instr_access_fault_u_hit
    || |illegal_instr_m_hit
    || |illegal_instr_u_hit
    || |breakpoint_m_hit
    || |breakpoint_u_hit
    || |load_access_fault_m_hit
    || |load_access_fault_u_hit
    || |store_AMO_access_fault_m_hit
    || |store_AMO_access_fault_u_hit
    || |uecall_m_hit
    || |uecall_u_hit
    || |mecall_m_hit
    || |mecall_u_hit
    || |instr_bus_fault_m_hit
    || |instr_bus_fault_u_hit
    || |instr_integrity_fault_m_hit
    || |instr_integrity_fault_u_hit

  ) else `uvm_error(info_tag, "We have entered debug mode due to triggers but not due to any of the listed reasons.\n");

endmodule : uvmt_cv32e40s_triggers_assert_cov
