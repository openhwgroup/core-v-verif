// Copyright 2023 Silicon Labs, Inc.
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


module uvmt_cv32e40s_triggers_assert_cov
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  import cv32e40s_rvfi_pkg::*;
  import uvmt_cv32e40s_pkg::*;
  (
    input logic [31:0] tdata1_array[CORE_PARAM_DBG_NUM_TRIGGERS+1],
    input privlvl_t priv_lvl,

    uvma_rvfi_instr_if_t rvfi_if,
    uvma_clknrst_if_t clknrst_if,
    uvmt_cv32e40s_support_logic_module_o_if_t.slave_mp  support_if,

    uvma_rvfi_csr_if_t tdata1_if,
    uvma_rvfi_csr_if_t tdata2_if,
    uvma_rvfi_csr_if_t tinfo_if,
    uvma_rvfi_csr_if_t tselect_if,
    uvma_rvfi_csr_if_t dcsr_if,
    uvma_rvfi_csr_if_t dpc_if
  );

  default clocking @(posedge clknrst_if.clk); endclocking
  default disable iff !(clknrst_if.reset_n);

  string info_tag = "TRIGGER ASSERT: ";

  /////////// Local Parameters ///////////

  //tinfo:
  localparam VERSION_MSB = 31;
  localparam VERSION_LSB = 24;
  localparam INFO_MSB = 15;
  localparam INFO_LSB = 0;

  //common tdata1 values:
  localparam LSB_TYPE = 28;
  localparam MSB_TYPE = 31;
  localparam DMODE = 27;

  //common tdata1 mcontrol and mcontrol6 values:
  localparam LOAD = 0;
  localparam STORE = 1;
  localparam EXECUTE = 2;
  localparam M2_M6_S_MODE = 4;
  localparam LSB_MATCH = 7;
  localparam MSB_MATCH = 10;
  localparam CHAIN = 11;
  localparam LSB_ACTION = 12;
  localparam MSB_ACTION = 15;

  //tdata1 mcontrol:
  localparam MSB_MASKMAX = 26;
  localparam LSB_MASKMAX = 21;
  localparam M2_HIT = 20;
  localparam M2_SELECT = 19;
  localparam M2_TIMING = 18;
  localparam M2_MSB_SIZELO = 17;
  localparam M2_LSB_SIZELO = 16;

  //tdata1 mcontrol6:
  localparam M6_UNCERTAIN = 26;
  localparam M6_HIT1 = 25;
  localparam M6_VS = 24;
  localparam M6_VU = 23;
  localparam M6_HIT0 = 22;
  localparam M6_SELECT = 21;
  localparam M6_TIMING = 20;
  localparam M6_MSB_SIZE = 19;
  localparam M6_LSB_SIZE = 16;
  localparam M6_UNCERTAINEN = 5;

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
  localparam ADDR_DCSR = 12'h7b0;
  localparam ADDR_DPC = 12'h7b1;

  //DCSR:
  localparam MSB_CAUSE = 8;
  localparam LSB_CAUSE = 6;

  //Initial settings
  localparam TDATA1_DISABLED = 32'hF800_0000;
  localparam TDATA1_RESET = 32'h2800_1000;
  localparam MAX_NUM_TRIGGERS = 5;
  localparam MAX_MEM_ACCESS = 13; //Push and pop can do 13 memory access. TODO: XIF, can potentially do more, so for XIF assertion a_dt_max_memory_transaction might fail.
  localparam MAX_MEM_ACCESS_PLUS_ONE = 53'b1_0000__0000_0000_0000_0000__0000_0000_0000_0000__0000_0000_0000_0000;

  /////////// Signals ///////////

  logic [31:0] tdata1_pre_state;
  logic [31:0] tdata2_pre_state;
  logic [31:0] tinfo_pre_state;
  logic [31:0] tselect_pre_state;

  logic [31:0] tdata1_post_state;
  logic [31:0] tdata2_post_state;
  logic [31:0] tinfo_post_state;
  logic [31:0] tselect_post_state;

  always_comb begin
    tdata1_pre_state = tdata1_if.pre_state();
    tdata2_pre_state = tdata2_if.pre_state();
    tinfo_pre_state = tinfo_if.pre_state();
    tselect_pre_state = tselect_if.pre_state();
  end

  always_comb begin
    tdata1_post_state = tdata1_if.post_state();
    tdata2_post_state = tdata2_if.post_state();
    tinfo_post_state = tinfo_if.post_state();
    tselect_post_state = tselect_if.post_state();
  end


  logic valid_instr_in_mmode;
  assign valid_instr_in_mmode = rvfi_if.rvfi_valid
      && !rvfi_if.rvfi_trap
      && !rvfi_if.rvfi_dbg_mode
      && rvfi_if.is_mmode;

  logic valid_instr_in_umode;
  assign valid_instr_in_umode = rvfi_if.rvfi_valid
      && !rvfi_if.rvfi_dbg_mode
      && rvfi_if.is_umode;

  logic valid_instr_in_dmode;
  assign valid_instr_in_dmode = rvfi_if.rvfi_valid
      && !rvfi_if.rvfi_trap
      && rvfi_if.rvfi_dbg_mode;


  logic is_csrrw;
  logic is_csrrs;
  logic is_csrrc;
  logic is_csrrwi;
  logic is_csrrsi;
  logic is_csrrci;
  logic [4:0] csri_uimm;

  always_comb begin
    is_csrrw = rvfi_if.match_instr_isb(rvfi_if.INSTR_OPCODE_CSRRW);
    is_csrrs = rvfi_if.match_instr_isb(rvfi_if.INSTR_OPCODE_CSRRS);
    is_csrrc = rvfi_if.match_instr_isb(rvfi_if.INSTR_OPCODE_CSRRC);
    is_csrrwi = rvfi_if.match_instr_isb(rvfi_if.INSTR_OPCODE_CSRRWI);
    is_csrrsi = rvfi_if.match_instr_isb(rvfi_if.INSTR_OPCODE_CSRRSI);
    is_csrrci = rvfi_if.match_instr_isb(rvfi_if.INSTR_OPCODE_CSRRCI);
    csri_uimm = rvfi_if.rvfi_insn[19:15];
  end

  /////////// Sequences ///////////

  sequence seq_csr_read_mmode(csr_addr);
    @(posedge clknrst_if.clk)
    valid_instr_in_mmode
    && rvfi_if.is_csr_read(csr_addr)
    && rvfi_if.rvfi_rd1_addr != 0;
  endsequence

  sequence seq_csr_write_mmode(csr_addr);
    @(posedge clknrst_if.clk)
    valid_instr_in_mmode
    && rvfi_if.is_csr_write(csr_addr);
  endsequence

  sequence seq_csr_read_dmode(csr_addr);
    @(posedge clknrst_if.clk)
    valid_instr_in_dmode
    && rvfi_if.is_csr_read(csr_addr)
    && rvfi_if.rvfi_rd1_addr != 0;
  endsequence

  sequence seq_csr_write_dmode(csr_addr);
    @(posedge clknrst_if.clk)
    valid_instr_in_dmode
    && rvfi_if.is_csr_write(csr_addr);
  endsequence

  sequence seq_tdata1_m2_m6_or_disabled(t);
    @(posedge clknrst_if.clk)
    valid_instr_in_dmode
    && tselect_pre_state == t
    && (tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL
    || tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6
    || tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_DISABLED);
  endsequence

  sequence seq_etrigger_hit(t, priv_lvl, exception);
    @(posedge clknrst_if.clk)
    support_if.trigger_match_exception[t]
    && !rvfi_if.rvfi_dbg_mode
    && priv_lvl
    && rvfi_if.rvfi_trap.exception_cause == exception;
  endsequence


  /////////// Properties ///////////

  property p_dt_tcsr_not_implemented(tcsr);
    rvfi_if.is_csr_instr(tcsr) //make sure no bus fault exceptions has occured
    |->
    (rvfi_if.rvfi_trap.trap
    && rvfi_if.rvfi_trap.exception
    && (rvfi_if.rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN))

    // Trigger match on PC is registered before exceptions is registered
    || (rvfi_if.rvfi_trap.debug
    && rvfi_if.rvfi_trap.debug_cause == DBG_CAUSE_TRIGGER);
  endproperty

  property p_etrigger_hit(t, priv_lvl, exception);
    seq_etrigger_hit(t,priv_lvl, exception)
    |->
    rvfi_if.rvfi_trap.debug;
  endproperty

  property p_trigger_type(tselect_value, tdata1_type);
    tselect_pre_state == tselect_value
    && tdata1_pre_state[MSB_TYPE:LSB_TYPE] == tdata1_type;
  endproperty

  property p_csrrw_in_dmode(addr, csr_post_state);
    seq_csr_write_dmode(addr)
    ##0 is_csrrw
    |->
    csr_post_state == rvfi_if.rvfi_rs1_rdata;
  endproperty

  property p_csrrs_in_dmode(addr, csr_post_state);
    seq_csr_write_dmode(addr)
    ##0 is_csrrs
    |->
    csr_post_state == (tdata2_pre_state | rvfi_if.rvfi_rs1_rdata);
  endproperty

  property p_csrrc_in_dmode(addr, csr_post_state);
    seq_csr_write_dmode(addr)
    ##0 is_csrrc
    |->
    csr_post_state == (tdata2_pre_state & (~rvfi_if.rvfi_rs1_rdata));
  endproperty

  property p_csrrwi_in_dmode(addr, csr_post_state);
    seq_csr_write_dmode(addr)
    ##0 is_csrrwi
    |->
    csr_post_state == csri_uimm;
  endproperty

  property p_csrrsi_in_dmode(addr, csr_post_state);
    seq_csr_write_dmode(addr)
    ##0 is_csrrsi
    |->
    csr_post_state == (tdata2_pre_state | csri_uimm);
  endproperty

  property p_csrrci_in_dmode(addr, csr_post_state);
    seq_csr_write_dmode(addr)
    ##0 is_csrrci
    |->
    csr_post_state == (tdata2_pre_state & (~csri_uimm));
  endproperty


  /////////// Assertions and Coverages ///////////

  //Verify that it is only possible to do 13 Memory transactions:
  //TODO XIF: this might not be the case for xif, as it can potentionally do more:

  a_dt_max_memory_transaction: assert property (
    rvfi_if.rvfi_valid
    |->
    rvfi_if.rvfi_mem_rmask < MAX_MEM_ACCESS_PLUS_ONE
    && rvfi_if.rvfi_mem_wmask < MAX_MEM_ACCESS_PLUS_ONE
  );

  //- Vplan:
  //Verify that core enters debug mode when the trigger matches on instruction address. NB! According to spec, the tdataN registers can only be written from debug mode, as m-mode writes are ignored.

  //Enter debug mode by any of the above methods.
  //Write (randomized) breakpoint addr to tdata2 and enable breakpoint in tdata1[2]
  //Exit debug mode (dret instruction)
  //Verify that core enters debug mode on breakpoint addr
  //Current PC is saved to DPC
  //Cause of debug must be saved to DCSR (cause=2)
  //PC is updated to value on dm_haltaddr_i input
  //Core starts executing debug code

  //- Assertion verification:
  //1) Verify that core enters debug mode on breakpoint addr
  //2) Current PC is saved to DPC
  //3) Cause of debug must be saved to DCSR (cause=2)
  //4) PC is updated to value on dm_haltaddr_i input
  //5) Core starts executing debug code

  //1) see a_dt_instr_trigger_hit_*
  //2) - 5): Debug assertions uvmt_cv32e40s_debug_assert.sv


  //- Vplan:
  //Check that attempts to access "tcontrol" raise an illegal instruction exception, always. (Unless overruled by a higher priority.)

  //- Assertion verification:
  //1) Check that attempts to access "tcontrol" raise an illegal instruction exception, always. (Unless overruled by a higher priority.)

  //1)
  a_dt_tcontrol_not_implemented: assert property (
    p_dt_tcsr_not_implemented(ADDR_TCONTROL)
  ) else `uvm_error(info_tag, "Access to tcontrol does not cause an illegal exception (when no higher priority exception has occured)\n");


  //- Vplan:
  //Check that attempts to access "tdata3" raise an illegal instruction exception, always. (Unless overruled by a higher priority.)

  //- Assertion verification:
  //1) Check that attempts to access "tdata3" raise an illegal instruction exception, always. (Unless overruled by a higher priorit

  //1)
  a_dt_tdata3_not_implemented: assert property (
    p_dt_tcsr_not_implemented(ADDR_TDATA3)
  ) else `uvm_error(info_tag, "Access to tdata3 does not cause an illegal exception (when no higher priority exception has occured)\n");

  //- Vplan:
  //Have 0 triggers, access any trigger register and check that illegal instruction exception occurs.
  //Check that no triggers ever fire. Check that "tselect" is 0.

  //- Assertion verification:
  //1) Have 0 triggers, access any trigger register and check that illegal instruction exception occurs
  //2) Have 0 triggers, No trigger ever fires

  if (CORE_PARAM_DBG_NUM_TRIGGERS == 0) begin

    //1)
    a_dt_0_triggers_tdata1_access: assert property (
        (rvfi_if.is_csr_instr(ADDR_TSELECT)
      || rvfi_if.is_csr_instr(ADDR_TDATA1)
      || rvfi_if.is_csr_instr(ADDR_TDATA2)
      || rvfi_if.is_csr_instr(ADDR_TINFO))

      |->
      rvfi_if.rvfi_trap.trap
      && rvfi_if.rvfi_trap.exception
      && (rvfi_if.rvfi_trap.exception_cause == EXC_CAUSE_ILLEGAL_INSN)

    ) else `uvm_error(info_tag, "There are no triggers, but accessing trigger SCRs does not cause exceptions.\n");

    //2)
    a_dt_0_triggers_no_triggering: assert property (
      rvfi_if.rvfi_valid
      |->
      rvfi_if.rvfi_dbg != TRIGGER_MATCH

    ) else `uvm_error(info_tag, "There are no triggers, but debug cause indicate a trigger match.\n");

  end // if CORE_PARAM_DBG_NUM_TRIGGERS == 0


    //- Vplan:
  //For all number of triggers, use tselect to exercise each trigger with each supported type.
  //(Also try writing to higher "tselect" than supported and check that a supported number is read back.)
  //Make the triggers fire and check that debug mode is entered. Check also that the four context registers trap when accessed.

  //- Assertion verification:
  //1) Check also that the four context registers trap when accessed.
  //2) For all number of triggers, use tselect to exercise each trigger with each supported type
  //3) Make the triggers fire and check that debug mode is entered.
  //4) Writing to higher "tselect" than supported, check that a supported number is read back


  //1)
  a_dt_access_context: assert property (
    (rvfi_if.is_csr_instr(ADDR_MCONTEXT)
    || rvfi_if.is_csr_instr(ADDR_MSCONTEXT)
    || rvfi_if.is_csr_instr(ADDR_HCONTEXT)
    || rvfi_if.is_csr_instr(ADDR_SCONTEXT))

    |->
    rvfi_if.rvfi_trap.trap
  ) else `uvm_error(info_tag, "Accessing context registers does not trap.\n");


  // Assertions and coverages for when debug triggers are enabled:

  if (CORE_PARAM_DBG_NUM_TRIGGERS > 0) begin

    //2)
    for (genvar i = 0; i < CORE_PARAM_DBG_NUM_TRIGGERS; i++) begin

      c_dt_trigger_i_has_type_mcontrol: cover property(
        p_trigger_type(i, TTYPE_MCONTROL)
      );

      c_dt_trigger_i_has_type_etrigger: cover property(
        p_trigger_type(i, TTYPE_ETRIGGER)
      );

      c_dt_trigger_i_has_type_mcontrol6: cover property(
        p_trigger_type(i, TTYPE_MCONTROL6)
      );

      c_dt_trigger_i_has_type_disable: cover property(
        p_trigger_type(i, TTYPE_DISABLED)
      );

    end

    //3) see a_dt_instr_trigger_hit_*, a_dt_load_trigger_hit_*, a_dt_store_trigger_hit_*, a_dt_exception_trigger_hit_*, a_dt_enter_dbg_reason

    //4)
    a_dt_tselect_higher_than_dbg_num_triggers: assert property(
      rvfi_if.rvfi_valid
      |->
      tselect_post_state < CORE_PARAM_DBG_NUM_TRIGGERS
    ) else `uvm_error(info_tag, "The CSR tselect is set to equal or higher than the number of trigger.\n");


    // Make sure the tdata1 array corresponds with the tdata1 csr.
    a_dt_tdata1_array: assert property(
      rvfi_if.rvfi_valid
      |->
      tdata1_array[tselect_post_state[$clog2(CORE_PARAM_DBG_NUM_TRIGGERS+1)-1:0]] == tdata1_post_state
    ) else `uvm_error(info_tag, "Verify that the tdata1 array is correct by compearing it with the tdata1 post state signal.\n");


    //- Vplan:
    //Configure triggers for load/store/execute and combinations of them, configure tdata2,
    //cause triggers to fire and check that debug mode is entered correctly.
    //Also check that the tied fields are tied. All of these configurations must be crossed, also against match conditions.

    //- Assertion verification:
    //1) trigger on loads if the load setting in tdata1 is set high
    //2) trigger on stores if the store setting in tdata1 is set high
    //3) trigger on instructions if the execute setting in tdata1 is set high
    //4) check that the tied fields are tied

    //1) - 3) see a_dt_instr_trigger_hit_*, a_dt_load_trigger_hit_*, a_dt_store_trigger_hit_*

    //4)
    a_dt_tie_offs_tselect: assert property (
      rvfi_if.rvfi_valid

      |->
      !tselect_pre_state[31:CORE_PARAM_DBG_NUM_TRIGGERS-1]
    ) else `uvm_error(info_tag, "There is a problem with tselect's tied off fields.\n");


    //mcontrol
    a_dt_tie_offs_tdata1_mcontrol: assert property (
      rvfi_if.rvfi_valid
      && tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL

      |->
      tdata1_pre_state[DMODE]
      && !tdata1_pre_state[MSB_MASKMAX:LSB_MASKMAX]
      && !tdata1_pre_state[M2_HIT]
      && !tdata1_pre_state[M2_SELECT]
      && !tdata1_pre_state[M2_TIMING]
      && !tdata1_pre_state[M2_MSB_SIZELO:M2_LSB_SIZELO]
      && tdata1_pre_state[MSB_ACTION:LSB_ACTION] == ENTER_DBG_ON_MATCH
      && !tdata1_pre_state[CHAIN]
      && !tdata1_pre_state[5]
      && !tdata1_pre_state[M2_M6_S_MODE]
    ) else `uvm_error(info_tag, "There is a problem with tdata1-mcontrol's tied off fields.\n");

    //etrigger
    a_dt_tie_offs_tdata1_etrigger: assert property (
      rvfi_if.rvfi_valid
      && tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER

      |->
      tdata1_pre_state[DMODE]
      && !tdata1_pre_state[ET_HIT]
      && !tdata1_pre_state[25:13]
      && !tdata1_pre_state[ET_VS]
      && !tdata1_pre_state[ET_VU]
      && !tdata1_pre_state[10]
      && !tdata1_pre_state[8]
      && !tdata1_pre_state[ET_S]
      && tdata1_pre_state[ET_MSB_ACTION:ET_LSB_ACTION] == ENTER_DBG_ON_MATCH
    ) else `uvm_error(info_tag, "There is a problem with tdata1-etrigger's tied off fields.\n");

    //mcontrol6
    a_dt_tie_offs_tdata1_mcontrol6: assert property (
      rvfi_if.rvfi_valid
      && tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6

      |->
      tdata1_pre_state[DMODE]
      && !tdata1_pre_state[M6_UNCERTAIN]
      && !tdata1_pre_state[M6_VS]
      && !tdata1_pre_state[M6_VU]
      && !tdata1_pre_state[M6_SELECT]
      && !tdata1_pre_state[20:19]
      && !tdata1_pre_state[M6_MSB_SIZE:M6_LSB_SIZE]
      && tdata1_pre_state[MSB_ACTION:LSB_ACTION] == ENTER_DBG_ON_MATCH
      && !tdata1_pre_state[CHAIN]
      && !tdata1_pre_state[M6_UNCERTAINEN]
      && !tdata1_pre_state[M2_M6_S_MODE]
    ) else `uvm_error(info_tag, "There is a problem with tdata1-mcontrol6's tied off fields.\n");

    //disabled
    a_dt_tie_offs_tdata1_disabled: assert property (
      rvfi_if.rvfi_valid
      && tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_DISABLED

      |->
      tdata1_pre_state[DMODE]
      && !tdata1_pre_state[DIS_MSB_DATA:DIS_LSB_DATA]
    ) else `uvm_error(info_tag, "There is a problem with tdata1-disabled's tied off fields.\n");


    a_dt_tie_offs_tdata2_etrigger: assert property (
      rvfi_if.rvfi_valid
      && tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER

      |->
      !tdata2_pre_state[31:26]
      && !tdata2_pre_state[23:12]
      && !tdata2_pre_state[10:9]
      && !tdata2_pre_state[6]
      && !tdata2_pre_state[4]
      && !tdata2_pre_state[0]
    ) else `uvm_error(info_tag, "There is a problem with tdata2-etrigger's tied off fields.\n");


    a_dt_tie_offs_tinfo: assert property (
      rvfi_if.rvfi_valid
      |->
      tinfo_pre_state[VERSION_MSB:VERSION_LSB] == 1
      && !tinfo_pre_state[23:16]
      && tinfo_pre_state[INFO_MSB:INFO_LSB] == 16'h8064
    ) else `uvm_error(info_tag, "There is a problem with tinfo's tied off fields.\n");


    //- Vplan:
    //Have triggers configured to be able to match, but enable/disable their corresponding mode bit, check that the trigger is either able to fire or is blocked from firing accordingly. Also check the tied values.

    //- Assertion verification:
    //1) but enable/disable their corresponding mode bit, check that the trigger is either able to fire or is blocked from firing accordingly, using different match configurations.
    //2) Also check the tied values. (P20-P21: 4))


    //1) see a_dt_instr_trigger_hit_*, a_dt_load_trigger_hit_*, a_dt_store_trigger_hit_*, a_dt_exception_trigger_hit_*, a_dt_enter_dbg_reason
    //2) see a_dt_tie_offs_*


    //- Vplan:
    //Check that these types can be selected, and check that no other types can be selected. (Functionality of these types should be handled by other items in this plan.) Check also that the default is "15".

    //- Assertion verification:
    //1) Sjekk at tdata1 type kun kan være 2, 6, 5 eller 15


    //1)
    a_dt_tdata1_types: assert property (
      rvfi_if.rvfi_valid
      |->
      tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL
      || tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER
      || tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6
      || tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_DISABLED
    ) else `uvm_error(info_tag, "tdata1 type is neither mcontrol, etrigger, mcontrol6 or disabled.\n");


    //- Vplan:
    //Try to write tdata registers outside of debug mode, check that they are not writable. Try changing "tdata1.dmode" and check that it is WARL (0x1). Cross the above checks with all supported types.

    //- Assertion verification:
    //1) write tdata registers outside of debug mode, check that they are not writable
    //2) Try changing "tdata1.dmode" and check that it is WARL (0x1)


    //1)
    a_dt_not_access_tdata1_dbg_mode: assert property (
      !rvfi_if.rvfi_dbg_mode
      && rvfi_if.is_csr_instr(ADDR_TDATA1)
      |->
      !tdata1_if.rvfi_csr_wmask
      //or m6 hit bits are set due to trigger match
      || (rvfi_if.rvfi_trap.debug
      && rvfi_if.rvfi_trap.debug_cause == DBG_CAUSE_TRIGGER
      && tdata1_pre_state[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6)
    ) else `uvm_error(info_tag, "Writing tdata1 in non-debug mode succeeds.\n");


    a_dt_not_access_tdata2_dbg_mode: assert property (
      !rvfi_if.rvfi_dbg_mode
      && rvfi_if.is_csr_instr(ADDR_TDATA2)

      |->
      !tdata2_if.rvfi_csr_wmask
    ) else `uvm_error(info_tag, "Writing tdata2 in non-debug mode succeeds.\n");


    //2)
    a_dt_dmode: assert property (
      seq_csr_write_dmode(ADDR_TDATA1)
      ##0 !rvfi_if.rvfi_trap.trap
      |->
      tdata1_post_state[DMODE]
    ) else `uvm_error(info_tag, "Setting tdata1's dmode bit to 0 succeeds.\n");


    //- Vplan:
    //When num triggers is more than 0, check that "tinfo.info" is "1" for the three supported types, "tinfo.version" is 0x1, and that the remaining bits are 0.

    //- Assertion verification:
    //1) When num triggers is more than 0, check that "tinfo.info" is "1" for the three supported types, "tinfo.version" is 0x1, and that the remaining bits are 0.

    //1)
    a_dt_triggers_tinfo: assert property (
      CORE_PARAM_DBG_NUM_TRIGGERS != '0
      && rvfi_if.rvfi_valid
      |->
      !tinfo_pre_state[1:0]
      && tinfo_pre_state[TTYPE_MCONTROL]
      && !tinfo_pre_state[4:3]
      && tinfo_pre_state[TTYPE_ETRIGGER]
      && tinfo_pre_state[TTYPE_MCONTROL6]
      && !tinfo_pre_state[14:7]
      && tinfo_pre_state[TTYPE_DISABLED]
      && tinfo_pre_state[VERSION_MSB:VERSION_LSB] == 1

    ) else `uvm_error(info_tag, "tinfo does not indicated that only tdata type mcontrol, etrigger, mcontrol6 and disabled are allowed.\n");


    //- Vplan:
    //Configure an exception trigger, use the privmode bits to disable/enable the trigger, exercise the trigger conditions, check that it fires/not accordingly. Also check the WARL fields.

    //- Assertion verification:
    //1) Configure an exception trigger, use the privmode bits to disable/enable the trigger, exercise the trigger conditions, check that it fires/not accordingly.
    //2) Check the WARL fields


    //1) see a_dt_exception_trigger_hit_*, a_dt_enter_dbg_reason

    //2)
    a_dt_warl_tselect: assert property (
      rvfi_if.rvfi_valid
      && |tselect_if.rvfi_csr_wmask != 0
      |->
      tselect_post_state < CORE_PARAM_DBG_NUM_TRIGGERS
    ) else `uvm_error(info_tag, "There is a problem with tselect's WARL fields.\n");

    a_dt_warl_tdata1_general: assert property (
      rvfi_if.rvfi_valid
      && |tdata1_if.rvfi_csr_wmask != 0
      |->
      (tdata1_post_state[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL
      || tdata1_post_state[MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER
      || tdata1_post_state[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6
      || tdata1_post_state[MSB_TYPE:LSB_TYPE] == TTYPE_DISABLED)
      && tdata1_post_state[DMODE]
    ) else `uvm_error(info_tag, "There is a problem with tdata1's general WARL fields.\n");

    a_dt_warl_tdata1_m2: assert property (
      rvfi_if.rvfi_valid
      && |tdata1_if.rvfi_csr_wmask != 0
      && tdata1_post_state[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL
      |->
      !tdata1_post_state[MSB_MASKMAX:LSB_MASKMAX]
      && !tdata1_post_state[M2_HIT]
      && !tdata1_post_state[M2_SELECT]
      && !tdata1_post_state[M2_TIMING]
      && !tdata1_post_state[M2_MSB_SIZELO:M2_LSB_SIZELO]
      && tdata1_post_state[MSB_ACTION:LSB_ACTION] == ENTER_DBG_ON_MATCH
      && !tdata1_post_state[CHAIN]
      && (tdata1_post_state[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL
      || tdata1_post_state[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL
      || tdata1_post_state[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER)
      && !tdata1_post_state[5]
      && !tdata1_post_state[M2_M6_S_MODE]
    ) else `uvm_error(info_tag, "There is a problem with tdata1-mcontrol's WARL fields.\n");

    a_dt_warl_tdata1_etrigger: assert property (
      rvfi_if.rvfi_valid
      && |tdata1_if.rvfi_csr_wmask != 0
      && tdata1_post_state[MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER
      |->
      !tdata1_post_state[ET_HIT]
      && !tdata1_post_state[25:13]
      && !tdata1_post_state[ET_VS]
      && !tdata1_post_state[ET_VU]
      && !tdata1_post_state[10]
      && !tdata1_post_state[8]
      && !tdata1_post_state[ET_S]
      && tdata1_post_state[ET_MSB_ACTION:ET_LSB_ACTION] == ENTER_DBG_ON_MATCH
    ) else `uvm_error(info_tag, "There is a problem with tdata1-etrigger's WARL fields.\n");

    a_dt_warl_tdata1_m6: assert property (
      rvfi_if.rvfi_valid
      && |tdata1_if.rvfi_csr_wmask != 0
      && tdata1_post_state[MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6
      |->
      tdata1_post_state[DMODE]
      && !tdata1_post_state[M6_UNCERTAIN]
      && ({tdata1_post_state[M6_HIT1], tdata1_post_state[M6_HIT0]} == 0
      || {tdata1_post_state[M6_HIT1], tdata1_post_state[M6_HIT0]} == 1)
      && !tdata1_post_state[M6_VS]
      && !tdata1_post_state[M6_VU]
      && !tdata1_post_state[M6_SELECT]
      && !tdata1_post_state[20:19]
      && !tdata1_post_state[M6_MSB_SIZE:M6_LSB_SIZE]
      && tdata1_post_state[MSB_ACTION:LSB_ACTION] == ENTER_DBG_ON_MATCH
      && !tdata1_post_state[CHAIN]
      && (tdata1_post_state[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL
      || tdata1_post_state[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL
      || tdata1_post_state[MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER)
      && !tdata1_post_state[M6_UNCERTAINEN]
      && !tdata1_post_state[M2_M6_S_MODE]
    ) else `uvm_error(info_tag, "There is a problem with tdata1-mcontrol6's WARL fields.\n");

    a_dt_warl_tdata1_disabled: assert property (
      rvfi_if.rvfi_valid
      && |tdata1_if.rvfi_csr_wmask != 0
      && tdata1_post_state[MSB_TYPE:LSB_TYPE] == TTYPE_DISABLED
      |->
      !tdata1_post_state[DIS_MSB_DATA:DIS_LSB_DATA]
    ) else `uvm_error(info_tag, "There is a problem with tdata1-disabled's WARL fields.\n");

    a_dt_warl_tdata2_etrigger: assert property (
      rvfi_if.rvfi_valid
      && |tdata2_if.rvfi_csr_wmask != 0
      && tdata1_post_state[MSB_TYPE:LSB_TYPE] == TTYPE_ETRIGGER
      |->
      !tdata2_post_state[31:26]
      && !tdata2_post_state[23:12]
      && !tdata2_post_state[10:9]
      && !tdata2_post_state[6]
      && !tdata2_post_state[4]
      && !tdata2_post_state[0]
    ) else `uvm_error(info_tag, "There is a problem with tdata1-etrigger's WARL fields.\n");

    a_dt_warl_tinfo: assert property (
      rvfi_if.rvfi_valid
      && |tinfo_if.rvfi_csr_wmask != 0
      |->
      !tinfo_post_state[23:16]
    ) else `uvm_error(info_tag, "There is a problem with tinfo's WARL fields.\n");


    //- Vplan:
    //Access all tdata registers in M-mode and observe writes have no effects and reads should reflect register content.
    //Access registers from D-mode and observe full R/W access.
    //Access from U-mode and observe no access at all.

    // - Assertion verification:
    //1) Verify that all tdata registers can be read in machine mode, but that writes do not have any effect
    //2) Verify that all tdata registers can be read in debug mode, and that writes have an effect
    //3) Verify that the tdata registers are unaccessible in user mode

    //1)
    a_dt_no_write_access_to_tdata_in_mmode: assert property (

      valid_instr_in_mmode
      && !rvfi_if.rvfi_dbg_mode
      |->
      (!tdata1_if.rvfi_csr_wmask
      && !tdata2_if.rvfi_csr_wmask)

      // A write to tselect will make the core display new tdata values, and consequently write the tdata csrs.
      || rvfi_if.is_csr_write(ADDR_TSELECT)

    ) else `uvm_error(info_tag, "The t-CSRs are written in machine mode (not debug mode), and the write changes the CSRs values.\n");

    c_dt_write_tdata1_in_mmode: cover property (
      seq_csr_write_mmode(ADDR_TDATA1)
    );

    c_dt_write_tdata2_in_mmode: cover property (
      seq_csr_write_mmode(ADDR_TDATA2)
    );

    a_dt_read_access_to_tdata1_in_mmode: assert property (
      seq_csr_read_mmode(ADDR_TDATA1)
      |->
      rvfi_if.rvfi_rd1_wdata == tdata1_pre_state
    ) else `uvm_error(info_tag, "No read access to tdata1 in machine mode.\n");

    a_dt_read_access_to_tdata2_in_mmode: assert property (
      seq_csr_read_mmode(ADDR_TDATA2)
      |->
      rvfi_if.rvfi_rd1_wdata == tdata2_pre_state
    ) else `uvm_error(info_tag, "No read access to tdata2 in machine mode.\n");


    //2)
    a_dt_write_access_to_tdata1_in_dmode: assert property (
      p_csrrw_in_dmode(ADDR_TDATA1, tdata1_post_state)
      or p_csrrs_in_dmode(ADDR_TDATA1, tdata1_post_state)
      or p_csrrc_in_dmode(ADDR_TDATA1, tdata1_post_state)
      or p_csrrwi_in_dmode(ADDR_TDATA1, tdata1_post_state)
      or p_csrrsi_in_dmode(ADDR_TDATA1, tdata1_post_state)
      or p_csrrci_in_dmode(ADDR_TDATA1, tdata1_post_state)
    ) else `uvm_error(info_tag, "No write access to tdata1 in debug mode.\n");

    a_dt_write_access_to_tdata2_in_dmode: assert property (
      p_csrrw_in_dmode(ADDR_TDATA2, tdata2_post_state)
      or p_csrrs_in_dmode(ADDR_TDATA2, tdata2_post_state)
      or p_csrrc_in_dmode(ADDR_TDATA2, tdata2_post_state)
      or p_csrrwi_in_dmode(ADDR_TDATA2, tdata2_post_state)
      or p_csrrsi_in_dmode(ADDR_TDATA2, tdata2_post_state)
      or p_csrrci_in_dmode(ADDR_TDATA2, tdata2_post_state)
    ) else `uvm_error(info_tag, "No write access to tdata2 in debug mode.\n");


    a_dt_read_access_to_tdata1_in_dmode: assert property (
      seq_csr_read_dmode(ADDR_TDATA1)
      |->
      rvfi_if.rvfi_rd1_wdata == tdata1_pre_state
    ) else `uvm_error(info_tag, "No read access to tdata1 in debug mode.\n");

    a_dt_read_access_to_tdata2_in_dmode: assert property (
      seq_csr_read_dmode(ADDR_TDATA2)
      |->
      rvfi_if.rvfi_rd1_wdata == tdata2_pre_state
    ) else `uvm_error(info_tag, "No read access to tdata2 in debug mode.\n");


    //3)
    a_dt_no_access_to_tdata_in_umode: assert property (

      valid_instr_in_umode

      && (rvfi_if.is_csr_instr(ADDR_TDATA1)
      || rvfi_if.is_csr_instr(ADDR_TDATA2))

      |->
      rvfi_if.rvfi_trap.trap
    ) else `uvm_error(info_tag, "Access to the t-CSRs in user mode.\n");


    //- Vplan:
    //Write 0 to "tdata1", ensure that its state becomes disabled (type 15). Write values to "tdata2" (addresses and/or exception causes)
    //and exercise would-have-been triggers and check that the trigger does not fire.

    //- Assertion verification:
    //1) Write 0 to "tdata1", ensure that its state becomes disabled (type 15).
    //2) Write values to "tdata2" (addresses and/or exception causes) and exercise would-have-been triggers and check that the trigger does not fire (because tdata1 is in disabled state).


    //1)
    a_dt_write_0_to_tdata1: assert property (
      seq_csr_write_dmode(ADDR_TDATA1)

      ##0 rvfi_if.is_csr_write(ADDR_TDATA1)

      && ((rvfi_if.rvfi_insn[14:12] == 3'b001 //write
      && rvfi_if.rvfi_rs1_rdata == '0)

      || (rvfi_if.rvfi_insn[14:12] == 3'b011 //clear
      && rvfi_if.rvfi_rs1_rdata == 32'hFFFF_FFFF)

      || (rvfi_if.rvfi_insn[14:12] == 3'b101 //write immediate
      && rvfi_if.csri_uimm == '0)

      || (rvfi_if.rvfi_insn[14:12] == 3'b111 //clear immediate
      && rvfi_if.csri_uimm == 5'h1F
      && tdata1_pre_state[31:6] == '0))

      |->
      tdata1_post_state == TDATA1_DISABLED
    ) else `uvm_error(info_tag, "Writing 0 to tdata1 does not set tdata1 into disabled state.\n");


    //2) see a_dt_enter_dbg_reason


    //- Vplan:
    //Read the state of all triggers, write to tdata1/2 (using all types in tdata1), read back the state of all triggers and
    //check that nothing got changes except the one "tdata*" register that was written.

    //- Assertion verification:
    //1) write to tdata1/2/3 and check that nothing got changes except the one "tdata*" register that was written

    //1)
    a_dt_write_only_tdata1: assert property (
      seq_csr_write_dmode(ADDR_TDATA1)
      |->
      !tdata2_if.rvfi_csr_wmask
    ) else `uvm_error(info_tag, "A write to tdata1 writes tdata2 as well.\n");

    a_dt_write_only_tdata2: assert property (
      seq_csr_write_dmode(ADDR_TDATA2)
      |->
      !tdata1_if.rvfi_csr_wmask
    ) else `uvm_error(info_tag, "A write to tdata2 writes tdata1 as well.\n");


    //- Vplan:
    //Bring core into debug and enable a trigger on the PC (pointing to the debug program buffer).
    //Continue execution in debug, and observe that no action is taken when the trigger matches.

    //- Assertion verification:
    //1) Bring core into debug and observe that no action is taken when there are trigger matches


    //1)
    a_dt_no_actions_on_trigger_matches_in_debug_dcsr: assert property (
      rvfi_if.rvfi_valid
      && rvfi_if.rvfi_dbg_mode
      && dcsr_if.rvfi_csr_wmask
      |->
      //If DCSR is written (wmask != 0) there must have been a csr write operation, and not due to a sideeffect of a trigger match
      rvfi_if.is_csr_write(ADDR_DCSR)
    ) else `uvm_error(info_tag, "Action is taken when there is a trigger match while in debug mode (dcsr is changed even though we dont do a dcsr write operation).\n");

    a_dt_no_actions_on_trigger_matches_in_debug_dpc: assert property (
      rvfi_if.rvfi_valid
      && rvfi_if.rvfi_dbg_mode
      && dpc_if.rvfi_csr_wmask
      |->
      //If DPC is written (wmask != 0) there must have been a csr write operation, and not due to a sideeffect of a trigger match
      rvfi_if.is_csr_write(ADDR_DPC)
    ) else `uvm_error(info_tag, "Action is taken when there is a trigger match while in debug mode (dpc is changed even though we dont do a dpc write operation).\n");


    for (genvar t = 0; t < CORE_PARAM_DBG_NUM_TRIGGERS; t++) begin

      //- Vplan:
      //Configure "tdata1" and "tdata2" to fire on exceptions, try both individual and multiple exceptions in addition to supported and unsupported. Exercise scenarios that would trigger or not trigger according to the configuration and check that debug mode is either entered or not entered accordingly, and that the entry goes correctly (pc, dpc, cause, etc).

      //- Assertion verification:
      //1) Verify that we enter debug when triggering the enabled exceptions
      //2) Verify that we do not enter debug when triggering unenabled exceptions

      //1)
      //TODO: krdosvik, fails, need rtl fix.
      /*a_dt_exception_trigger_hit_m_instr_access_fault: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_mmode,
          EXC_CAUSE_INSTR_FAULT)
      ) else `uvm_error(info_tag, "The trigger match (exception match, machine mode, instruction fault) does not send the core into debug mode.\n");*/

      a_dt_exception_trigger_hit_u_instr_access_fault: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_umode,
          EXC_CAUSE_INSTR_FAULT)
      ) else `uvm_error(info_tag, "The trigger match (exception match, user mode, instruction fault) does not send the core into debug mode.\n");

      a_dt_exception_trigger_hit_m_illegal_instr: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_mmode,
          EXC_CAUSE_ILLEGAL_INSN)
      ) else `uvm_error(info_tag, "The trigger match (exception match, machine mode, illegal instruction) does not send the core into debug mode.\n");

      a_dt_exception_trigger_hit_u_illegal_instr: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_umode,
          EXC_CAUSE_ILLEGAL_INSN)
      ) else `uvm_error(info_tag, "The trigger match (exception match, user mode, illegal instruction) does not send the core into debug mode.\n");

      a_dt_exception_trigger_hit_m_breakpoint: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_mmode,
          EXC_CAUSE_BREAKPOINT)
      ) else `uvm_error(info_tag, "The trigger match (exception match, machine mode, breakpoint in machine mode) does not send the core into debug mode.\n");

      a_dt_exception_trigger_hit_u_breakpoint: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_umode,
          EXC_CAUSE_BREAKPOINT)
      ) else `uvm_error(info_tag, "The trigger match (exception match, user mode, breakpoint in user mode) does not send the core into debug mode.\n");

      a_dt_exception_trigger_hit_m_load_access_fault: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_mmode,
          EXC_CAUSE_LOAD_FAULT)
      ) else `uvm_error(info_tag, "The trigger match (exception match, machine mode, load access fault) does not send the core into debug mode.\n");

      a_dt_exception_trigger_hit_u_load_access_fault: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_umode,
          EXC_CAUSE_LOAD_FAULT)
      ) else `uvm_error(info_tag, "The trigger match (exception match, user mode, load access fault) does not send the core into debug mode.\n");

      a_dt_exception_trigger_hit_m_store_AMO_access_fault: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_mmode,
          EXC_CAUSE_STORE_FAULT)
      ) else `uvm_error(info_tag, "The trigger match (exception match, machine mode, stor/AMO access fault) does not send the core into debug mode.\n");

      a_dt_exception_trigger_hit_u_store_AMO_access_fault: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_umode,
          EXC_CAUSE_STORE_FAULT)
      ) else `uvm_error(info_tag, "The trigger match (exception match, user mode, stor/AMO access fault) does not send the core into debug mode.\n");

      a_dt_exception_trigger_hit_m_mecall: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_mmode,
          EXC_CAUSE_ECALL_MMODE)
      ) else `uvm_error(info_tag, "The trigger match (exception match, machine mode, ecall in machine mode) does not send the core into debug mode.\n");

      a_dt_exception_trigger_hit_u_uecall: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_umode,
          EXC_CAUSE_ECALL_UMODE)
      ) else `uvm_error(info_tag, "The trigger match (exception match, user mode, ecall in user mode) does not send the core into debug mode.\n");

      //TODO: krdosvik, fails, need rtl fix.
      /*a_dt_exception_trigger_hit_m_instr_bus_fault: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_mmode,
          EXC_CAUSE_INSTR_BUS_FAULT)
      ) else `uvm_error(info_tag, "The trigger match (exception match, machine mode, instruction bus fault) does not send the core into debug mode.\n");*/

      a_dt_exception_trigger_hit_u_instr_bus_fault: assert property(
        p_etrigger_hit(
          t,
          rvfi_if.is_umode,
          EXC_CAUSE_INSTR_BUS_FAULT)
      ) else `uvm_error(info_tag, "The trigger match (exception match, user mode, instruction bus fault) does not send the core into debug mode.\n");

      //TODO: krdosvik, fails, need rtl fix.
      /*if (INTEGRITY_ERRORS_ENABLED) begin

        a_glitch_dt_exception_trigger_hit_m_instr_integrity_fault: assert property(
          p_etrigger_hit(
            t,
            rvfi_if.is_mmode,
            EXC_CAUSE_INSTR_INTEGRITY_FAULT)
        ) else `uvm_error(info_tag, "The trigger match (exception match, machine mode, instruction integrity fault) does not send the core into debug mode.\n");

        a_glitch_dt_exception_trigger_hit_u_instr_integrity_fault: assert property(
          p_etrigger_hit(
            t,
            rvfi_if.is_umode,
            EXC_CAUSE_INSTR_INTEGRITY_FAULT)
        ) else `uvm_error(info_tag, "The trigger match (exception match, user mode, instruction integrity fault) does not send the core into debug mode.\n");

      end else begin

        a_glitch_dt_exception_trigger_hit_m_instr_integrity_fault_noprecondition: assert property(
          not seq_etrigger_hit(
            t,
            rvfi_if.is_mmode,
            EXC_CAUSE_INSTR_INTEGRITY_FAULT)
        ) else `uvm_error(info_tag, "exception trigger hit precondition is met for machine mode even though we assueme no integrity faults.\n");

        a_glitch_dt_exception_trigger_hit_u_instr_integrity_fault_noprecondition: assert property(
          not seq_etrigger_hit(
            t,
            rvfi_if.is_umode,
            EXC_CAUSE_INSTR_INTEGRITY_FAULT)
        ) else `uvm_error(info_tag, "exception trigger hit precondition is met for user mode even though we assueme no integrity faults.\n");

      end*/

      //2) see a_dt_enter_dbg_reason


      //- Assertion verification:
      //1) Verify that we enter debug when triggering the enabled instruction, memory address or exception
      //2) Verify that we do not enter debug when triggering unenabled instruction, memory address or exception

      //It is possible to formulate an assertions for general verification of instruction triggering,
      //However, to reduce convergence time we verify this trigger feature with several more constricted assertions:

      a_dt_instr_trigger_hit_mmode_match_when_equal: assert property (
        rvfi_if.is_mmode
        && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL
        && support_if.trigger_match_execute[t]
        && !rvfi_if.rvfi_dbg_mode
        |->
        rvfi_if.rvfi_trap.debug
      ) else `uvm_error(info_tag, "The trigger match (instruction match, machine mode, match when equal) does not send the core into debug mode.\n");

      a_dt_instr_trigger_hit_umode_match_when_equal: assert property (
        rvfi_if.is_umode
        && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL
        && support_if.trigger_match_execute[t]
        && !rvfi_if.rvfi_dbg_mode
        |->
        rvfi_if.rvfi_trap.debug
      ) else `uvm_error(info_tag, "The trigger match (instruction match, user mode, match when equal) does not send the core into debug mode.\n");

      a_dt_instr_trigger_hit_mmode_match_when_equal_or_greater: assert property (
        rvfi_if.is_mmode
        && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL
        && support_if.trigger_match_execute[t]
        && !rvfi_if.rvfi_dbg_mode
        |->
        rvfi_if.rvfi_trap.debug
      ) else `uvm_error(info_tag, "The trigger match (instruction match, machine mode, match when greater or equal) does not send the core into debug mode.\n");

      a_dt_instr_trigger_hit_umode_match_when_equal_or_greater: assert property (
        rvfi_if.is_umode
        && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL
        && support_if.trigger_match_execute[t]
        && !rvfi_if.rvfi_dbg_mode
        |->
        rvfi_if.rvfi_trap.debug
      ) else `uvm_error(info_tag, "The trigger match (instruction match, user mode, match when greater or equal) does not send the core into debug mode.\n");

      a_dt_instr_trigger_hit_mmode_match_when_lesser: assert property (
        rvfi_if.is_mmode
        && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER
        && support_if.trigger_match_execute[t]
        && !rvfi_if.rvfi_dbg_mode
        |->
        rvfi_if.rvfi_trap.debug
      ) else `uvm_error(info_tag, "The trigger match (instruction match, machine mode, match when lesser) does not send the core into debug mode.\n");

      a_dt_instr_trigger_hit_umode_match_when_lesser: assert property (
        rvfi_if.is_umode
        && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER
        && support_if.trigger_match_execute[t]
        && !rvfi_if.rvfi_dbg_mode
        |->
        rvfi_if.rvfi_trap.debug
      ) else `uvm_error(info_tag, "The trigger match (instruction match, user mode, match when lesser) does not send the core into debug mode.\n");


      for (genvar n = 0; n < MAX_MEM_ACCESS; n++) begin

        a_dt_load_trigger_hit_mmode_match_when_equal: assert property (
          rvfi_if.is_mmode
          && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL
          && rvfi_if.is_load_instr
          && support_if.trigger_match_mem[t]
          && !rvfi_if.rvfi_dbg_mode
          |->
          rvfi_if.rvfi_trap.debug
        ) else `uvm_error(info_tag, "The trigger match (load match, machine mode, match when equal) does not send the core into debug mode.\n");

        a_dt_load_trigger_hit_umode_match_when_equal: assert property (
          rvfi_if.is_umode
          && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL
          && rvfi_if.is_load_instr
          && support_if.trigger_match_mem[t]
          && !rvfi_if.rvfi_dbg_mode
          |->
          rvfi_if.rvfi_trap.debug
        ) else `uvm_error(info_tag, "The trigger match (load match, user mode, match when equal) does not send the core into debug mode.\n");

        a_dt_load_trigger_hit_mmode_match_when_equal_or_greater: assert property (
          rvfi_if.is_mmode
          && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL
          && rvfi_if.is_load_instr
          && support_if.trigger_match_mem[t]
          && !rvfi_if.rvfi_dbg_mode
          |->
          rvfi_if.rvfi_trap.debug
        ) else `uvm_error(info_tag, "The trigger match (load match, machine mode, match when greater or equal) does not send the core into debug mode.\n");

        a_dt_load_trigger_hit_umode_match_when_equal_or_greater: assert property (
          rvfi_if.is_umode
          && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL
          && rvfi_if.is_load_instr
          && support_if.trigger_match_mem[t]
          && !rvfi_if.rvfi_dbg_mode
          |->
          rvfi_if.rvfi_trap.debug
        ) else `uvm_error(info_tag, "The trigger match (load match, user mode, match when greater or equal) does not send the core into debug mode.\n");

        a_dt_load_trigger_hit_mmode_match_when_lesser: assert property (
          rvfi_if.is_mmode
          && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER
          && rvfi_if.is_load_instr
          && support_if.trigger_match_mem[t]
          && !rvfi_if.rvfi_dbg_mode
          |->
          rvfi_if.rvfi_trap.debug
        ) else `uvm_error(info_tag, "The trigger match (load match, machine mode, match when lesser) does not send the core into debug mode.\n");

        a_dt_load_trigger_hit_umode_match_when_lesser: assert property (
          rvfi_if.is_umode
          && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER
          && rvfi_if.is_load_instr
          && support_if.trigger_match_mem[t]
          && !rvfi_if.rvfi_dbg_mode
          |->
          rvfi_if.rvfi_trap.debug
        ) else `uvm_error(info_tag, "The trigger match (load match, user mode, match when lesser) does not send the core into debug mode.\n");

        //Store:
        a_dt_store_trigger_hit_mmode_match_when_equal: assert property (
          rvfi_if.is_mmode
          && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL
          && rvfi_if.is_store_instr
          && support_if.trigger_match_mem[t]
          && !rvfi_if.rvfi_dbg_mode
          |->
          rvfi_if.rvfi_trap.debug
        ) else `uvm_error(info_tag, "The trigger match (store match, machine mode, match when equal) does not send the core into debug mode.\n");

        a_dt_store_trigger_hit_umode_match_when_equal: assert property (
          rvfi_if.is_umode
          && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_EQUAL
          && rvfi_if.is_store_instr
          && support_if.trigger_match_mem[t]
          && !rvfi_if.rvfi_dbg_mode
          |->
          rvfi_if.rvfi_trap.debug
        ) else `uvm_error(info_tag, "The trigger match (store match, user mode, match when equal) does not send the core into debug mode.\n");

        a_dt_store_trigger_hit_mmode_match_when_equal_or_greater: assert property (
          rvfi_if.is_mmode
          && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL
          && rvfi_if.is_store_instr
          && support_if.trigger_match_mem[t]
          && !rvfi_if.rvfi_dbg_mode
          |->
          rvfi_if.rvfi_trap.debug
        ) else `uvm_error(info_tag, "The trigger match (store match, machine mode, match when greater or equal) does not send the core into debug mode.\n");

        a_dt_store_trigger_hit_umode_match_when_equal_or_greater: assert property (
          rvfi_if.is_umode
          && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_GREATER_OR_EQUAL
          && rvfi_if.is_store_instr
          && support_if.trigger_match_mem[t]
          && !rvfi_if.rvfi_dbg_mode
          |->
          rvfi_if.rvfi_trap.debug
        ) else `uvm_error(info_tag, "The trigger match (store match, user mode, match when greater or equal) does not send the core into debug mode.\n");

        a_dt_store_trigger_hit_mmode_match_when_lesser: assert property (
          rvfi_if.is_mmode
          && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER
          && rvfi_if.is_store_instr
          && support_if.trigger_match_mem[t]
          && !rvfi_if.rvfi_dbg_mode
          |->
          rvfi_if.rvfi_trap.debug
        ) else `uvm_error(info_tag, "The trigger match (store match, machine mode, match when lesser) does not send the core into debug mode.\n");

        a_dt_store_trigger_hit_umode_match_when_lesser: assert property (
          rvfi_if.is_umode
          && tdata1_array[t][MSB_MATCH:LSB_MATCH] == MATCH_WHEN_LESSER
          && rvfi_if.is_store_instr
          && support_if.trigger_match_mem[t]
          && !rvfi_if.rvfi_dbg_mode
          |->
          rvfi_if.rvfi_trap.debug
        ) else `uvm_error(info_tag, "The trigger match (store match, user mode, match when lesser) does not send the core into debug mode.\n");

      end
    end


    //2)
    //TODO: krdosvik, fails, need rtl fix.
    /*a_dt_enter_dbg_reason: assert property (
      rvfi_if.rvfi_valid
      && rvfi_if.rvfi_trap.debug
      && rvfi_if.rvfi_trap.debug_cause == TRIGGER_MATCH

      |->
      support_if.is_trigger_match

    ) else `uvm_error(info_tag, "We have entered debug mode due to triggers but not due to any of the listed reasons.\n");*/

    //- Vplan:
    //Change the type to 2/6/15 and write any data to "tdata2", read it back and check that it always gets set.

    //- Assertion verification:
    //1) Change the type to 2/6/15 and write any data to "tdata2", read it back and check that it always gets set.


    //1)
    a_dt_write_tdata2_random_in_dmode_type_2_6_15: assert property (

      (seq_csr_write_dmode(ADDR_TDATA2)
      ##0 (tdata1_pre_state[MSB_TYPE:LSB_TYPE] == 2
      || tdata1_pre_state[MSB_TYPE:LSB_TYPE] == 6
      || tdata1_pre_state[MSB_TYPE:LSB_TYPE] == 15))

      |->
      (is_csrrw && (tdata2_post_state == rvfi_if.rvfi_rs1_rdata))
      || (is_csrrs && (tdata2_post_state == (tdata2_pre_state | rvfi_if.rvfi_rs1_rdata)))
      || (is_csrrc && (tdata2_post_state == (tdata2_pre_state & (~rvfi_if.rvfi_rs1_rdata))))
      || (is_csrrwi && (tdata2_post_state == csri_uimm))
      || (is_csrrsi && (tdata2_post_state == (tdata2_pre_state | csri_uimm)))
      || (is_csrrci && (tdata2_post_state == (tdata2_pre_state & (~csri_uimm))))

    ) else `uvm_error(info_tag, "Random values for tdata2 type 2/6/15 in debug mode, is not accepted.\n");


    for (genvar t = 0; t < CORE_PARAM_DBG_NUM_TRIGGERS; t++) begin

      c_dt_w_csrrw_tdata2_m2_m6_disabled: cover property (
        seq_tdata1_m2_m6_or_disabled(t)
        ##0 is_csrrw
        && rvfi_if.rvfi_insn[31:20] == ADDR_TDATA2
      );

      c_dt_w_csrrs_tdata2_m2_m6_disabled: cover property (
        seq_tdata1_m2_m6_or_disabled(t)
        ##0 is_csrrs
        && rvfi_if.rvfi_insn[31:20] == ADDR_TDATA2
      );

      c_dt_w_csrrc_tdata2_m2_m6_disabled: cover property (
        seq_tdata1_m2_m6_or_disabled(t)
        ##0 is_csrrc
        && rvfi_if.rvfi_insn[31:20] == ADDR_TDATA2
      );

      c_dt_w_csrrwi_tdata2_m2_m6_disabled: cover property (
        seq_tdata1_m2_m6_or_disabled(t)
        ##0 is_csrrwi
        && rvfi_if.rvfi_insn[31:20] == ADDR_TDATA2
      );

      c_dt_w_csrrsi_tdata2_m2_m6_disabled: cover property (
        seq_tdata1_m2_m6_or_disabled(t)
        ##0 is_csrrsi
        && rvfi_if.rvfi_insn[31:20] == ADDR_TDATA2
      );

      c_dt_w_csrrci_tdata2_m2_m6_disabled: cover property (
        seq_tdata1_m2_m6_or_disabled(t)
        ##0 is_csrrci
        && rvfi_if.rvfi_insn[31:20] == ADDR_TDATA2
      );


      //- Vplan:
      //Induce firing of a trigger. Check that the corresponding "hit" field gets set. Do the same for variations of multiple triggers firing at once.
      //Check that the field is WARL 0x0, 0x1.

      //- Assertion verification:
      //1) Induce firing of a trigger. Check that the corresponding "hit" field gets set
      //2) Check that the field is WARL 0x0, 0x1

      //1)
      a_dt_m6_hit_bit: assert property(
        rvfi_if.rvfi_valid
        && !rvfi_if.rvfi_dbg_mode
        && tdata1_array[t][MSB_TYPE:LSB_TYPE] == TTYPE_MCONTROL6
        && support_if.is_trigger_match[t]
        |->
        {tdata1_array[t][M6_HIT1], tdata1_array[t][M6_HIT0]} == 2'b01
      ) else `uvm_error(info_tag, "The hit bits is not set even though there is a m6 trigger match.\n");

    end

    //2) see a_dt_warl_tdata1_m6


  end // if CORE_PARAM_DBG_NUM_TRIGGERS > 0


endmodule : uvmt_cv32e40s_triggers_assert_cov
