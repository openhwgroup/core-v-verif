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

module uvmt_cv32e40s_debug_assert
  import uvm_pkg::*;
  import uvma_rvfi_pkg::*;
  import cv32e40s_pkg::*;
  (
      uvma_rvfi_instr_if rvfi,
      uvma_rvfi_csr_if csr_dcsr,
      uvma_rvfi_csr_if csr_dpc,
      uvma_rvfi_csr_if csr_mepc,
      uvma_rvfi_csr_if csr_mstatus,
      uvma_rvfi_csr_if csr_mtvec,
      //TODO:MT tdatas should not be necessary when trigger logic is ready
      uvma_rvfi_csr_if csr_tdata1,
      uvma_rvfi_csr_if csr_tdata2,
      uvmt_cv32e40s_debug_cov_assert_if cov_assert_if
  );

  // ---------------------------------------------------------------------------
  // Local parameters
  // ---------------------------------------------------------------------------
  localparam WFI_INSTR_MASK       = 32'h ffff_ffff;
  localparam WFI_INSTR_OPCODE     = 32'h 1050_0073;
  localparam EBREAK_INSTR_OPCODE  = 32'h 0010_0073;
  localparam CEBREAK_INSTR_OPCODE = 32'h 0000_9002;
  localparam DRET_INSTR_OPCODE    = 32'h 7B20_0073;
  localparam int MSTATUS_TW_POS   = 21;
  localparam int DCSR_STEP_POS    = 2;
  localparam int DCSR_NMIP_POS    = 3;
  localparam int DCSR_STEPIE_POS  = 11;
  localparam int DCSR_EBREAKM_POS  = 15;
  localparam int DCSR_EBREAKU_POS  = 12;

  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------
  string        info_tag = "CV32E40S_DEBUG_ASSERT";
  logic [31:0]  pc_at_dbg_req; // Capture PC when debug_req_i or ebreak is active
  logic [31:0]  halt_addr;
  logic [31:0]  exception_addr_at_entry;
  logic         exception_addr_at_entry_flag;
  // Locally track which debug cause should be used
  logic [2:0]   debug_cause_pri;
  logic [31:0]  boot_addr;
  logic [31:0]  mtvec_addr;
  logic         is_trigger_match;
  logic         is_rvfi_nmi_handler;

  logic         first_debug_ins_flag;
  logic         first_debug_ins;
  logic         ins_was_dret;
  logic         started_decoding_in_debug;
  logic         ebreak_allowed;
  logic         exception_trigger_hit;
  logic         first_fetch;
  logic         fetch_enable_i_q;

  logic         recorded_req;
  logic [3:0]   req_vs_valid_cnt;
  logic [3:0]   stable_req_vs_valid_cnt;

  logic         prev_was_ebreak_flag;
  logic [31:0]  prev_was_ebreak_pc_wdata;
  logic [31:0]  dpc_rdata_q;
  logic [31:0]  dcsr_rdata_q;

  // ---------------------------------------------------------------------------
  // Clocking blocks
  // ---------------------------------------------------------------------------

  // Single clock, single reset design, use default clocking
  default clocking @(posedge cov_assert_if.clk_i); endclocking
  default disable iff !(cov_assert_if.rst_ni);


  assign cov_assert_if.is_ebreak =
    cov_assert_if.wb_valid
    && (cov_assert_if.wb_stage_instr_rdata_i == EBREAK_INSTR_OPCODE)
    && !cov_assert_if.wb_err
    && (cov_assert_if.wb_mpu_status == MPU_OK);

  assign cov_assert_if.is_cebreak =
    cov_assert_if.wb_valid
    && (cov_assert_if.wb_stage_instr_rdata_i == CEBREAK_INSTR_OPCODE)
    && !cov_assert_if.wb_err
    && (cov_assert_if.wb_mpu_status == MPU_OK);

  assign cov_assert_if.is_mulhsu =
    cov_assert_if.wb_stage_instr_valid_i
    && (cov_assert_if.wb_stage_instr_rdata_i[31:25] == 7'h1)
    && (cov_assert_if.wb_stage_instr_rdata_i[14:12] == 3'b010)
    && (cov_assert_if.wb_stage_instr_rdata_i[6:0]   == 7'h33);

  assign is_trigger_match = (cov_assert_if.trigger_match_in_wb || cov_assert_if.etrigger_in_wb) && cov_assert_if.wb_valid;

  assign mtvec_addr = {csr_mtvec.rvfi_csr_rdata[31:2], 2'b00};

  assign is_rvfi_nmi_handler =
    rvfi.rvfi_valid && (rvfi.rvfi_intr.cause & 11'h 400);
    // Note: 0x400 currently uniquely identifies NMIs, though this may (but is not expected to) change.

    // ---------------------------------------
    // Assertions
    // ---------------------------------------

    // Helper sequence: Go to next WB retirement

    sequence s_conse_next_retire;  // Should only be used in consequent (not antecedent)
        ($fell(cov_assert_if.wb_stage_instr_valid_i) [->1]  // Finish current WB preoccupation
            ##0 cov_assert_if.wb_valid [->1])  // Go to next WB done
        or
        ($fell(cov_assert_if.ex_valid) [->1]  // Finish current EX preoccupation
            ##0 cov_assert_if.wb_valid [->2])  // Go to next two WB done
        or
        (cov_assert_if.wb_valid [->1]  // Go directly to next WB done
            ##0 (cov_assert_if.dcsr_q[8:6] inside {3, 4}))  // Need good reason to forgo $fell(instr_valid)
        ;
    endsequence


    // Check that we enter debug mode when expected. CSR checks are done in other assertions
    /*TODO:MT replace with specifics for each entry cause
    property p_enter_debug;
        $changed(debug_cause_pri) && (debug_cause_pri != 0) && !cov_assert_if.debug_mode_q
        |->
        s_conse_next_retire
        ##0 cov_assert_if.debug_mode_q;
    endproperty
*/

    property p_enter_debug;
        $changed(debug_cause_pri) && (debug_cause_pri != 0) && !rvfi.rvfi_dbg_mode
        |=>
        rvfi.rvfi_valid[->1]
        ##0 first_debug_ins;
    endproperty

    a_enter_debug: assert property(p_enter_debug)
        else `uvm_error(info_tag, $sformatf("Debug mode not entered after exepected cause %d", debug_cause_pri));


    // Check that dpc gets the correct value when debug mode is entered.
    a_debug_mode_pc: assert property(
        $rose(first_debug_ins)
        |->
        rvfi.rvfi_pc_rdata == halt_addr
        ) else `uvm_error(info_tag, $sformatf("Debug mode entered with wrong pc. pc==%08x", rvfi.rvfi_pc_rdata));

    //TODO:MT rewrite to rvfi timing
    a_debug_mode_pc_dpc: assert property(
        $rose(first_debug_ins)
        |->
        (rvfi.rvfi_intr.intr && rvfi.rvfi_intr.interrupt
        ##1
        dpc_rdata_q == pc_at_dbg_req)
        or
        ((rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_HALTREQ || rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_STEP) &&
        prev_was_ebreak_flag &&
        csr_dpc.rvfi_csr_rdata == prev_was_ebreak_pc_wdata)
        or
        (csr_dpc.rvfi_csr_rdata == pc_at_dbg_req)
        ) else `uvm_error(info_tag, $sformatf("Debug mode entered with wrong dpc. dpc==%08x", csr_dpc.rvfi_csr_rdata));

    // Check that dcsr.cause is as expected
    property p_dcsr_cause;
        $rose(first_debug_ins)
        |->
        (rvfi.rvfi_dbg == debug_cause_pri)
        or
        (recorded_req && (rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_HALTREQ));
    endproperty

    a_dcsr_cause: assert property(p_dcsr_cause)
        else `uvm_error(info_tag, "dcsr.cause was not as expected");



    // check that a steble debug_req is actually taken within reasonable time
    a_debug_req_taken: assert property(stable_req_vs_valid_cnt <= 3)
        else `uvm_error(info_tag, "External debug request not taken in reasonable time");


    // Check that debug with cause ebreak is correct
    property p_ebreak_debug_mode;
        $rose(first_debug_ins) && (rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_EBREAK)
        |-> prev_was_ebreak_flag;
    endproperty

    a_ebreak_debug_mode: assert property(p_ebreak_debug_mode)
        else `uvm_error(info_tag,$sformatf("Debug mode with wrong cause after ebreak, case = %d",cov_assert_if.dcsr_q[8:6]));


    // ebreak / c.ebreak without dcsr.ebreak[prv] results in exception at mtvec
    property p_ebreak_mmode_exception;
        rvfi.is_ebreak() &&
        !rvfi.rvfi_dbg_mode &&
        rvfi.is_mmode() &&
        !csr_dcsr.rvfi_csr_rdata[DCSR_EBREAKM_POS]
        |-> rvfi.rvfi_trap.trap && rvfi.rvfi_trap.exception
            or
            rvfi.rvfi_trap.trap && rvfi.rvfi_trap.debug && !(rvfi.rvfi_trap.debug_cause == cv32e40s_pkg::DBG_CAUSE_EBREAK);
    endproperty

    property p_ebreak_umode_exception;
        rvfi.is_ebreak() &&
        !rvfi.rvfi_dbg_mode &&
        rvfi.is_umode() &&
        !csr_dcsr.rvfi_csr_rdata[DCSR_EBREAKU_POS]
        |-> rvfi.rvfi_trap.trap && rvfi.rvfi_trap.exception
            or
            rvfi.rvfi_trap.trap && rvfi.rvfi_trap.debug && !(rvfi.rvfi_trap.debug_cause == cv32e40s_pkg::DBG_CAUSE_EBREAK);
    endproperty

    a_ebreak_mmode_exception: assert property(p_ebreak_mmode_exception)
        else `uvm_error(info_tag, $sformatf("Exception not entered correctly after ebreak with dcsr.ebreakm=0 in mmode"));

    a_ebreak_umode_exception: assert property(p_ebreak_umode_exception)
        else `uvm_error(info_tag, $sformatf("Exception not entered correctly after ebreak with dcsr.ebreaku=0 in umode"));


    // ebreak and cebreak during debug mode results in relaunch
    property p_ebreak_during_debug_mode;
        rvfi.is_ebreak() &&
        rvfi.rvfi_trap.debug_cause == cv32e40s_pkg::DBG_CAUSE_EBREAK && //The ebreak is actually taken
        rvfi.rvfi_dbg_mode
        |=>
        rvfi.rvfi_valid[->1]
        ##0 rvfi.rvfi_dbg_mode &&
        ((csr_dcsr.rvfi_csr_rdata | (1 << DCSR_NMIP_POS)) == (dcsr_rdata_q | (1 << DCSR_NMIP_POS))) &&
        (csr_dpc.rvfi_csr_rdata == dpc_rdata_q) &&
        (rvfi.rvfi_pc_rdata == halt_addr);
    endproperty

    a_ebreak_during_debug_mode: assert property(p_ebreak_during_debug_mode)
        else `uvm_error(info_tag,$sformatf("Debug mode not restarted after ebreak"));

    cov_cebreak_dbg : cover property(
        rvfi.is_ebreak_compr() && rvfi.rvfi_dbg_mode
    );
    cov_ebreak_dbg : cover property(
        rvfi.is_ebreak_noncompr() && rvfi.rvfi_dbg_mode
    );

    // Trigger match results in debug mode
    //TODO:MT redo in rvfi timing with new triger logic
   /* property p_trigger_match;
        is_trigger_match ##0 cov_assert_if.tdata1[2] ##0 !cov_assert_if.debug_mode_q
        |->
        s_conse_next_retire
        ##0 cov_assert_if.debug_mode_q && (cov_assert_if.dcsr_q[8:6] === cv32e40s_pkg::DBG_CAUSE_TRIGGER)
            && (cov_assert_if.dpc_q == tdata2_at_entry) && (cov_assert_if.wb_stage_pc == halt_addr_at_entry);
    endproperty

    a_trigger_match: assert property(p_trigger_match)
        else `uvm_error(info_tag,
            $sformatf("Debug mode not correctly entered after trigger match dpc=%08x, tdata2=%08x",
                cov_assert_if.dpc_q, tdata2_at_entry));
    */
    // Address match without trigger enabled should NOT result in debug mode

    property p_trigger_match_disabled;
        $rose(cov_assert_if.addr_match) && !cov_assert_if.debug_mode_q |-> ##[1:6] !cov_assert_if.debug_mode_q;
    endproperty

    a_trigger_match_disabled: assert property(p_trigger_match_disabled)
        else `uvm_error(info_tag, "Trigger match with tdata[2]==0 resulted in debug mode");


    // Exception in debug mode results in pc->dm_exception_addr_i

    property p_debug_mode_exception;
        $rose(cov_assert_if.illegal_insn_i) && cov_assert_if.debug_mode_q
        |=>
        s_conse_next_retire
        ##0 cov_assert_if.debug_mode_q && (cov_assert_if.wb_stage_pc == exception_addr_at_entry);
    endproperty

    a_debug_mode_exception : assert property(p_debug_mode_exception)
        else `uvm_error(info_tag,
            $sformatf("Exception in debug mode not handled incorrectly. dm=%d, pc=%08x",
                cov_assert_if.debug_mode_q, cov_assert_if.wb_stage_pc));


    // ECALL in debug mode results in pc->dm_exception_addr_i
    property p_debug_mode_ecall;
        $rose(cov_assert_if.sys_ecall_insn_i && cov_assert_if.sys_en_i) && cov_assert_if.debug_mode_q
        |->
        s_conse_next_retire
        ##0 cov_assert_if.debug_mode_q && (cov_assert_if.wb_stage_pc == exception_addr_at_entry);
    endproperty

    a_debug_mode_ecall : assert property(p_debug_mode_ecall)
        else `uvm_error(info_tag,
            $sformatf("ECALL in debug mode not handled incorrectly. dm=%d, pc=%08x",
                cov_assert_if.debug_mode_q, cov_assert_if.wb_stage_pc));

    // IRQ in debug mode are masked
    property p_irq_in_debug;
        cov_assert_if.debug_mode_q |-> !cov_assert_if.irq_ack_o;
    endproperty

    a_irq_in_debug : assert property(p_irq_in_debug)
        else
            `uvm_error(info_tag, $sformatf("IRQ not ignored while in debug mode"));


    // WFI in debug mode does not sleep

    property p_wfi_in_debug;
        cov_assert_if.debug_mode_q && $rose(cov_assert_if.is_wfi) |-> ##6 !cov_assert_if.core_sleep_o;
        // TODO:ropeders should/could the consequent be more specific?
    endproperty

    a_wfi_in_debug : assert property(p_wfi_in_debug)
        else `uvm_error(info_tag, $sformatf("WFI in debug mode cause core_sleep_o=1"));


    // Debug request while sleeping makes core wake up and enter debug mode with cause=haltreq

    property p_sleep_debug_req;
        (cov_assert_if.ctrl_fsm_cs == SLEEP) && cov_assert_if.debug_req_i
        |=>
        !cov_assert_if.core_sleep_o
        ##0 s_conse_next_retire
        ##0 cov_assert_if.debug_mode_q && (cov_assert_if.dcsr_q[8:6] == cv32e40s_pkg::DBG_CAUSE_HALTREQ);
    endproperty

    a_sleep_debug_req : assert property(p_sleep_debug_req)
        else `uvm_error(info_tag,
            $sformatf("Did not exit sleep(== %d) after debug_req_i. Debug_mode = %d cause = %d",
                cov_assert_if.core_sleep_o, cov_assert_if.debug_mode_q, cov_assert_if.dcsr_q[8:6]));


    // Accessing debug regs in m-mode is illegal

    property p_debug_regs_mmode;
        int tmp;
        cov_assert_if.ex_stage_csr_en && cov_assert_if.ex_valid && !cov_assert_if.debug_mode_q
        && cov_assert_if.ex_stage_instr_rdata_i[31:20] inside {'h7B0, 'h7B1, 'h7B2, 'h7B3}
        ##0 (1, tmp = cov_assert_if.ex_stage_pc)
        |=>
        (cov_assert_if.wb_stage_pc == tmp) [->1]
        ##0 cov_assert_if.illegal_insn_i;
    endproperty

    a_debug_regs_mmode : assert property(p_debug_regs_mmode)
        else
            `uvm_error(info_tag, "Accessing debug regs in M-mode did not result in illegal instruction");


    // Exception while single step -> PC is set to exception handler before debug
    //TODO:MT I think this is covered in pc_dpc, remove if we become satisfied with that/those assert(s)
    property p_single_step_exception;
        !cov_assert_if.debug_mode_q && cov_assert_if.dcsr_q[2]
        && cov_assert_if.illegal_insn_i && cov_assert_if.wb_valid && !is_trigger_match
        |-> ##[1:20] cov_assert_if.debug_mode_q && (cov_assert_if.dpc_q == mtvec_addr);
    endproperty

    a_single_step_exception : assert property(p_single_step_exception)
        else `uvm_error(info_tag, "PC not set to exception handler after single step with exception");


    // Trigger during single step
    //TODO:MT rewrite to rvfi timing
    //TODO:MT covered in cause + pc_dpc?
    property p_single_step_trigger;
        !cov_assert_if.debug_mode_q && cov_assert_if.dcsr_q[2]
        && cov_assert_if.addr_match && cov_assert_if.wb_valid && cov_assert_if.tdata1[2]
        |-> ##[1:20] cov_assert_if.debug_mode_q && (cov_assert_if.dcsr_q[8:6] == cv32e40s_pkg::DBG_CAUSE_TRIGGER)
        && (cov_assert_if.dpc_q == pc_at_dbg_req);
    endproperty

    a_single_step_trigger : assert property (p_single_step_trigger)
        else `uvm_error(info_tag,
        $sformatf("Single step and trigger error: dpc = %08x, cause = %d",cov_assert_if.dpc_q, cov_assert_if.dcsr_q[8:6]));


    // Single step WFI must not result in sleeping

    property p_single_step_wfi;
        !cov_assert_if.debug_mode_q && cov_assert_if.dcsr_q[2] && cov_assert_if.is_wfi
        |->
        s_conse_next_retire
        ##0 cov_assert_if.debug_mode_q && !cov_assert_if.core_sleep_o;
    endproperty

    a_single_step_wfi : assert property(p_single_step_wfi)
        else `uvm_error(info_tag, "Debug mode not entered after single step WFI or core went sleeping");


    // Executing with single step with no irq results in debug mode

    property p_single_step;
        !cov_assert_if.debug_mode_q && cov_assert_if.dcsr_q[2] && !cov_assert_if.dcsr_q[11]
        && cov_assert_if.wb_stage_instr_valid_i
        |=>
        s_conse_next_retire
        ##0 cov_assert_if.debug_mode_q;
    endproperty

    a_single_step: assert property(p_single_step)
        else `uvm_error(info_tag, "Debug mode not entered for single step");


    // dret in M-mode will cause illegal instruction
    // If pending debug req, illegal insn will not assert until resume
    property p_mmode_dret;
        !cov_assert_if.debug_mode_q && cov_assert_if.is_dret &&
        !(cov_assert_if.pending_sync_debug || cov_assert_if.pending_async_debug)
        |-> cov_assert_if.illegal_insn_i;
    endproperty

    a_mmode_dret : assert property(p_mmode_dret)
        else `uvm_error(info_tag, "Executing dret in M-mode did not result in illegal instruction");


    // dret in D-mode will restore pc (if no re-entry or interrupt intervenes)

    property p_dmode_dret_pc;
        int dpc;
        (rvfi.rvfi_valid && rvfi.rvfi_dbg_mode && rvfi.rvfi_insn == DRET_INSTR_OPCODE,
         dpc = csr_dpc.rvfi_csr_rdata)
        ##1
        rvfi.rvfi_valid[->1]
        ##0 (!rvfi.rvfi_intr && !rvfi.rvfi_dbg_mode)
        |->
        rvfi.rvfi_pc_rdata == dpc;
    endproperty

    a_dmode_dret_pc : assert property(p_dmode_dret_pc)
        else `uvm_error(info_tag, "Dret did not cause correct return from debug mode");


    // dret in D-mode will place dpc in mepc if re-entry is interrupted (excluding nmi)

    property p_dmode_dret_pc_int;
        int dpc;
        (rvfi.rvfi_valid && rvfi.rvfi_dbg_mode && rvfi.rvfi_insn == DRET_INSTR_OPCODE,
         dpc = csr_dpc.rvfi_csr_rdata)
        ##1
        rvfi.rvfi_valid[->1]
        ##0 (rvfi.rvfi_intr && !rvfi.rvfi_dbg_mode && !is_rvfi_nmi_handler)
        |->
        csr_mepc.rvfi_csr_rdata == dpc;
    endproperty

    a_dmode_dret_pc_int : assert property(p_dmode_dret_pc_int)
        else `uvm_error(info_tag, "Dret did not save dpc to mepc when return from debug mode was interrupted");


    // dret in D-mode can be followed by nmi where "mepc=dpc"

    property p_dmode_dret_pc_nmi_eq;
        int dpc;
        (rvfi.rvfi_valid && rvfi.rvfi_dbg_mode && rvfi.rvfi_insn == DRET_INSTR_OPCODE,
         dpc = csr_dpc.rvfi_csr_rdata)
        ##1
        rvfi.rvfi_valid[->1]
        ##0 (!rvfi.rvfi_dbg_mode && is_rvfi_nmi_handler)
        ##0 (csr_mepc.rvfi_csr_rdata == dpc);
    endproperty

    cov_dmode_dret_pc_nmi_eq : cover property(p_dmode_dret_pc_nmi_eq);


    // dret in D-mode can be followed by nmi where "mepc!=dpc"

    property p_dmode_dret_pc_nmi_neq;
        int dpc;
        (rvfi.rvfi_valid && rvfi.rvfi_dbg_mode && rvfi.rvfi_insn == DRET_INSTR_OPCODE,
         dpc = csr_dpc.rvfi_csr_rdata)
        ##1
        rvfi.rvfi_valid[->1]
        ##0 (!rvfi.rvfi_dbg_mode && is_rvfi_nmi_handler)
        ##0 (csr_mepc.rvfi_csr_rdata != dpc);
    endproperty

    cov_dmode_dret_pc_nmi_neq : cover property(p_dmode_dret_pc_nmi_neq);


    // dret in D-mode will exit D-mode

    property p_dmode_dret_exit;
        cov_assert_if.debug_mode_q && cov_assert_if.is_dret
        |=>
        !cov_assert_if.debug_mode_q;
        // TODO:ropeders also assert, stays in mmode until wb_valid if no debug_request
    endproperty

    a_dmode_dret_exit : assert property(p_dmode_dret_exit)
        else `uvm_error(info_tag, "Dret did not exit debug mode");

    // TODO:ropeders what is missing from these dret assertions?


    // Check that trigger regs cannot be written from M-mode
    // TSEL, and TDATA3 are tied to zero, hence no register to check
    property p_mmode_tdata1_write;
        !cov_assert_if.debug_mode_q && cov_assert_if.csr_access && cov_assert_if.csr_op == 'h1  // TODO:ropeders also "set" op?
        && cov_assert_if.wb_stage_instr_rdata_i[31:20] == 'h7A1
        |->
        ##0 $stable(cov_assert_if.tdata1) [*4];
    endproperty

    a_mmode_tdata1_write : assert property(p_mmode_tdata1_write)
        else `uvm_error(info_tag, "Writing tdata1 from M-mode not allowed to change register value!");

    property p_mmode_tdata2_write;
        !cov_assert_if.debug_mode_q && cov_assert_if.csr_access && cov_assert_if.csr_op == 'h1
        && cov_assert_if.wb_stage_instr_rdata_i[31:20] == 'h7A2
        |->
        ##0 $stable(cov_assert_if.tdata2) [*4];
    endproperty

    a_mmode_tdata2_write : assert property(p_mmode_tdata2_write)
        else `uvm_error(info_tag, "Writing tdata2 from M-mode not allowed to change register value!");


    // Check that mcycle works as expected when not sleeping
    // Counter can be written an arbitrary value, check that
    // it changed only when not being written to
    // Counter should not increment when in debug mode with dcsr.stopcount set

    property p_mcycle_count;
        !cov_assert_if.mcountinhibit_q[0] && !cov_assert_if.core_sleep_o && !((cov_assert_if.debug_mode_q) && cov_assert_if.dcsr_q[10])
        && !(cov_assert_if.csr_we_int && (cov_assert_if.csr_addr ==12'hB00 || cov_assert_if.csr_addr == 12'hB80))
        |=> $changed(cov_assert_if.mcycle);
    endproperty

    a_mcycle_count : assert property(p_mcycle_count)
        else `uvm_error(info_tag, "Mcycle not counting when mcountinhibit[0] is cleared!");


    // Check that minstret works as expected when not sleeping
    // Check only when not written to
    // Counter should not increment when in debug mode with dcsr.stopcount set

    property p_minstret_count;
        !cov_assert_if.mcountinhibit_q[2] && cov_assert_if.inst_ret && !cov_assert_if.core_sleep_o && !((cov_assert_if.debug_mode_q) && cov_assert_if.dcsr_q[10])
        && !(cov_assert_if.csr_we_int && (cov_assert_if.csr_addr == 12'hB02 || cov_assert_if.csr_addr == 12'hB82))
        |=> (cov_assert_if.minstret == ($past(cov_assert_if.minstret)+1));
    endproperty

    a_minstret_count : assert property(p_minstret_count)
        else
            `uvm_error(info_tag, "Minstret not counting when mcountinhibit[2] is cleared!");

    // Check debug_req_i and irq on same cycle.
    // Should result in debug mode with regular pc in dpc, not pc from interrupt handler.
    // PC is checked in another assertion
    /* TODO:MT Commented out temporarily to keep sim working after removal of debug_req_q
    //TODO:MT should this be a cover instead? checking in cause + pc_dpc
    property p_debug_req_and_irq;
        ((cov_assert_if.debug_req_i || cov_assert_if.debug_req_q) && !cov_assert_if.debug_mode_q)
        && (cov_assert_if.pending_enabled_irq != 0)
        |->
        s_conse_next_retire
        ##0 cov_assert_if.debug_mode_q;
        // TODO:ropeders should dpc be checked here?
    endproperty

    a_debug_req_and_irq : assert property(p_debug_req_and_irq)
        else `uvm_error(info_tag, "Debug mode not entered after debug_req_i and irq on same cycle");
    */

    // debug_req at reset should result in debug mode and no instructions executed

    property p_debug_at_reset;
        (cov_assert_if.ctrl_fsm_cs == cv32e40s_pkg::RESET) && cov_assert_if.debug_req_i
        |->
        s_conse_next_retire
        ##0 cov_assert_if.debug_mode_q && (cov_assert_if.dpc_q == boot_addr);
    endproperty

    a_debug_at_reset : assert property(p_debug_at_reset)
        else `uvm_error(info_tag, "Debug mode not entered correctly at reset!");


    // Debug vs reset

    a_debug_state_onehot : assert property (
      $onehot({cov_assert_if.debug_havereset, cov_assert_if.debug_running, cov_assert_if.debug_halted})
      ) else `uvm_error(info_tag, "Should have exactly 1 of havereset/running/halted");

    cov_havereset_to_running : cover property (
      (cov_assert_if.debug_havereset  == 1)
      && (cov_assert_if.debug_running == 0)
      && (cov_assert_if.debug_halted  == 0)
      #=#
      (cov_assert_if.debug_havereset  == 0)
      && (cov_assert_if.debug_running == 1)
      && (cov_assert_if.debug_halted  == 0)
      );

    cov_havereset_to_halted : cover property (
      (cov_assert_if.debug_havereset  == 1)
      && (cov_assert_if.debug_running == 0)
      && (cov_assert_if.debug_halted  == 0)
      #=#
      (cov_assert_if.debug_havereset  == 0)
      && (cov_assert_if.debug_running == 0)
      && (cov_assert_if.debug_halted  == 1)
      );

    // step vs nmi
    // check that stepie disables nmi
    property p_stepie_irq_dis;
        rvfi.is_dret() && csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS] && !csr_dcsr.rvfi_csr_rdata[DCSR_STEPIE_POS]
        |=>
        rvfi.rvfi_valid[->1]
        ##0 !(rvfi.rvfi_intr.intr && rvfi.rvfi_intr.interrupt);
    endproperty

    a_stepie_irq_dis : assert property(p_stepie_irq_dis)
        else `uvm_error(info_tag, "Single stepping should ignore all interrupts if stepie is set");

    cov_step_stepie_nmi : cover property (
        rvfi.is_dret()
        && csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS]
        && !csr_dcsr.rvfi_csr_rdata[DCSR_STEPIE_POS]
        && csr_dcsr.rvfi_csr_rdata[DCSR_NMIP_POS]
    );

    // step trap handler entry, no retire

    // if the next instruction after a single step dret is in debug mode,
    // a trap entry has to be the cause.
    property p_step_trap_handler_entry;
        (rvfi.is_dret() &&
        csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS] &&
        csr_dcsr.rvfi_csr_rdata[DCSR_STEPIE_POS])
        ##1 rvfi.rvfi_valid[->1]
        ##0 rvfi.rvfi_dbg_mode && (rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_STEP)
        |->
        rvfi.rvfi_intr.intr;
    endproperty

    a_step_trap_handler_entry : assert property(p_step_trap_handler_entry)
        else `uvm_error(info_tag, "single stepping remained in debug mode illegally");

    property p_step_no_trap;
        rvfi.is_dret() && csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS] && csr_dcsr.rvfi_csr_rdata[DCSR_STEPIE_POS]
        ##1 rvfi.rvfi_valid[->1]
        ##0 !rvfi.rvfi_dbg_mode
        |->
        !rvfi.rvfi_intr.intr;
    endproperty

    a_step_no_trap : assert property(p_step_no_trap)
        else `uvm_error(info_tag, "single stepping should not retire a trap handler entry");


    // Check that we cover the case where a debug_req_i
    // comes while flushing due to an illegal insn, causing
    // dpc to be set to the exception handler entry addr

    // TODO We have excluded the case where an nmi is taken in the second stage of the antecedent.
    // TODO:MT covered with dcsr_cause + pc_dpc asserts?
    //      Make sure this is covered in a debug vs nmi assertion when it is written
    sequence s_illegal_insn_debug_req_ante;  // Antecedent
        cov_assert_if.wb_illegal && cov_assert_if.wb_valid && !cov_assert_if.debug_mode_q
        ##1 cov_assert_if.debug_req_i && !cov_assert_if.debug_mode_q && !cov_assert_if.pending_nmi;
    endsequence

    sequence s_illegal_insn_debug_req_conse;  // Consequent
        s_conse_next_retire
        ##0 cov_assert_if.debug_mode_q && (cov_assert_if.dpc_q == mtvec_addr);
    endsequence

    // Need to confirm that the assertion can be reached for non-trivial cases
    cov_illegal_insn_debug_req_nonzero : cover property(
        s_illegal_insn_debug_req_ante |-> s_illegal_insn_debug_req_conse ##0 (cov_assert_if.dpc_q != 0));

    a_illegal_insn_debug_req : assert property(s_illegal_insn_debug_req_ante |-> s_illegal_insn_debug_req_conse)
        else `uvm_error(info_tag, "Debug mode not entered correctly while handling illegal instruction!");


    // -------------------------------------------
    // Capture internal states for use in checking
    // -------------------------------------------

    always @(posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if(!cov_assert_if.rst_ni) begin
            pc_at_dbg_req <= 32'h0;
        end else begin
            //NMI has highest priority for dpc
            if(rvfi.is_nmi() && rvfi.rvfi_dbg_mode) begin
                if (csr_mtvec.rvfi_csr_rdata[1:0] == 3) begin //CLIC
                    //TODO:MT placeholder for predicting clic address
                    pc_at_dbg_req <= csr_dpc.rvfi_csr_wdata;
                end else if (csr_mtvec.rvfi_csr_rdata[1:0] == 1) begin // vectored CLINT
                    pc_at_dbg_req <= mtvec_addr+'h3C;
                end else begin //unvectored CLINT
                    pc_at_dbg_req <= mtvec_addr;
                end
            // if the debug cause is synchronous debug entry IRQ is "taken" first4
            end else if (   rvfi.rvfi_valid &&
                            rvfi.rvfi_dbg_mode &&
                            rvfi.rvfi_intr.intr) begin
                if (csr_mtvec.rvfi_csr_rdata[1:0] == 3) begin //CLIC
                    //TODO:MT placeholder for predicting clic address
                    pc_at_dbg_req <= csr_dpc.rvfi_csr_wdata;
                end else if (csr_mtvec.rvfi_csr_rdata[1:0] == 1) begin //vectored CLINT
                    pc_at_dbg_req <= mtvec_addr + (rvfi.rvfi_intr.cause << 2);
                end else begin //unvectored CLINT
                    pc_at_dbg_req <= mtvec_addr;
                end
            //TODO: placeholder, works for 1 available trigger. Fix when trigger support logic is in place
            // Exception with exception trigger active
            end else if (rvfi.rvfi_valid && exception_trigger_hit) begin
                pc_at_dbg_req <= rvfi.rvfi_pc_wdata;

            end else if (rvfi.is_ebreak() || rvfi.is_dbg_trg()) begin
                pc_at_dbg_req <= rvfi.rvfi_pc_rdata;

            end else if (first_fetch) begin
                pc_at_dbg_req <= {cov_assert_if.boot_addr_i[31:2], 2'b00};

            end else if (rvfi.rvfi_valid) begin
                pc_at_dbg_req <= rvfi.rvfi_pc_wdata;
            end
        end
    end
    // remembering pc_wdata from an ecall, to deal with a req taking priority for debug entry
    always @(posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if(!cov_assert_if.rst_ni) begin
            prev_was_ebreak_flag <= 0;
            prev_was_ebreak_pc_wdata <= 32'h0;
        end else begin
            if(rvfi.is_ebreak()) begin
                prev_was_ebreak_flag <= 1;
                prev_was_ebreak_pc_wdata <= rvfi.rvfi_pc_wdata;
            end else if (rvfi.rvfi_valid) begin
                prev_was_ebreak_flag <= 0;
                prev_was_ebreak_pc_wdata <= 32'h0;
            end
        end
    end

    always @(posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if(!cov_assert_if.rst_ni) begin
            dpc_rdata_q <= 32'h0;
            dcsr_rdata_q <= 32'h0;
        end else if(rvfi.rvfi_valid) begin
            dpc_rdata_q <= csr_dpc.rvfi_csr_rdata;
            dcsr_rdata_q <= csr_dcsr.rvfi_csr_rdata;
        end
    end

/*
    always @(posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if(!cov_assert_if.rst_ni) begin
            pc_at_dbg_req <= 32'h0;
            pc_at_ebreak <= 32'h0;
        end else begin
            // Capture debug pc
            if (first_fetch) begin
                pc_at_dbg_req <= {cov_assert_if.boot_addr_i[31:2], 2'b00};
            end
            if (rvfi.rvfi_valid) begin
                pc_at_dbg_req <= rvfi.rvfi_pc_wdata;
                if ((debug_cause_pri == 2) && !started_decoding_in_debug) begin  // trigger
                    pc_at_dbg_req <= rvfi.rvfi_pc_rdata;
                end
                if ((debug_cause_pri == 1) && !started_decoding_in_debug) begin  // ebreak
                    pc_at_dbg_req <= rvfi.rvfi_pc_rdata;
                end
            end
            if (cov_assert_if.addr_match && !cov_assert_if.tdata1[18] && cov_assert_if.wb_valid) begin  // trigger
                pc_at_dbg_req <= cov_assert_if.wb_stage_pc;
            end
            if (cov_assert_if.irq_ack_o) begin  // interrupt
                if (cov_assert_if.mtvec[1:0] == 0) begin
                    pc_at_dbg_req <= mtvec_addr;
                end else if (cov_assert_if.mtvec[1:0] == 1) begin
                    pc_at_dbg_req <= mtvec_addr + (cov_assert_if.irq_id_o << 2);
                end
            end
            if(cov_assert_if.pending_nmi && cov_assert_if.nmi_allowed && (cov_assert_if.ctrl_fsm_cs == cv32e40s_pkg::FUNCTIONAL))
            begin
                //TODO:ropeders shouldn't "nmi_allowed" be trustable without "ctrl_fsm_cs"?
                //TODO:ropeders shouldn't "dcsr.nmip" be usable as a "dpc" pedictor?
                //TODO:ropeders shouldn't there be an assert for "dpc" not only on first instr in dmode?
              pc_at_dbg_req <= mtvec_addr + 'h3C; // mtvec_addr + 'h3c = nmi_addr
            end
            if(cov_assert_if.debug_mode_q && started_decoding_in_debug) begin
                pc_at_dbg_req <= pc_at_dbg_req;
            end

            // Capture pc at ebreak
            if(cov_assert_if.is_ebreak || cov_assert_if.is_cebreak ) begin
                pc_at_ebreak <= cov_assert_if.wb_stage_pc;
            end
       end
    end
*/


  // Capture start values
  always@ (posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
    if(!cov_assert_if.rst_ni) begin
          halt_addr <= 0;
          boot_addr <= 0;
    end else begin
        if(first_fetch) begin
            halt_addr <= {cov_assert_if.dm_halt_addr_i[31:2], 2'b00};
            boot_addr <= {cov_assert_if.boot_addr_i[31:2], 2'b00};
        end
    end
  end


  always@ (posedge cov_assert_if.clk_i)  begin
      if ((cov_assert_if.illegal_insn_i || (cov_assert_if.sys_ecall_insn_i && cov_assert_if.sys_en_i))
          && cov_assert_if.pc_set && cov_assert_if.debug_mode_q && cov_assert_if.wb_valid)
      begin
          exception_addr_at_entry = {cov_assert_if.dm_exception_addr_i[31:2], 2'b00};
      end
  end

    assign cov_assert_if.addr_match   = (cov_assert_if.wb_stage_pc == cov_assert_if.tdata2);
    assign cov_assert_if.dpc_will_hit = (cov_assert_if.dpc_n == cov_assert_if.tdata2);
    assign cov_assert_if.pending_enabled_irq = |(cov_assert_if.irq_i & cov_assert_if.mie_q);
    assign cov_assert_if.is_wfi =
        cov_assert_if.wb_valid
        && ((cov_assert_if.wb_stage_instr_rdata_i & WFI_INSTR_MASK) == WFI_INSTR_OPCODE)
        && ((rvfi.rvfi_mode == UVMA_RVFI_M_MODE) || (csr_mstatus.rvfi_csr_rdata[MSTATUS_TW_POS] == 1)) //not legal if in user mode with tw == 0
        && !cov_assert_if.wb_err
        && (cov_assert_if.wb_mpu_status == MPU_OK);
    assign cov_assert_if.is_dret =
        cov_assert_if.wb_valid
        && (cov_assert_if.wb_stage_instr_rdata_i == DRET_INSTR_OPCODE)
        && !cov_assert_if.wb_err
        && (cov_assert_if.wb_mpu_status == MPU_OK);

    // Track which debug cause should be expected
    // cause REQ is treated separately, as it's timing is vaguely defined.
    always@ (posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if( !cov_assert_if.rst_ni) begin
            debug_cause_pri <= 3'b000;
        end else begin  //TODO:MT placeholder for new trigger support logic, this only works with 1 trigger.
            if (rvfi.is_dbg_trg() || exception_trigger_hit) begin
                debug_cause_pri <= cv32e40s_pkg::DBG_CAUSE_TRIGGER;
            end else if(rvfi.is_ebreak() && ebreak_allowed && rvfi.is_instr_bus_valid()) begin
                debug_cause_pri <= cv32e40s_pkg::DBG_CAUSE_EBREAK;
            end else if(rvfi.rvfi_valid && csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS]) begin  // "step"
                debug_cause_pri <= cv32e40s_pkg::DBG_CAUSE_STEP;
            end else if(rvfi.is_dret() && !csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS]) begin
                debug_cause_pri <= 3'b000;  // (not a cause)
            end
        end
    end

    ////TODO:MT placeholder for new trigger support logic, this only works with 1 trigger.
    assign exception_trigger_hit =  (rvfi.rvfi_valid && rvfi.rvfi_trap.exception && csr_tdata1.rvfi_csr_rdata[31:28] == 5) &&
                                    (csr_tdata2.rvfi_csr_rdata[rvfi.rvfi_trap.exception_cause] == 1) &&
                                    ((rvfi.is_mmode() && csr_tdata1.rvfi_csr_rdata[9]) ||
                                    (rvfi.is_umode() && csr_tdata1.rvfi_csr_rdata[6]));
    assign ebreak_allowed = (rvfi.is_mmode() && csr_dcsr.rvfi_csr_rdata[DCSR_EBREAKM_POS]) || (rvfi.is_umode() && csr_dcsr.rvfi_csr_rdata[DCSR_EBREAKU_POS]);

    // Detect first instruction of debug code
    assign first_debug_ins = rvfi.rvfi_valid && rvfi.rvfi_dbg_mode && !first_debug_ins_flag;

    always@ (posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if( !cov_assert_if.rst_ni) begin
            first_debug_ins_flag <= 0;
            ins_was_dret <= 0;
        end else begin
            if(rvfi.rvfi_valid) begin
                if(rvfi.rvfi_dbg_mode) begin
                    first_debug_ins_flag <= 1;
                end else begin
                    first_debug_ins_flag <= 0;
                end
                if(rvfi.is_dret() && !rvfi.rvfi_trap.trap) begin
                    ins_was_dret <= 1;
                end
            end
            if(ins_was_dret) begin
                first_debug_ins_flag <= 0;
                ins_was_dret <= 0;
            end
        end
    end

    //detect core startup
    assign first_fetch = cov_assert_if.fetch_enable_i && !fetch_enable_i_q;

    always@ (posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if( !cov_assert_if.rst_ni) begin
            fetch_enable_i_q <= 0;
        end else if (cov_assert_if.fetch_enable_i) begin
            fetch_enable_i_q <= 1;
        end
    end

    //record a debug_req long enough that it could be taken
    always@ (posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if( !cov_assert_if.rst_ni) begin
            recorded_req <= 0;
            req_vs_valid_cnt <= 4'h0;
        end else begin
            if(rvfi.rvfi_valid) begin
                if(cov_assert_if.debug_req_i) begin
                    recorded_req <= 1;
                    req_vs_valid_cnt <= 4'h2;
                end else if (req_vs_valid_cnt > 0) begin
                    req_vs_valid_cnt <= req_vs_valid_cnt - 1;
                end else begin
                    recorded_req <= 0;
                end
            end else if (cov_assert_if.debug_req_i) begin
                    recorded_req <= 1;
                    req_vs_valid_cnt <= 4'h3;
            end
        end
    end

    // count the number of rvalids while debug_req is stable
    always@ (posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if( !cov_assert_if.rst_ni) begin
            stable_req_vs_valid_cnt <= 4'h0;
        end else begin
            if(!cov_assert_if.debug_req_i || (rvfi.rvfi_valid && rvfi.rvfi_dbg_mode)) begin
                stable_req_vs_valid_cnt <= 4'h0;
            end else if (rvfi.rvfi_valid) begin
                stable_req_vs_valid_cnt <= stable_req_vs_valid_cnt + 1;
            end
        end
    end

endmodule : uvmt_cv32e40s_debug_assert
