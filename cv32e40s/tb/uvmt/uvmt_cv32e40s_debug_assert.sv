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
  import uvmt_cv32e40s_base_test_pkg::*;
  (
      uvma_rvfi_instr_if_t rvfi,
      uvma_rvfi_csr_if_t csr_dcsr,
      uvma_rvfi_csr_if_t csr_dpc,
      uvma_rvfi_csr_if_t csr_dscratch0,
      uvma_rvfi_csr_if_t csr_dscratch1,
      uvma_rvfi_csr_if_t csr_mcause,
      uvma_rvfi_csr_if_t csr_mepc,
      uvma_rvfi_csr_if_t csr_mstatus,
      uvma_rvfi_csr_if_t csr_mtvec,
      //TODO:MT tdatas should not be necessary when trigger logic is ready
      uvma_rvfi_csr_if_t csr_tdata1,
      uvma_rvfi_csr_if_t csr_tdata2,
      uvma_obi_memory_if_t instr_obi,
      uvma_obi_memory_if_t data_obi,
      uvmt_cv32e40s_debug_cov_assert_if_t cov_assert_if,
      uvmt_cv32e40s_support_logic_module_o_if_t.slave_mp support_if
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
  localparam int MCAUSE_MINHV_POS = 30;
  localparam int DCSR_STEP_POS    = 2;
  localparam int DCSR_NMIP_POS    = 3;
  localparam int DCSR_STEPIE_POS  = 11;
  localparam int DCSR_EBREAKM_POS = 15;
  localparam int DCSR_EBREAKU_POS = 12;

  localparam CSR_ADDR_DCSR        = 12'h7B0;
  localparam CSR_ADDR_DPC         = 12'h7B1;
  localparam CSR_ADDR_DSCRATCH0   = 12'h7B2;
  localparam CSR_ADDR_DSCRATCH1   = 12'h7B3;
  localparam CSR_ADDR_MCAUSE      = 12'h342;

  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------
  string        info_tag = "CV32E40S_DEBUG_ASSERT";
  logic [31:0]  pc_at_dbg_req; // Capture PC when debug_req_i or ebreak is active
  logic [31:0]  dpc_dbg_ebreak;
  logic [31:0]  dpc_dbg_trg;
  logic [31:0]  dpc_dbg_step;
  logic [31:0]  dpc_dbg_step_notrap;
  logic [31:0]  dpc_dbg_step_irq;
  logic [31:0]  dpc_dbg_step_nmi;
  logic [31:0]  dpc_dbg_haltreq;
  logic [31:0]  dpc_dbg_haltreq_notrap;
  logic [31:0]  dpc_dbg_haltreq_irq;
  logic [31:0]  dpc_dbg_haltreq_nmi;
  logic [31:0]  halt_addr;
  logic [31:0]  exception_addr_at_entry;
  logic         exception_addr_at_entry_flag;
  // Locally track which debug cause should be used
  logic [2:0]   debug_cause_pri;
  logic [31:0]  boot_addr;
  logic [31:0]  mtvec_addr;

  logic         ebreak_allowed;

  int           stable_req_vs_valid_cnt;

  logic [31:0]  dpc_rdata_q;
  logic [31:0]  dcsr_rdata_q;
  logic [31:0]  debug_pc_o_q;


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

  assign mtvec_addr = {csr_mtvec.rvfi_csr_rdata[31:2], 2'b00};

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
    property p_enter_debug;
        $changed(debug_cause_pri) && (debug_cause_pri != 0) && !rvfi.rvfi_dbg_mode
        ##1 rvfi.rvfi_valid[->1]
        |->
        support_if.first_debug_ins;
    endproperty

    a_enter_debug: assert property(p_enter_debug)
        else `uvm_error(info_tag, $sformatf("Debug mode not entered after exepected cause %d", debug_cause_pri));


    // Check that dpc gets the correct value when debug mode is entered.
    a_debug_mode_pc: assert property(
        $rose(support_if.first_debug_ins)
        |->
        rvfi.rvfi_pc_rdata == halt_addr
        ) else `uvm_error(info_tag, $sformatf("Debug mode entered with wrong pc. pc==%08x", rvfi.rvfi_pc_rdata));


    generate // ignore CLIC, checked in clic asserts
        if (uvmt_cv32e40s_base_test_pkg::CORE_PARAM_CLIC==0) begin
            a_debug_mode_pc_dpc: assert property(
                $rose(support_if.first_debug_ins)
                |->
                (rvfi.rvfi_intr.intr && rvfi.rvfi_intr.interrupt
                ##1
                dpc_rdata_q == pc_at_dbg_req)
                or
                (csr_dpc.rvfi_csr_rdata == pc_at_dbg_req)
                ) else `uvm_error(info_tag, $sformatf("Debug mode entered with wrong dpc. dpc==%08x", csr_dpc.rvfi_csr_rdata));
        end
    endgenerate

    // Breaking down the above assert in to debug causes, to improve runtime
    property p_dpc_dbg_ebreak;
        $rose(support_if.first_debug_ins) && rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_EBREAK
        |->
        csr_dpc.rvfi_csr_rdata == dpc_dbg_ebreak;
    endproperty

    a_dpc_dbg_ebreak: assert property(p_dpc_dbg_ebreak)
        else `uvm_error(info_tag, $sformatf("DPC csr does not match expected on an ebreak, dpc==%08x", csr_dpc.rvfi_csr_rdata));

    property p_dpc_dbg_trigger;
        $rose(support_if.first_debug_ins) && rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_TRIGGER
        |->
        csr_dpc.rvfi_csr_rdata == dpc_dbg_trg;
    endproperty

    a_dpc_dbg_trigger: assert property(p_dpc_dbg_trigger)
        else `uvm_error(info_tag, $sformatf("DPC csr does not match expected on a trigger, dpc==%08x", csr_dpc.rvfi_csr_rdata));

    //TODO:MT Fully covered by those below, remove?
     property p_dpc_dbg_step;
        $rose(support_if.first_debug_ins) &&
        rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_STEP
        |->
        (csr_dpc.rvfi_csr_rdata == dpc_dbg_step)
        or
        (rvfi.rvfi_intr.intr && rvfi.rvfi_intr.interrupt
        ##1 dpc_rdata_q == dpc_dbg_step);
    endproperty

    generate // ignore CLIC, checked in clic asserts
        if (uvmt_cv32e40s_base_test_pkg::CORE_PARAM_CLIC==0) begin
            a_dpc_dbg_step: assert property(p_dpc_dbg_step)
                else `uvm_error(info_tag, $sformatf("DPC csr does not match expected on a step, dpc==%08x", csr_dpc.rvfi_csr_rdata));
        end
    endgenerate


    property p_dpc_dbg_step_notrap;
        $rose(support_if.first_debug_ins) &&
        !rvfi.rvfi_intr.intr &&
        rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_STEP
        |->
        (csr_dpc.rvfi_csr_rdata == dpc_dbg_step_notrap);
    endproperty

    a_dpc_dbg_step_notrap: assert property(p_dpc_dbg_step_notrap)
        else `uvm_error(info_tag, $sformatf("DPC csr does not match expected on a step, dpc==%08x", csr_dpc.rvfi_csr_rdata));


    property p_dpc_dbg_step_nmi;
        $rose(support_if.first_debug_ins) &&
        rvfi.is_nmi &&
        (rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_STEP)
        |=>
        dpc_rdata_q == dpc_dbg_step_nmi;
    endproperty

    a_dpc_dbg_step_nmi: assert property(p_dpc_dbg_step_nmi)
        else `uvm_error(info_tag, $sformatf("DPC csr does not match expected on a step, dpc==%08x", csr_dpc.rvfi_csr_rdata));


    property p_dpc_dbg_step_irq;
        $rose(support_if.first_debug_ins) &&
        rvfi.rvfi_intr.intr &&
        rvfi.rvfi_intr.interrupt &&
        !rvfi.is_nmi &&
        (rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_STEP)
        |=>
        dpc_rdata_q == dpc_dbg_step_irq;
    endproperty

    generate // ignore CLIC, checked in clic asserts
        if (uvmt_cv32e40s_base_test_pkg::CORE_PARAM_CLIC==0) begin
            a_dpc_dbg_step_irq: assert property(p_dpc_dbg_step_irq)
                else `uvm_error(info_tag, $sformatf("DPC csr does not match expected on a step, dpc==%08x", csr_dpc.rvfi_csr_rdata));
        end
    endgenerate

    //TODO:MT Fully covered by those below, remove?
    property p_dpc_dbg_haltreq;
        $rose(support_if.first_debug_ins) &&
        (rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_HALTREQ)
        |->
        (csr_dpc.rvfi_csr_rdata == dpc_dbg_haltreq)
        or
        (rvfi.rvfi_intr.intr && rvfi.rvfi_intr.interrupt
        ##1 dpc_rdata_q == dpc_dbg_haltreq);
    endproperty

    generate // ignore CLIC, checked in clic asserts
        if (uvmt_cv32e40s_base_test_pkg::CORE_PARAM_CLIC==0) begin
            a_dpc_dbg_haltreq: assert property(p_dpc_dbg_haltreq)
                else `uvm_error(info_tag, $sformatf("DPC csr does not match expected on a haltreq, dpc==%08x", csr_dpc.rvfi_csr_rdata));
        end
    endgenerate

    property p_dpc_dbg_haltreq_notrap;
        $rose(support_if.first_debug_ins) &&
        !rvfi.rvfi_intr.intr &&
        rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_HALTREQ
        |->
        (csr_dpc.rvfi_csr_rdata == dpc_dbg_haltreq_notrap);
    endproperty

    a_dpc_dbg_haltreq_notrap: assert property(p_dpc_dbg_haltreq_notrap)
        else `uvm_error(info_tag, $sformatf("DPC csr does not match expected on a haltreq, dpc==%08x", csr_dpc.rvfi_csr_rdata));


    property p_dpc_dbg_haltreq_nmi;
        $rose(support_if.first_debug_ins) &&
        rvfi.is_nmi &&
        (rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_HALTREQ)
        |=>
        dpc_rdata_q == dpc_dbg_haltreq_nmi;
    endproperty

    a_dpc_dbg_haltreq_nmi: assert property(p_dpc_dbg_haltreq_nmi)
        else `uvm_error(info_tag, $sformatf("DPC csr does not match expected on a haltreq, dpc==%08x", csr_dpc.rvfi_csr_rdata));


    property p_dpc_dbg_haltreq_irq;
        $rose(support_if.first_debug_ins) &&
        rvfi.rvfi_intr.intr &&
        rvfi.rvfi_intr.interrupt &&
        !rvfi.is_nmi &&
        (rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_HALTREQ)
        |=>
        dpc_rdata_q == dpc_dbg_haltreq_irq;
    endproperty

    generate // ignore CLIC, checked in clic asserts
        if (uvmt_cv32e40s_base_test_pkg::CORE_PARAM_CLIC==0) begin
            a_dpc_dbg_haltreq_irq: assert property(p_dpc_dbg_haltreq_irq)
                else `uvm_error(info_tag, $sformatf("DPC csr does not match expected on a haltreq, dpc==%08x", csr_dpc.rvfi_csr_rdata));
        end
    endgenerate

    // Check that dcsr.cause is as expected
    property p_dcsr_cause;
        $rose(support_if.first_debug_ins)
        |->
        (rvfi.rvfi_dbg == debug_cause_pri)
        or
        (support_if.recorded_dbg_req && (rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_HALTREQ));
    endproperty

    a_dcsr_cause: assert property(p_dcsr_cause)
        else `uvm_error(info_tag, "dcsr.cause was not as expected");



    // check that a stable debug_req is actually taken within reasonable time
    a_debug_req_taken: assert property(stable_req_vs_valid_cnt <= 3)
        else `uvm_error(info_tag, "External debug request not taken in reasonable time");


    // ebreak / c.ebreak without dcsr.ebreak[prv] results in exception at mtvec
    property p_ebreak_mmode_exception;
        rvfi.is_ebreak &&
        !rvfi.rvfi_dbg_mode &&
        rvfi.is_mmode &&
        !csr_dcsr.rvfi_csr_rdata[DCSR_EBREAKM_POS]
        |-> rvfi.rvfi_trap.trap && rvfi.rvfi_trap.exception
            or
            rvfi.rvfi_trap.trap && rvfi.rvfi_trap.debug && !(rvfi.rvfi_trap.debug_cause == cv32e40s_pkg::DBG_CAUSE_EBREAK);
    endproperty

    property p_ebreak_umode_exception;
        rvfi.is_ebreak &&
        !rvfi.rvfi_dbg_mode &&
        rvfi.is_umode &&
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
        rvfi.is_ebreak &&
        rvfi.rvfi_trap.debug_cause == cv32e40s_pkg::DBG_CAUSE_EBREAK && //The ebreak is actually taken
        rvfi.rvfi_dbg_mode
        ##1 rvfi.rvfi_valid[->1]
        |->
        rvfi.rvfi_dbg_mode &&
        ((csr_dcsr.rvfi_csr_rdata | (1 << DCSR_NMIP_POS)) == (dcsr_rdata_q | (1 << DCSR_NMIP_POS))) &&
        (csr_dpc.rvfi_csr_rdata == dpc_rdata_q) &&
        (rvfi.rvfi_pc_rdata == halt_addr);
    endproperty

    a_ebreak_during_debug_mode: assert property(p_ebreak_during_debug_mode)
        else `uvm_error(info_tag,$sformatf("Debug mode not restarted after ebreak"));

    cov_cebreak_dbg : cover property(
        rvfi.is_ebreak_compr && rvfi.rvfi_dbg_mode
    );
    cov_ebreak_dbg : cover property(
        rvfi.is_ebreak_noncompr && rvfi.rvfi_dbg_mode
    );




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


    // WFI/WFE in debug mode does not sleep

    property p_wfi_wfe_in_debug;
        cov_assert_if.debug_mode_q |-> !cov_assert_if.core_sleep_o;
    endproperty

    a_wfi_wfe_in_debug : assert property(p_wfi_wfe_in_debug)
        else `uvm_error(info_tag, $sformatf("WFI or WFE in debug mode cause core_sleep_o=1"));


    // Debug request while sleeping makes core wake up and enter debug mode with cause=haltreq

    property p_sleep_debug_req_wu;
        (cov_assert_if.ctrl_fsm_cs == SLEEP) && cov_assert_if.debug_req_i
        |=>
        !cov_assert_if.core_sleep_o;
    endproperty

    a_sleep_debug_req_wu : assert property(p_sleep_debug_req_wu)
        else `uvm_error(info_tag,
            $sformatf("Did not exit sleep(== %d) after debug_req_i. ",
                cov_assert_if.core_sleep_o));

    property p_sleep_debug_req;
        (cov_assert_if.ctrl_fsm_cs == SLEEP) && cov_assert_if.debug_req_i
        ##0(cov_assert_if.debug_req_i throughout cov_assert_if.debug_halted[->1])
        ##0 rvfi.rvfi_valid[->1]
        |->
        rvfi.rvfi_dbg_mode && rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_HALTREQ;
    endproperty

    a_sleep_debug_req : assert property(p_sleep_debug_req)
        else `uvm_error(info_tag,
            $sformatf("Did not enter debug haltreq after debug_req_i during sleep. Debug_mode = %d cause = %d",
                rvfi.rvfi_dbg_mode, rvfi.rvfi_dbg));

    // Accessing debug regs in m-mode is illegal
    property p_debug_regs_mumode(csr_addr, csr_wmask);
        rvfi.is_csr_instr(csr_addr) && !rvfi.rvfi_dbg_mode
        |->
        // instruction traps either as illegal or trigger
        rvfi.rvfi_trap.trap && (
        (rvfi.rvfi_trap.exception && (rvfi.rvfi_trap.exception_cause == cv32e40s_pkg::EXC_CAUSE_ILLEGAL_INSN) && (csr_wmask == 0))
        ||
        (rvfi.rvfi_trap.debug && (rvfi.rvfi_trap.debug_cause == cv32e40s_pkg::DBG_CAUSE_TRIGGER))
        );
    endproperty

    a_debug_regs_mumode_dcsr : assert property(p_debug_regs_mumode(CSR_ADDR_DCSR, csr_dcsr.rvfi_csr_wmask))
        else `uvm_error(info_tag, "Accessing debug reg DCSR in M- or U-mode did not result in illegal instruction");

    a_debug_regs_mumode_dpc : assert property(p_debug_regs_mumode(CSR_ADDR_DPC, csr_dpc.rvfi_csr_wmask))
        else `uvm_error(info_tag, "Accessing debug reg DPC in M- or U-mode did not result in illegal instruction");

    a_debug_regs_mumode_dscratch0 : assert property(p_debug_regs_mumode(CSR_ADDR_DSCRATCH0, csr_dscratch0.rvfi_csr_wmask))
        else `uvm_error(info_tag, "Accessing debug reg DSCRATCH0 in M- or U-mode did not result in illegal instruction");

    a_debug_regs_mumode_dscratch1 : assert property(p_debug_regs_mumode(CSR_ADDR_DSCRATCH1, csr_dscratch1.rvfi_csr_wmask))
        else `uvm_error(info_tag, "Accessing debug reg DSCRATCH1 in M- or U-mode did not result in illegal instruction");


    // Exception while single step -> PC is set to exception handler before debug
    property p_single_step_exception;
        rvfi.rvfi_valid && //valid
        !rvfi.rvfi_dbg_mode && //not in dbg
        csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS] && // step set
        !(rvfi.is_dbg_trg) && // not trigger
        rvfi.rvfi_trap.exception // exception
        ##1 rvfi.rvfi_valid[->1]
        |->
        rvfi.rvfi_dbg_mode &&
        (csr_dpc.rvfi_csr_rdata == mtvec_addr);

    endproperty

    a_single_step_exception : assert property(p_single_step_exception)
        else `uvm_error(info_tag, "PC not set to exception handler after single step with exception");


    // Trigger during single step
    property p_single_step_trigger;
        (rvfi.is_dbg_trg) &&
        !rvfi.rvfi_dbg_mode &&
        csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS]
        ##1 rvfi.rvfi_valid[->1]
        |->
        rvfi.rvfi_dbg_mode && ((rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_TRIGGER) ||
        (support_if.recorded_dbg_req && (rvfi.rvfi_dbg == cv32e40s_pkg::DBG_CAUSE_HALTREQ)));
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


    // Executing with single step results in debug mode

    property p_single_step;
        rvfi.rvfi_valid &&
        !rvfi.rvfi_dbg_mode &&
        csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS]
        ##1 rvfi.rvfi_valid[->1]
        |->
        rvfi.rvfi_dbg_mode;
    endproperty

    a_single_step: assert property(p_single_step)
        else `uvm_error(info_tag, "Debug mode not entered for single step");


    property p_mumode_dret;
        rvfi.is_dret && !rvfi.rvfi_dbg_mode
        |-> rvfi.rvfi_trap;
    endproperty

    a_mumode_dret : assert property(p_mumode_dret)
        else `uvm_error(info_tag, "Executing dret in M-mode did not result in illegal instruction");


    // dret in D-mode will restore pc (if no re-entry or interrupt intervenes)

    property p_dmode_dret_pc;
        int dpc;
        (rvfi.is_dret && rvfi.rvfi_dbg_mode,
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
        (rvfi.is_dret && rvfi.rvfi_dbg_mode,
         dpc = csr_dpc.rvfi_csr_rdata)
        ##1
        rvfi.rvfi_valid[->1]
        ##0 (rvfi.rvfi_intr && !rvfi.rvfi_dbg_mode && !rvfi.is_nmi)
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
        ##0 (!rvfi.rvfi_dbg_mode && rvfi.is_nmi)
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
        ##0 (!rvfi.rvfi_dbg_mode && rvfi.is_nmi)
        ##0 (csr_mepc.rvfi_csr_rdata != dpc);
    endproperty

    cov_dmode_dret_pc_nmi_neq : cover property(p_dmode_dret_pc_nmi_neq);


    // dret in D-mode will exit D-mode

    property p_dmode_dret_exit;
        cov_assert_if.debug_mode_q && cov_assert_if.is_dret
        |=>
        !cov_assert_if.debug_mode_q;
    endproperty

    a_dmode_dret_exit : assert property(p_dmode_dret_exit)
        else `uvm_error(info_tag, "Dret did not exit debug mode");


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


    // debug_req at reset should result in debug mode and no instructions executed

    property p_debug_at_reset;
        (cov_assert_if.ctrl_fsm_cs == cv32e40s_pkg::RESET) && cov_assert_if.debug_req_i
        ##0 (cov_assert_if.debug_req_i throughout !cov_assert_if.debug_havereset[->1])
        ##0 rvfi.rvfi_valid[->1]
        |->
        rvfi.rvfi_dbg_mode;
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
      ##1
      (cov_assert_if.debug_havereset  == 0)
      && (cov_assert_if.debug_running == 1)
      && (cov_assert_if.debug_halted  == 0)
      );

    cov_havereset_to_halted : cover property (
      (cov_assert_if.debug_havereset  == 1)
      && (cov_assert_if.debug_running == 0)
      && (cov_assert_if.debug_halted  == 0)
      ##1
      (cov_assert_if.debug_havereset  == 0)
      && (cov_assert_if.debug_running == 0)
      && (cov_assert_if.debug_halted  == 1)
      );

    // step vs nmi
    // check that stepie disables nmi
    property p_stepie_irq_dis;
        rvfi.is_dret && csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS] && !csr_dcsr.rvfi_csr_rdata[DCSR_STEPIE_POS]
        ##1 rvfi.rvfi_valid[->1]
        |->
        !(rvfi.rvfi_intr.intr && rvfi.rvfi_intr.interrupt);
    endproperty

    a_stepie_irq_dis : assert property(p_stepie_irq_dis)
        else `uvm_error(info_tag, "Single stepping should ignore all interrupts if stepie is not set");

    cov_step_stepie_nmi : cover property (
        rvfi.is_dret
        && csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS]
        && !csr_dcsr.rvfi_csr_rdata[DCSR_STEPIE_POS]
        && csr_dcsr.rvfi_csr_rdata[DCSR_NMIP_POS]
    );

    property p_stepie_irq_en;
        rvfi.is_dret
        && csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS]
        && csr_dcsr.rvfi_csr_rdata[DCSR_STEPIE_POS]
        && csr_dcsr.rvfi_csr_rdata[DCSR_NMIP_POS]
        ##1 rvfi.rvfi_valid[->1]
        |->
        rvfi.rvfi_intr.intr && rvfi.rvfi_intr.interrupt;
    endproperty

    a_stepie_irq_en : assert property(p_stepie_irq_en)
        else `uvm_error(info_tag, "Single stepping should take NMI if stepie is set");

    // step trap handler entry, no retire

    // if the next instruction after a single step dret is in debug mode,
    // a trap entry has to be the cause.
    property p_step_trap_handler_entry;
        (rvfi.is_dret &&
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
        rvfi.is_dret && csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS] && csr_dcsr.rvfi_csr_rdata[DCSR_STEPIE_POS]
        ##1 rvfi.rvfi_valid[->1]
        ##0 !rvfi.rvfi_dbg_mode
        |->
        !rvfi.rvfi_intr.intr || (rvfi.rvfi_intr.intr && rvfi.rvfi_trap.clicptr);
    endproperty

    a_step_no_trap : assert property(p_step_no_trap)
        else `uvm_error(info_tag, "single stepping should not retire a trap handler entry");


    // Check that we cover the case where a debug_req_i
    // comes while flushing due to an illegal insn, causing
    // dpc to be set to the exception handler entry addr

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
        s_illegal_insn_debug_req_ante ##0 s_illegal_insn_debug_req_conse ##0 (cov_assert_if.dpc_q != 0));

    a_illegal_insn_debug_req : assert property(s_illegal_insn_debug_req_ante |-> s_illegal_insn_debug_req_conse)
        else `uvm_error(info_tag, "Debug mode not entered correctly while handling illegal instruction!");

    // OBI dbg signal needs to correlate to debug mode

    property p_obi_dbg_instr;
        (instr_obi.req && !support_if.instr_bus_addr_ph_cont && instr_obi.dbg)
        |->
        cov_assert_if.debug_mode_if;
    endproperty

    a_obi_dbg_instr : assert property(p_obi_dbg_instr)
    else `uvm_error(info_tag, "OBI instruction bus dbg signal high for non-debug transaction");

    property p_obi_dbg_instr_inv;
        (instr_obi.req && !support_if.instr_bus_addr_ph_cont && !instr_obi.dbg)
        |->
        !cov_assert_if.debug_mode_if;
    endproperty

    a_obi_dbg_instr_inv : assert property(p_obi_dbg_instr_inv)
    else `uvm_error(info_tag, "OBI instruction bus dbg signal low for debug transaction");

    property p_obi_dbg_data;
        (data_obi.req && !support_if.data_bus_addr_ph_cont && data_obi.dbg)
        |->
        cov_assert_if.debug_mode_q;
    endproperty

    a_obi_dbg_data : assert property(p_obi_dbg_data)
    else `uvm_error(info_tag, "OBI data bus dbg signal high for non-debug transaction");

    property p_obi_dbg_data_inv;
        (data_obi.req && !support_if.data_bus_addr_ph_cont && !data_obi.dbg)
        |->
        !cov_assert_if.debug_mode_q;
    endproperty

    a_obi_dbg_data_inv : assert property(p_obi_dbg_data_inv)
    else `uvm_error(info_tag, "OBI data bus dbg signal low for debug transaction");

    // Pending NMI shall be visible in dcsr.nmip
    property p_dcsr_nmip;
        rvfi.rvfi_dbg_mode && rvfi.is_csr_read(CSR_ADDR_DCSR) && csr_dcsr.rvfi_csr_rdata[DCSR_NMIP_POS]
        |->
        rvfi.rvfi_nmip[0];
    endproperty

    a_dcsr_nmip : assert property(p_dcsr_nmip)
    else `uvm_error(info_tag, "NMI pending not reflected in dcsr.nmip");

    // debug_pc_o shall show PC of last retired instruction
    property p_debug_pc_o;
        (rvfi.rvfi_valid && !rvfi.rvfi_trap.trap)
        |->
        rvfi.rvfi_pc_rdata == debug_pc_o_q;
    endproperty

    a_debug_pc_o : assert property(p_debug_pc_o)
    else `uvm_error(info_tag, "debug_pc_o is not driven correctly")

    property p_debug_pc_o_inv;
        int dbg_pc;
        (cov_assert_if.debug_pc_valid_o, dbg_pc = cov_assert_if.debug_pc_o)
        ##1 rvfi.rvfi_valid[->1]
        |->
        rvfi.rvfi_pc_rdata == dbg_pc;
    endproperty

    a_debug_pc_o_inv : assert property(p_debug_pc_o_inv)
    else `uvm_error(info_tag, "debug_pc_o is not driven correctly")


    // Exceptions don't update "mcause"

    a_dbg_mcause: assert property (
      rvfi.rvfi_valid  &&
      rvfi.rvfi_dbg_mode  &&
      rvfi.rvfi_trap
      |->
      !csr_mstatus.rvfi_csr_wmask
    ) else `uvm_error(info_tag, "dmode exceptions shouldn't update mcause")


    // "mret" causes exceptions

    a_dbg_mret: assert property (
      rvfi.is_mret  &&
      rvfi.rvfi_dbg_mode
      |->
      rvfi.rvfi_valid  &&
      rvfi.rvfi_trap.trap  &&
      rvfi.rvfi_trap.exception
    ) else `uvm_error(info_tag, "dmode mret should except")


    // -------------------------------------------
    // Capture internal states for use in checking
    // -------------------------------------------

    always @(posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if(!cov_assert_if.rst_ni) begin
            pc_at_dbg_req <= 32'h0;
        end else begin
            //NMI has highest priority for dpc
            if(rvfi.is_nmi && rvfi.rvfi_dbg_mode) begin
                if (csr_mtvec.rvfi_csr_rdata[1:0] == 1) begin // vectored CLINT
                    pc_at_dbg_req <= mtvec_addr+'h3C;
                end else begin //unvectored CLINT
                    pc_at_dbg_req <= mtvec_addr;
                end
            // if the debug cause is synchronous debug entry IRQ is "taken" first4
            end else if (   rvfi.rvfi_valid &&
                            rvfi.rvfi_dbg_mode &&
                            rvfi.rvfi_intr.intr &&
                            rvfi.rvfi_intr.interrupt) begin
                if (csr_mtvec.rvfi_csr_rdata[1:0] == 1) begin //vectored CLINT
                    pc_at_dbg_req <= mtvec_addr + (rvfi.rvfi_intr.cause << 2);
                end else begin //unvectored CLINT
                    pc_at_dbg_req <= mtvec_addr;
                end
            // Exception with exception trigger active
            end else if (rvfi.is_dbg_trg && rvfi.rvfi_trap.exception) begin
                pc_at_dbg_req <= rvfi.rvfi_pc_wdata;

            end else if ((rvfi.is_ebreak && ebreak_allowed)|| rvfi.is_dbg_trg) begin
                pc_at_dbg_req <= rvfi.rvfi_pc_rdata;

            end else if (support_if.first_fetch) begin
                pc_at_dbg_req <= {cov_assert_if.boot_addr_i[31:2], 2'b00};

            end else if (rvfi.rvfi_valid) begin
                pc_at_dbg_req <= rvfi.rvfi_pc_wdata;
            end
        end
    end

    // Breaking down the above structure on debug cause, to improve likelyhood of formal convergence
    always @(posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if(!cov_assert_if.rst_ni) begin
            dpc_dbg_ebreak <= 32'h0;
        end else begin
            if (rvfi.is_ebreak) begin
                dpc_dbg_ebreak <=  rvfi.rvfi_pc_rdata;
            end
        end
    end

    always @(posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if(!cov_assert_if.rst_ni) begin
            dpc_dbg_trg <= 32'h0;
        end else begin
            if (rvfi.is_dbg_trg && rvfi.rvfi_trap.exception) begin
                dpc_dbg_trg <=  rvfi.rvfi_pc_wdata;
            end else if (rvfi.is_dbg_trg) begin
                dpc_dbg_trg <=  rvfi.rvfi_pc_rdata;
            end
        end
    end

    always @(posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if(!cov_assert_if.rst_ni) begin
            dpc_dbg_step            <= 32'h0;
            dpc_dbg_step_notrap     <= 32'h0;
            dpc_dbg_step_irq        <= 32'h0;
            dpc_dbg_step_nmi        <= 32'h0;
            dpc_dbg_haltreq         <= 32'h0;
            dpc_dbg_haltreq_notrap  <= 32'h0;
            dpc_dbg_haltreq_irq     <= 32'h0;
            dpc_dbg_haltreq_nmi     <= 32'h0;
        end else begin
            //NMI has highest priority for dpc
            if(rvfi.is_nmi && rvfi.rvfi_dbg_mode) begin
                if (csr_mtvec.rvfi_csr_rdata[1:0] == 1) begin // vectored CLINT
                    dpc_dbg_step        <= mtvec_addr+'h3C;
                    dpc_dbg_step_nmi    <= mtvec_addr+'h3C;
                    dpc_dbg_haltreq     <= mtvec_addr+'h3C;
                    dpc_dbg_haltreq_nmi <= mtvec_addr+'h3C;
                end else begin //unvectored CLINT
                    dpc_dbg_step        <= mtvec_addr;
                    dpc_dbg_step_nmi    <= mtvec_addr;
                    dpc_dbg_haltreq     <= mtvec_addr;
                    dpc_dbg_haltreq_nmi <= mtvec_addr;
                end

            // if the debug cause is synchronous debug entry IRQ is "taken" first4
            end else if (   rvfi.rvfi_valid &&
                            rvfi.rvfi_dbg_mode &&
                            rvfi.rvfi_intr.intr &&
                            rvfi.rvfi_intr.interrupt) begin
                if (csr_mtvec.rvfi_csr_rdata[1:0] == 1) begin //vectored CLINT
                    dpc_dbg_step        <= mtvec_addr + (rvfi.rvfi_intr.cause << 2);
                    dpc_dbg_step_irq    <= mtvec_addr + (rvfi.rvfi_intr.cause << 2);
                    dpc_dbg_haltreq     <= mtvec_addr + (rvfi.rvfi_intr.cause << 2);
                    dpc_dbg_haltreq_irq <= mtvec_addr + (rvfi.rvfi_intr.cause << 2);
                end else begin //unvectored CLINT
                    dpc_dbg_step        <= mtvec_addr;
                    dpc_dbg_step_irq    <= mtvec_addr;
                    dpc_dbg_haltreq     <= mtvec_addr;
                    dpc_dbg_haltreq_irq <= mtvec_addr;
                end

            end else if (rvfi.rvfi_valid) begin
                dpc_dbg_step            <=  rvfi.rvfi_pc_wdata;
                dpc_dbg_haltreq         <=  rvfi.rvfi_pc_wdata;

            end else if (support_if.first_fetch) begin
                dpc_dbg_haltreq         <= {cov_assert_if.boot_addr_i[31:2], 2'b00};
            end
            //keep separate to truly disconnect
            if(rvfi.rvfi_valid) begin
                dpc_dbg_step_notrap     <=  rvfi.rvfi_pc_wdata;
                dpc_dbg_haltreq_notrap  <=  rvfi.rvfi_pc_wdata;
            end else if (support_if.first_fetch) begin
                dpc_dbg_haltreq_notrap  <= {cov_assert_if.boot_addr_i[31:2], 2'b00};
            end


        end
    end


    always @(posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if(!cov_assert_if.rst_ni) begin
            dpc_rdata_q <= 32'h0;
            dcsr_rdata_q <= 32'h0;
            debug_pc_o_q <= 32'h0;
        end else begin
            if(rvfi.rvfi_valid) begin
                dpc_rdata_q <= csr_dpc.rvfi_csr_rdata;
                dcsr_rdata_q <= csr_dcsr.rvfi_csr_rdata;
            end
            if(cov_assert_if.debug_pc_valid_o) begin
                debug_pc_o_q <= cov_assert_if.debug_pc_o;
            end
        end
    end


  // Capture start values
  always@ (posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
    if(!cov_assert_if.rst_ni) begin
          halt_addr <= 0;
          boot_addr <= 0;
    end else begin
        if(support_if.first_fetch) begin
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
        end else begin
            if (rvfi.is_dbg_trg) begin
                debug_cause_pri <= cv32e40s_pkg::DBG_CAUSE_TRIGGER;
            end else if(rvfi.is_ebreak && ebreak_allowed) begin
                debug_cause_pri <= cv32e40s_pkg::DBG_CAUSE_EBREAK;
            end else if(rvfi.rvfi_valid && csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS]) begin  // "step"
                debug_cause_pri <= cv32e40s_pkg::DBG_CAUSE_STEP;
            end else if(rvfi.is_dret && !csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS]) begin
                debug_cause_pri <= 3'b000;  // (not a cause)
            end
        end
    end

    assign ebreak_allowed = (rvfi.is_mmode && csr_dcsr.rvfi_csr_rdata[DCSR_EBREAKM_POS]) || (rvfi.is_umode && csr_dcsr.rvfi_csr_rdata[DCSR_EBREAKU_POS]);


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

    sequence s_dbg_with_nmi_dret_stepie(bit stepie_value);
          rvfi.rvfi_dbg_mode
       && rvfi.is_dret
       && rvfi.rvfi_nmip[0]
       && csr_dcsr.rvfi_csr_rdata[DCSR_STEPIE_POS] == stepie_value
       && csr_dcsr.rvfi_csr_rdata[DCSR_STEP_POS]
       && rvfi.rvfi_valid
      ##1
       rvfi.rvfi_valid[->1]
      ;
    endsequence : s_dbg_with_nmi_dret_stepie

    property p_dbg_with_nmi_dret_stepie(bit stepie_value);
      reject_on(
          csr_mtvec.rvfi_csr_rdata[31:2] == 0 // ignore lower bits
       || csr_dpc.rvfi_csr_rdata == 0
       || csr_mtvec.rvfi_csr_rdata == csr_dpc.rvfi_csr_rdata
       || rvfi.rvfi_trap.exception)
      s_dbg_with_nmi_dret_stepie(stepie_value)
      ;
    endproperty : p_dbg_with_nmi_dret_stepie


    cov_dbg_with_nmi_dret_stepie:   cover property (p_dbg_with_nmi_dret_stepie(1'b1));
    cov_dbg_with_nmi_dret_stepie_n: cover property (p_dbg_with_nmi_dret_stepie(1'b0));

endmodule : uvmt_cv32e40s_debug_assert
