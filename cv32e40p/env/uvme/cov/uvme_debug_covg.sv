///////////////////////////////////////////////////////////////////////////////
// Copyright 2020 OpenHW Group
// Copyright 2020 BTA Design Services
// Copyright 2020 Silicon Labs, Inc.
// Copyright 2023 Dolphin Design
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//
///////////////////////////////////////////////////////////////////////////////


class uvme_debug_covg extends uvm_component;

    /*
    * Class members
    */
    uvme_cv32e40p_cntxt_c  cntxt;


    `uvm_component_utils(uvme_debug_covg);

    extern function new(string name = "debug_covg", uvm_component parent = null);
    extern function void build_phase(uvm_phase phase);
    extern task run_phase(uvm_phase phase);

    extern task sample_clk_i();
    extern task sample_debug_req_i();

    /*
    * Covergroups
    */

  covergroup cg_debug_mode_ext ;
          `per_instance_fcov
          state: coverpoint cntxt.debug_cov_vif.mon_cb.ctrl_fsm_cs{
              ignore_bins ignore_pulp_states = {cv32e40p_pkg::ELW_EXE, cv32e40p_pkg::IRQ_FLUSH_ELW, cv32e40p_pkg::DECODE_HWLOOP};
          }
  endgroup : cg_debug_mode_ext

  // Waive duplicate code since embedded covergroups are used
  //@DVT_LINTER_WAIVER_START "SR20211012_1" disable SVTB.33.1.0

  // Cover that we execute ebreak with dcsr.ebreakm==1
  covergroup cg_ebreak_execute_with_ebreakm;
          `per_instance_fcov
          ex: coverpoint cntxt.debug_cov_vif.mon_cb.is_ebreak {
                  bins active = {1};
          }
          ebreakm_set: coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[15] {
                  bins active = {1};
          }
          dm : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
                  bins active = {1};
          }
          ebreak_with_ebreakm: cross ex, ebreakm_set;
          ebreak_in_debug : cross ex, dm;
  endgroup

  // Cover that we execute c.ebreak with dcsr.ebreakm==1
  covergroup cg_cebreak_execute_with_ebreakm;
          `per_instance_fcov
          ex: coverpoint cntxt.debug_cov_vif.mon_cb.is_cebreak {
                  bins active = {1};
          }
          ebreakm_set: coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[15] {
                  bins active = {1};
          }
          dm : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
                  bins active = {1};
          }
          cebreak_with_ebreakm: cross ex, ebreakm_set;
          cebreak_in_debug : cross ex, dm;
  endgroup

  // Cover that we execute ebreak with dcsr.ebreakm==0
  covergroup cg_ebreak_execute_without_ebreakm;
          `per_instance_fcov
          ex: coverpoint cntxt.debug_cov_vif.mon_cb.is_ebreak {
                  bins active = {1};
          }
          ebreakm_clear: coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[15] {
                  bins active = {0};
          }
          step: coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[2] {
                  bins active = {1};
          }
          nostep: coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[2] {
                  bins active = {0};
          }
          ebreak_regular_nodebug: cross ex, ebreakm_clear, nostep;
          ebreak_step_nodebug : cross ex, ebreakm_clear, step;
  endgroup

  // Cover that we execute c.ebreak with dcsr.ebreakm==0
  covergroup cg_cebreak_execute_without_ebreakm;
          `per_instance_fcov
          ex: coverpoint cntxt.debug_cov_vif.mon_cb.is_cebreak {
                  bins active = {1};
          }
          ebreakm_clear: coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[15] {
                  bins active = {0};
          }
          step: coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[2] {
                  bins active = {1};
          }
          nostep: coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[2] {
                  bins active = {0};
          }
          cebreak_regular_nodebug: cross ex, ebreakm_clear, nostep;
          cebreak_step_nodebug : cross ex, ebreakm_clear, step;
  endgroup
  //@DVT_LINTER_WAIVER_END "SR20211012_1"

    // Cover that we hit a trigger match
    covergroup cg_trigger_match;
        `per_instance_fcov
        en : coverpoint cntxt.debug_cov_vif.mon_cb.tdata1[2] {
            bins active = {1};
        }
        match: coverpoint cntxt.debug_cov_vif.mon_cb.trigger_match_i {
            bins hit = {1};
        }
        ok_match: cross en, match;
    endgroup

    // cover that we hit pc==tdata2  without having enabled trigger in m/d-mode
    // cover hit in d-mode with trigger enabled (no action)
    covergroup cg_trigger_match_disabled;
        `per_instance_fcov
        dis : coverpoint cntxt.debug_cov_vif.mon_cb.tdata1[2] {
            bins hit = {0};
        }
        en : coverpoint cntxt.debug_cov_vif.mon_cb.tdata1[2] {
            bins hit = {1};
        }
        match: coverpoint cntxt.debug_cov_vif.mon_cb.addr_match {
           bins hit = {1};
        }
        mmode : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
           bins m = {0};
        }
        dmode : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
           bins m = {1};
        }
        m_match_without_en : cross dis, match, mmode;
        d_match_without_en : cross dis, match, dmode;
        d_match_with_en    : cross en, match, dmode;
    endgroup

    // Cover that we hit an exception during debug mode
    covergroup cg_debug_mode_exception;
        `per_instance_fcov
        dm : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins hit  = {1};
        }
        ill : coverpoint cntxt.debug_cov_vif.mon_cb.illegal_insn_q {
            bins hit = {1};
        }
        ex_in_debug : cross dm, ill;
    endgroup

    // Cover that we hit an ecall during debug mode
    covergroup cg_debug_mode_ecall;
        `per_instance_fcov
        dm : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins hit  = {1};
        }
        ill : coverpoint cntxt.debug_cov_vif.mon_cb.ecall_insn_i {
            bins hit = {1};
        }
        ex_in_debug : cross dm, ill;
    endgroup

    // Cover that we get interrupts while in debug mode
    covergroup cg_irq_in_debug;
        `per_instance_fcov
        dm : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins hit  = {1};
        }
        irq : coverpoint |cntxt.debug_cov_vif.mon_cb.irq_i {
            bins hit = {1};
        }
        ex_in_debug : cross dm, irq;
    endgroup

    // Cover that hit a WFI insn in debug mode
    covergroup cg_wfi_in_debug;
        `per_instance_fcov
        iswfi : coverpoint cntxt.debug_cov_vif.mon_cb.is_wfi {
                bins hit  = {1};
        }
        dm : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins hit = {1};
        }
        dm_wfi : cross iswfi, dm;
    endgroup

    // Cover that we get a debug_req while in wfi
    covergroup cg_wfi_debug_req;
        `per_instance_fcov
        inwfi : coverpoint cntxt.debug_cov_vif.mon_cb.in_wfi {
                bins hit  = {1};
        }
        dreq: coverpoint cntxt.debug_cov_vif.mon_cb.debug_req_i {
            bins hit = {1};
        }
        dm_wfi : cross inwfi, dreq;
    endgroup

    // Cover that we perform single stepping
    covergroup cg_single_step;
        `per_instance_fcov
        step : coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[2] {
                bins en  = {1};
        }
        mmode: coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins hit = {0};
        }
        trigger : coverpoint cntxt.debug_cov_vif.mon_cb.trigger_match_i {
            bins hit = {1};
        }
        wfi : coverpoint cntxt.debug_cov_vif.mon_cb.is_wfi {
            bins hit = {1};
        }
        ill : coverpoint cntxt.debug_cov_vif.mon_cb.illegal_insn_i {
            bins hit = {1};
        }
        pc_will_trig : coverpoint cntxt.debug_cov_vif.mon_cb.dpc_will_hit {
            bins hit = {1};
        }
        stepie : coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[11];
        mmode_step : cross step, mmode;
        mmode_step_trigger_match : cross step, mmode, trigger;
        mmode_step_wfi : cross step, mmode, wfi;
        mmode_step_stepie : cross step, mmode, stepie;
        mmode_step_illegal : cross step, mmode, ill;
        mmode_step_next_pc_will_match : cross step, mmode, pc_will_trig;
    endgroup

    // Cover dret is executed in machine mode
    covergroup cg_mmode_dret;
        `per_instance_fcov
        mmode : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q;
        dret_ins : coverpoint cntxt.debug_cov_vif.mon_cb.is_dret {
            bins hit = {1};
        }
        dret_ex : cross mmode, dret_ins;
    endgroup

    // Cover debug_req and irq asserted on same cycle
    covergroup cg_irq_dreq;
        `per_instance_fcov
        dreq : coverpoint cntxt.debug_cov_vif.mon_cb.debug_req_i {
                bins trans_active  = (1'b0 => 1'b1);
        }
        irq  : coverpoint |cntxt.debug_cov_vif.mon_cb.irq_i {
                bins trans_active = (1'b0 => 1'b1);
        }
        trigger : coverpoint cntxt.debug_cov_vif.mon_cb.trigger_match_i {
            bins hit = {1};
        }
        ill : coverpoint cntxt.debug_cov_vif.mon_cb.illegal_insn_i {
            bins hit = {1};
        }
        ebreak : coverpoint cntxt.debug_cov_vif.mon_cb.is_ebreak {
            bins active= {1'b1};
        }
        cebreak : coverpoint cntxt.debug_cov_vif.mon_cb.is_cebreak {
            bins active= {1'b1};
        }
        branch : coverpoint cntxt.debug_cov_vif.mon_cb.branch_in_decode {
            bins active= {1'b1};
        }
        mulhsu : coverpoint cntxt.debug_cov_vif.mon_cb.is_mulhsu {
            bins active= {1'b1};
        }
        dreq_and_ill : cross dreq, ill;
        irq_and_dreq : cross dreq, irq;
        irq_dreq_trig_ill : cross dreq, irq, trigger, ill;
        irq_dreq_trig_cebreak : cross dreq, irq, trigger, cebreak;
        irq_dreq_trig_ebreak : cross dreq, irq, trigger, ebreak;
        irq_dreq_trig_branch : cross dreq, irq, trigger, branch;
        irq_dreq_trig_multicycle : cross dreq, irq, trigger, mulhsu;
    endgroup

    // Cover access to dcsr, dpc and dscratch0/1 in D-mode
    covergroup cg_debug_regs_d_mode;
        `per_instance_fcov
        mode : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins M = {1};
        }

        access : coverpoint cntxt.debug_cov_vif.mon_cb.csr_access {
            bins hit = {1};
        }
        op : coverpoint cntxt.debug_cov_vif.mon_cb.csr_op {
            bins read = {'h0};
            bins write = {'h1};
        }
        addr  : coverpoint cntxt.debug_cov_vif.mon_cb.id_stage_instr_rdata_i[31:20] { // csr addr not updated if illegal access
            bins dcsr = {'h7B0};
            bins dpc = {'h7B1};
            bins dscratch0 = {'h7B2};
            bins dscratch1 = {'h7B3};
        }
        dregs_access : cross mode, access, op, addr;
    endgroup

    // Cover access to dcsr, dpc and dscratch0/1 in M-mode
    covergroup cg_debug_regs_m_mode;
        `per_instance_fcov
        mode : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins M = {0};
        }

        access : coverpoint cntxt.debug_cov_vif.mon_cb.csr_access {
            bins hit = {1};
        }
        op : coverpoint cntxt.debug_cov_vif.mon_cb.csr_op_dec {
            bins read = {1'h0};
            bins write = {1'h1};
        }
        addr  : coverpoint cntxt.debug_cov_vif.mon_cb.id_stage_instr_rdata_i[31:20] { // csr addr not updated if illegal access
            bins dcsr = {'h7B0};
            bins dpc = {'h7B1};
            bins dscratch0 = {'h7B2};
            bins dscratch1 = {'h7B3};
        }
        dregs_access : cross mode, access, op, addr;
    endgroup
    // Cover access to trigger registers
    // Do we need to cover all READ/WRITE/SET/CLEAR from m-mode?
    covergroup cg_trigger_regs;
        `per_instance_fcov
        mode : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q; // Only M and D supported
        access : coverpoint cntxt.debug_cov_vif.mon_cb.csr_access {
            bins hit = {1};
        }
        op : coverpoint cntxt.debug_cov_vif.mon_cb.csr_op {
            bins read = {'h0};
            bins write = {'h1};
        }
        addr  : coverpoint cntxt.debug_cov_vif.mon_cb.id_stage_instr_rdata_i[31:20]{ // csr addr not updated if illegal access
            bins tsel = {'h7A0};
            bins tdata1 = {'h7A1};
            bins tdata2 = {'h7A2};
            bins tdata3 = {'h7A3};
            bins tinfo  = {'h7A4};
        }
        tregs_access : cross mode, access, op, addr;
    endgroup

    // Cover that we run with counters mcycle and minstret enabled
    covergroup cg_counters_enabled;
        `per_instance_fcov
        mcycle_en : coverpoint cntxt.debug_cov_vif.mon_cb.mcountinhibit_q[0];
        minstret_en : coverpoint cntxt.debug_cov_vif.mon_cb.mcountinhibit_q[2];
    endgroup

    // Cover that we get a debug_req_i while in RESET state
    covergroup cg_debug_at_reset;
        `per_instance_fcov
        state : coverpoint cntxt.debug_cov_vif.mon_cb.ctrl_fsm_cs {
            bins reset= {cv32e40p_pkg::RESET};
        }
         dbg : coverpoint cntxt.debug_cov_vif.mon_cb.debug_req_i {
            bins active= {1'b1};
        }
        dbg_at_reset : cross state, dbg;
    endgroup

    // Cover that we execute fence and fence.i in debug mode
    covergroup cg_fence_in_debug;
        `per_instance_fcov
        mode : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins debug= {1'b1};
        }
        fence : coverpoint cntxt.debug_cov_vif.mon_cb.fence_i {
            bins active= {1'b1};
        }
        fence_in_debug : cross mode, fence;
    endgroup

    // Cover that we get all combinations of debug causes
    covergroup cg_debug_causes;
        `per_instance_fcov
        tmatch : coverpoint cntxt.debug_cov_vif.mon_cb.trigger_match_i {
            bins match= {1'b1};
        }
        tnomatch : coverpoint cntxt.debug_cov_vif.mon_cb.trigger_match_i {
            bins nomatch= {1'b0};
        }
         ebreak : coverpoint cntxt.debug_cov_vif.mon_cb.is_ebreak {
            bins active= {1'b1};
        }
         cebreak : coverpoint cntxt.debug_cov_vif.mon_cb.is_cebreak {
            bins active= {1'b1};
        }
         dbg_req : coverpoint cntxt.debug_cov_vif.mon_cb.debug_req_i {
            bins active= {1'b1};
        }
         step : coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[2] & !cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins active= {1'b1};
        }
        trig_vs_ebreak : cross tmatch, ebreak;
        trig_vs_cebreak : cross tmatch, cebreak;
        trig_vs_dbg_req : cross tmatch, dbg_req;
        trig_vs_step : cross tmatch, step;
        // Excluding trigger match to check 'lower' priority causes
        ebreak_vs_req : cross ebreak, dbg_req, tnomatch;
        cebreak_vs_req : cross cebreak, dbg_req, tnomatch;
        ebreak_vs_step : cross ebreak, step;
        cebreak_cs_step : cross cebreak, step;
        dbg_req_vs_step : cross dbg_req, step;
    endgroup

    covergroup cg_debug_with_f_inst;
        `per_instance_fcov
        dbg_req : coverpoint cntxt.debug_cov_vif.mon_cb.debug_req_i {
            bins dbg_req_active = {1'b1};
            bins dbg_req_0_to_1 = (0 => 1);
        }
        step : coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[2] & !cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins debug_step_mode_set = {1'b1};
        }
        ebreak: coverpoint cntxt.debug_cov_vif.mon_cb.is_ebreak {
                bins ebreak_ex = {1};
        }
        cebreak : coverpoint cntxt.debug_cov_vif.mon_cb.is_cebreak {
            bins cebreak_ex= {1'b1};
        }
        ebreakm_set: coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[15] {
                bins ebreakm_is_set = {1};
        }
        dm : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
                bins in_debug_mode = {1};
        }
        irq  : coverpoint |cntxt.debug_cov_vif.mon_cb.irq_i {
                bins irq_trans_0_to_1 = (1'b0 => 1'b1);
        }
        ill : coverpoint cntxt.debug_cov_vif.mon_cb.illegal_insn_i {
            bins ill_inst_hit = {1};
        }

        f_inst : coverpoint cntxt.debug_cov_vif.mon_cb.rvfi_insn {
            wildcard bins fadd = {cv32e40p_tracer_pkg::INSTR_FADD};
            wildcard bins fsub = {cv32e40p_tracer_pkg::INSTR_FSUB};
            wildcard bins fmul = {cv32e40p_tracer_pkg::INSTR_FMUL};
            wildcard bins fdiv = {cv32e40p_tracer_pkg::INSTR_FDIV};
            wildcard bins fsqrt = {cv32e40p_tracer_pkg::INSTR_FSQRT};
            wildcard bins fsgnjs = {cv32e40p_tracer_pkg::INSTR_FSGNJS};
            wildcard bins fsgnjns = {cv32e40p_tracer_pkg::INSTR_FSGNJNS};
            wildcard bins fsgnjxs = {cv32e40p_tracer_pkg::INSTR_FSGNJXS};
            wildcard bins fmin = {cv32e40p_tracer_pkg::INSTR_FMIN};
            wildcard bins fmax = {cv32e40p_tracer_pkg::INSTR_FMAX};
            wildcard bins fcvtws = {cv32e40p_tracer_pkg::INSTR_FCVTWS};
            wildcard bins fcvtwus = {cv32e40p_tracer_pkg::INSTR_FCVTWUS};
            wildcard bins fmvxs = {cv32e40p_tracer_pkg::INSTR_FMVXS};
            wildcard bins feqs = {cv32e40p_tracer_pkg::INSTR_FEQS};
            wildcard bins flts = {cv32e40p_tracer_pkg::INSTR_FLTS};
            wildcard bins fles = {cv32e40p_tracer_pkg::INSTR_FLES};
            wildcard bins fclass = {cv32e40p_tracer_pkg::INSTR_FCLASS};
            wildcard bins fcvtsw = {cv32e40p_tracer_pkg::INSTR_FCVTSW};
            wildcard bins fcvtswu = {cv32e40p_tracer_pkg::INSTR_FCVTSWU};
            wildcard bins fmvsw = {cv32e40p_tracer_pkg::INSTR_FMVSX};
            wildcard bins fmadd = {cv32e40p_tracer_pkg::INSTR_FMADD};
            wildcard bins fmsub = {cv32e40p_tracer_pkg::INSTR_FMSUB};
            wildcard bins fnmsub = {cv32e40p_tracer_pkg::INSTR_FNMSUB};
            wildcard bins fnmadd = {cv32e40p_tracer_pkg::INSTR_FNMADD};
        }

        rvfi_valid : coverpoint cntxt.debug_cov_vif.mon_cb.rvfi_valid {
            bins rvfi_valid = {1};
        }

        apu_req_valid : coverpoint cntxt.debug_cov_vif.mon_cb.apu_req {
            bins apu_req_valid = {1'b1};
        }

        apu_grant_valid : coverpoint cntxt.debug_cov_vif.mon_cb.apu_gnt {
            bins apu_gnt_valid[] = {1'b1};
        }

        apu_busy : coverpoint cntxt.debug_cov_vif.mon_cb.apu_busy {
            bins apu_busy[] = {1'b0, 1'b1};
            bins apu_busy_0_to_1 = (0 => 1);
            bins apu_busy_1_to_0 = (1 => 0);
        }

        dbg_x_finst : cross dbg_req, f_inst;

        step_x_finst : cross step, f_inst;

        f_inst_in_dbg_mode : cross dm, f_inst;

        //debug mode entry with debug_halt_req during multi cycle fp inst
        dbg_while_multi_cyc_f_A : cross apu_req_valid, apu_grant_valid, dbg_req;
        dbg_while_multi_cyc_f_B : cross apu_busy, dbg_req;

        //debug_halt_req with irq during multi cycle fp inst
        dbg_irq_while_multi_cyc_f_A : cross apu_req_valid, apu_grant_valid, dbg_req, irq;
        dbg_irq_while_multi_cyc_f_B : cross apu_busy, dbg_req, irq;

        //debug_halt_req with illegal instr during multi cycle fp inst
        dbg_ill_while_multi_cyc_f_A : cross apu_req_valid, apu_grant_valid, dbg_req, ill;
        dbg_ill_while_multi_cyc_f_B : cross apu_busy, dbg_req, ill;

        //debug mode entry with ebreak during multi cycle fp inst
        ebreak_while_multi_cyc_f_A : cross apu_req_valid, apu_grant_valid, ebreak, ebreakm_set;
        ebreak_while_multi_cyc_f_B : cross apu_busy, ebreak, ebreakm_set;

        //debug mode entry with cebreak during multi cycle fp inst
        cebreak_while_multi_cyc_f_A : cross apu_req_valid, apu_grant_valid, cebreak, ebreakm_set;
        cebreak_while_multi_cyc_f_B : cross apu_busy, cebreak, ebreakm_set;

    endgroup

    covergroup cg_debug_with_xpulp_inst;
        `per_instance_fcov
        dbg_req : coverpoint cntxt.debug_cov_vif.mon_cb.debug_req_i {
            bins dbg_req_active = {1'b1};
            bins dbg_req_0_to_1 = (0 => 1);
        }
        step : coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[2] & !cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins debug_step_mode_set = {1'b1};
        }
        dm : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
                bins in_debug_mode = {1};
        }

        xpulp_instruction : coverpoint cntxt.debug_cov_vif.mon_cb.rvfi_insn {
            wildcard bins cv_lb_pi_ri           =    {INSTR_CV_LB_PI_RI};
            wildcard bins cv_lh_pi_ri           =    {INSTR_CV_LH_PI_RI};
            wildcard bins cv_lw_pi_ri           =    {INSTR_CV_LW_PI_RI};
            wildcard bins cv_elw_pi_ri          =    {INSTR_CV_ELW_PI_RI};
            wildcard bins cv_lbu_pi_ri          =    {INSTR_CV_LBU_PI_RI};
            wildcard bins cv_lhu_pi_ri          =    {INSTR_CV_LHU_PI_RI};
            wildcard bins cv_beqimm             =    {INSTR_CV_BEQIMM};
            wildcard bins cv_bneimm             =    {INSTR_CV_BNEIMM};
            wildcard bins  cv_lb_pi_rr          =    {INSTR_CV_LB_PI_RR};
            wildcard bins  cv_lh_pi_rr          =    {INSTR_CV_LH_PI_RR};
            wildcard bins  cv_lw_pi_rr          =    {INSTR_CV_LW_PI_RR};
            wildcard bins  cv_lbu_pi_rr         =    {INSTR_CV_LBU_PI_RR};
            wildcard bins  cv_lhu_pi_rr         =    {INSTR_CV_LHU_PI_RR};
            wildcard bins  cv_lb_rr             =    {INSTR_CV_LB_RR};
            wildcard bins  cv_lh_rr             =    {INSTR_CV_LH_RR};
            wildcard bins  cv_lw_rr             =    {INSTR_CV_LW_RR};
            wildcard bins  cv_lbu_rr            =    {INSTR_CV_LBU_RR};
            wildcard bins  cv_lhu_rr            =    {INSTR_CV_LHU_RR};
            wildcard bins  cv_sb_pi_ri          =    {INSTR_CV_SB_PI_RI};
            wildcard bins  cv_sh_pi_ri          =    {INSTR_CV_SH_PI_RI};
            wildcard bins  cv_sw_pi_ri          =    {INSTR_CV_SW_PI_RI};
            wildcard bins  cv_sb_pi_rr          =    {INSTR_CV_SB_PI_RR};
            wildcard bins  cv_sh_pi_rr          =    {INSTR_CV_SH_PI_RR};
            wildcard bins  cv_sw_pi_rr          =    {INSTR_CV_SW_PI_RR};
            wildcard bins  cv_sb_rr             =    {INSTR_CV_SB_RR};
            wildcard bins  cv_sh_rr             =    {INSTR_CV_SH_RR};
            wildcard bins  cv_sw_rr             =    {INSTR_CV_SW_RR};
            wildcard bins  cv_starti            =    {INSTR_CV_STARTI};
            wildcard bins  cv_start             =    {INSTR_CV_START};
            wildcard bins  cv_endi              =    {INSTR_CV_ENDI};
            wildcard bins  cv_end               =    {INSTR_CV_END};
            wildcard bins  cv_counti            =    {INSTR_CV_COUNTI};
            wildcard bins  cv_count             =    {INSTR_CV_COUNT};
            wildcard bins  cv_setupi            =    {INSTR_CV_SETUPI};
            wildcard bins  cv_setup             =    {INSTR_CV_SETUP};
            wildcard bins  cv_extractr          =    {INSTR_CV_EXTRACTR};
            wildcard bins  cv_extractur         =    {INSTR_CV_EXTRACTUR};
            wildcard bins  cv_insertr           =    {INSTR_CV_INSERTR};
            wildcard bins  cv_bclrr             =    {INSTR_CV_BCLRR};
            wildcard bins  cv_bsetr             =    {INSTR_CV_BSETR};
            wildcard bins  cv_ror               =    {INSTR_CV_ROR};
            wildcard bins  cv_ff1               =    {INSTR_CV_FF1};
            wildcard bins  cv_fl1               =    {INSTR_CV_FL1};
            wildcard bins  cv_clb               =    {INSTR_CV_CLB};
            wildcard bins  cv_cnt               =    {INSTR_CV_CNT};
            wildcard bins  cv_abs               =    {INSTR_CV_ABS};
            wildcard bins  cv_slet              =    {INSTR_CV_SLET};
            wildcard bins  cv_sletu             =    {INSTR_CV_SLETU};
            wildcard bins  cv_min               =    {INSTR_CV_MIN};
            wildcard bins  cv_minu              =    {INSTR_CV_MINU};
            wildcard bins  cv_max               =    {INSTR_CV_MAX};
            wildcard bins  cv_maxu              =    {INSTR_CV_MAXU};
            wildcard bins  cv_exths             =    {INSTR_CV_EXTHS};
            wildcard bins  cv_exthz             =    {INSTR_CV_EXTHZ};
            wildcard bins  cv_extbs             =    {INSTR_CV_EXTBS};
            wildcard bins  cv_extbz             =    {INSTR_CV_EXTBZ};
            wildcard bins  cv_clip              =    {INSTR_CV_CLIP};
            wildcard bins  cv_clipu             =    {INSTR_CV_CLIPU};
            wildcard bins  cv_clipr             =    {INSTR_CV_CLIPR};
            wildcard bins  cv_clipur            =    {INSTR_CV_CLIPUR};
            wildcard bins  cv_addnr             =    {INSTR_CV_ADDNR};
            wildcard bins  cv_addunr            =    {INSTR_CV_ADDUNR};
            wildcard bins  cv_addrnr            =    {INSTR_CV_ADDRNR};
            wildcard bins  cv_addurnr           =    {INSTR_CV_ADDURNR};
            wildcard bins  cv_subnr             =    {INSTR_CV_SUBNR};
            wildcard bins  cv_subunr            =    {INSTR_CV_SUBUNR};
            wildcard bins  cv_subrnr            =    {INSTR_CV_SUBRNR};
            wildcard bins  cv_suburnr           =    {INSTR_CV_SUBURNR};
            wildcard bins  cv_mac               =    {INSTR_CV_MAC};
            wildcard bins  cv_msu               =    {INSTR_CV_MSU};
            wildcard bins  cv_extract           =    {INSTR_CV_EXTRACT};
            wildcard bins  cv_extractu          =    {INSTR_CV_EXTRACTU};
            wildcard bins  cv_insert            =    {INSTR_CV_INSERT};
            wildcard bins  cv_bclr              =    {INSTR_CV_BCLR};
            wildcard bins  cv_bset              =    {INSTR_CV_BSET};
            wildcard bins  cv_bitrev            =    {INSTR_CV_BITREV};
            wildcard bins  cv_addn              =    {INSTR_CV_ADDN};
            wildcard bins  cv_addun             =    {INSTR_CV_ADDUN};
            wildcard bins  cv_addrn             =    {INSTR_CV_ADDRN};
            wildcard bins  cv_addurn            =    {INSTR_CV_ADDURN};
            wildcard bins  cv_subn              =    {INSTR_CV_SUBN};
            wildcard bins  cv_subun             =    {INSTR_CV_SUBUN};
            wildcard bins  cv_subrn             =    {INSTR_CV_SUBRN};
            wildcard bins  cv_suburn            =    {INSTR_CV_SUBURN};
            wildcard bins  cv_mulsn             =    {INSTR_CV_MULSN};
            wildcard bins  cv_mulhhsn           =    {INSTR_CV_MULHHSN};
            wildcard bins  cv_mulsrn            =    {INSTR_CV_MULSRN};
            wildcard bins  cv_mulhhsrn          =    {INSTR_CV_MULHHSRN};
            wildcard bins  cv_mulun             =    {INSTR_CV_MULUN};
            wildcard bins  cv_mulhhun           =    {INSTR_CV_MULHHUN};
            wildcard bins  cv_mulurn            =    {INSTR_CV_MULURN};
            wildcard bins  cv_mulhhurn          =    {INSTR_CV_MULHHURN};
            wildcard bins  cv_macsn             =    {INSTR_CV_MACSN};
            wildcard bins  cv_machhsn           =    {INSTR_CV_MACHHSN};
            wildcard bins  cv_macsrn            =    {INSTR_CV_MACSRN};
            wildcard bins  cv_machhsrn          =    {INSTR_CV_MACHHSRN};
            wildcard bins  cv_macun             =    {INSTR_CV_MACUN};
            wildcard bins  cv_machhun           =    {INSTR_CV_MACHHUN};
            wildcard bins  cv_macurn            =    {INSTR_CV_MACURN};
            wildcard bins  cv_machhurn          =    {INSTR_CV_MACHHURN};
            wildcard bins  cv_add_h             =    {INSTR_CV_ADD_H};
            wildcard bins  cv_add_sc_h          =    {INSTR_CV_ADD_SC_H};
            wildcard bins  cv_add_sci_h         =    {INSTR_CV_ADD_SCI_H};
            wildcard bins  cv_add_b             =    {INSTR_CV_ADD_B};
            wildcard bins  cv_add_sc_b          =    {INSTR_CV_ADD_SC_B};
            wildcard bins  cv_add_sci_b         =    {INSTR_CV_ADD_SCI_B};
            wildcard bins  cv_sub_h             =    {INSTR_CV_SUB_H};
            wildcard bins  cv_sub_sc_h          =    {INSTR_CV_SUB_SC_H};
            wildcard bins  cv_sub_sci_h         =    {INSTR_CV_SUB_SCI_H};
            wildcard bins  cv_sub_b             =    {INSTR_CV_SUB_B};
            wildcard bins  cv_sub_sc_b          =    {INSTR_CV_SUB_SC_B};
            wildcard bins  cv_sub_sci_b         =    {INSTR_CV_SUB_SCI_B};
            wildcard bins  cv_avg_h             =    {INSTR_CV_AVG_H};
            wildcard bins  cv_avg_sc_h          =    {INSTR_CV_AVG_SC_H};
            wildcard bins  cv_avg_sci_h         =    {INSTR_CV_AVG_SCI_H};
            wildcard bins  cv_avg_b             =    {INSTR_CV_AVG_B};
            wildcard bins  cv_avg_sc_b          =    {INSTR_CV_AVG_SC_B};
            wildcard bins  cv_avg_sci_b         =    {INSTR_CV_AVG_SCI_B};
            wildcard bins  cv_avgu_h            =    {INSTR_CV_AVGU_H};
            wildcard bins  cv_avgu_sc_h         =    {INSTR_CV_AVGU_SC_H};
            wildcard bins  cv_avgu_sci_h        =    {INSTR_CV_AVGU_SCI_H};
            wildcard bins  cv_avgu_b            =    {INSTR_CV_AVGU_B};
            wildcard bins  cv_avgu_sc_b         =    {INSTR_CV_AVGU_SC_B};
            wildcard bins  cv_avgu_sci_b        =    {INSTR_CV_AVGU_SCI_B};
            wildcard bins  cv_min_h             =    {INSTR_CV_MIN_H};
            wildcard bins  cv_min_sc_h          =    {INSTR_CV_MIN_SC_H};
            wildcard bins  cv_min_sci_h         =    {INSTR_CV_MIN_SCI_H};
            wildcard bins  cv_min_b             =    {INSTR_CV_MIN_B};
            wildcard bins  cv_min_sc_b          =    {INSTR_CV_MIN_SC_B};
            wildcard bins  cv_min_sci_b         =    {INSTR_CV_MIN_SCI_B};
            wildcard bins  cv_minu_h            =    {INSTR_CV_MINU_H};
            wildcard bins  cv_minu_sc_h         =    {INSTR_CV_MINU_SC_H};
            wildcard bins  cv_minu_sci_h        =    {INSTR_CV_MINU_SCI_H};
            wildcard bins  cv_minu_b            =    {INSTR_CV_MINU_B};
            wildcard bins  cv_minu_sc_b         =    {INSTR_CV_MINU_SC_B};
            wildcard bins  cv_minu_sci_b        =    {INSTR_CV_MINU_SCI_B};
            wildcard bins  cv_max_h             =    {INSTR_CV_MAX_H};
            wildcard bins  cv_max_sc_h          =    {INSTR_CV_MAX_SC_H};
            wildcard bins  cv_max_sci_h         =    {INSTR_CV_MAX_SCI_H};
            wildcard bins  cv_max_b             =    {INSTR_CV_MAX_B};
            wildcard bins  cv_max_sc_b          =    {INSTR_CV_MAX_SC_B};
            wildcard bins  cv_max_sci_b         =    {INSTR_CV_MAX_SCI_B};
            wildcard bins  cv_maxu_h            =    {INSTR_CV_MAXU_H};
            wildcard bins  cv_maxu_sc_h         =    {INSTR_CV_MAXU_SC_H};
            wildcard bins  cv_maxu_sci_h        =    {INSTR_CV_MAXU_SCI_H};
            wildcard bins  cv_maxu_b            =    {INSTR_CV_MAXU_B};
            wildcard bins  cv_maxu_sc_b         =    {INSTR_CV_MAXU_SC_B};
            wildcard bins  cv_maxu_sci_b        =    {INSTR_CV_MAXU_SCI_B};
            wildcard bins  cv_srl_h             =    {INSTR_CV_SRL_H};
            wildcard bins  cv_srl_sc_h          =    {INSTR_CV_SRL_SC_H};
            wildcard bins  cv_srl_sci_h         =    {INSTR_CV_SRL_SCI_H};
            wildcard bins  cv_srl_b             =    {INSTR_CV_SRL_B};
            wildcard bins  cv_srl_sc_b          =    {INSTR_CV_SRL_SC_B};
            wildcard bins  cv_srl_sci_b         =    {INSTR_CV_SRL_SCI_B};
            wildcard bins  cv_sra_h             =    {INSTR_CV_SRA_H};
            wildcard bins  cv_sra_sc_h          =    {INSTR_CV_SRA_SC_H};
            wildcard bins  cv_sra_sci_h         =    {INSTR_CV_SRA_SCI_H};
            wildcard bins  cv_sra_b             =    {INSTR_CV_SRA_B};
            wildcard bins  cv_sra_sc_b          =    {INSTR_CV_SRA_SC_B};
            wildcard bins  cv_sra_sci_b         =    {INSTR_CV_SRA_SCI_B};
            wildcard bins  cv_sll_h             =    {INSTR_CV_SLL_H};
            wildcard bins  cv_sll_sc_h          =    {INSTR_CV_SLL_SC_H};
            wildcard bins  cv_sll_sci_h         =    {INSTR_CV_SLL_SCI_H};
            wildcard bins  cv_sll_b             =    {INSTR_CV_SLL_B};
            wildcard bins  cv_sll_sc_b          =    {INSTR_CV_SLL_SC_B};
            wildcard bins  cv_sll_sci_b         =    {INSTR_CV_SLL_SCI_B};
            wildcard bins  cv_or_h              =    {INSTR_CV_OR_H};
            wildcard bins  cv_or_sc_h           =    {INSTR_CV_OR_SC_H};
            wildcard bins  cv_or_sci_h          =    {INSTR_CV_OR_SCI_H};
            wildcard bins  cv_or_b              =    {INSTR_CV_OR_B};
            wildcard bins  cv_or_sc_b           =    {INSTR_CV_OR_SC_B};
            wildcard bins  cv_or_sci_b          =    {INSTR_CV_OR_SCI_B};
            wildcard bins  cv_xor_h             =    {INSTR_CV_XOR_H};
            wildcard bins  cv_xor_sc_h          =    {INSTR_CV_XOR_SC_H};
            wildcard bins  cv_xor_sci_h         =    {INSTR_CV_XOR_SCI_H};
            wildcard bins  cv_xor_b             =    {INSTR_CV_XOR_B};
            wildcard bins  cv_xor_sc_b          =    {INSTR_CV_XOR_SC_B};
            wildcard bins  cv_xor_sci_b         =    {INSTR_CV_XOR_SCI_B};
            wildcard bins  cv_and_h             =    {INSTR_CV_AND_H};
            wildcard bins  cv_and_sc_h          =    {INSTR_CV_AND_SC_H};
            wildcard bins  cv_and_sci_h         =    {INSTR_CV_AND_SCI_H};
            wildcard bins  cv_and_b             =    {INSTR_CV_AND_B};
            wildcard bins  cv_and_sc_b          =    {INSTR_CV_AND_SC_B};
            wildcard bins  cv_and_sci_b         =    {INSTR_CV_AND_SCI_B};
            wildcard bins  cv_abs_h             =    {INSTR_CV_ABS_H};
            wildcard bins  cv_abs_b             =    {INSTR_CV_ABS_B};
            wildcard bins  cv_dotup_h           =    {INSTR_CV_DOTUP_H};
            wildcard bins  cv_dotup_sc_h        =    {INSTR_CV_DOTUP_SC_H};
            wildcard bins  cv_dotup_sci_h       =    {INSTR_CV_DOTUP_SCI_H};
            wildcard bins  cv_dotup_b           =    {INSTR_CV_DOTUP_B};
            wildcard bins  cv_dotup_sc_b        =    {INSTR_CV_DOTUP_SC_B};
            wildcard bins  cv_dotup_sci_b       =    {INSTR_CV_DOTUP_SCI_B};
            wildcard bins  cv_dotusp_h          =    {INSTR_CV_DOTUSP_H};
            wildcard bins  cv_dotusp_sc_h       =    {INSTR_CV_DOTUSP_SC_H};
            wildcard bins  cv_dotusp_sci_h      =    {INSTR_CV_DOTUSP_SCI_H};
            wildcard bins  cv_dotusp_b          =    {INSTR_CV_DOTUSP_B};
            wildcard bins  cv_dotusp_sc_b       =    {INSTR_CV_DOTUSP_SC_B};
            wildcard bins  cv_dotusp_sci_b      =    {INSTR_CV_DOTUSP_SCI_B};
            wildcard bins  cv_dotsp_h           =    {INSTR_CV_DOTSP_H};
            wildcard bins  cv_dotsp_sc_h        =    {INSTR_CV_DOTSP_SC_H};
            wildcard bins  cv_dotsp_sci_h       =    {INSTR_CV_DOTSP_SCI_H};
            wildcard bins  cv_dotsp_b           =    {INSTR_CV_DOTSP_B};
            wildcard bins  cv_dotsp_sc_b        =    {INSTR_CV_DOTSP_SC_B};
            wildcard bins  cv_dotsp_sci_b       =    {INSTR_CV_DOTSP_SCI_B};
            wildcard bins  cv_sdotup_h          =    {INSTR_CV_SDOTUP_H};
            wildcard bins  cv_sdotup_sc_h       =    {INSTR_CV_SDOTUP_SC_H};
            wildcard bins  cv_sdotup_sci_h      =    {INSTR_CV_SDOTUP_SCI_H};
            wildcard bins  cv_sdotup_b          =    {INSTR_CV_SDOTUP_B};
            wildcard bins  cv_sdotup_sc_b       =    {INSTR_CV_SDOTUP_SC_B};
            wildcard bins  cv_sdotup_sci_b      =    {INSTR_CV_SDOTUP_SCI_B};
            wildcard bins  cv_sdotusp_h         =    {INSTR_CV_SDOTUSP_H};
            wildcard bins  cv_sdotusp_sc_h      =    {INSTR_CV_SDOTUSP_SC_H};
            wildcard bins  cv_sdotusp_sci_h     =    {INSTR_CV_SDOTUSP_SCI_H};
            wildcard bins  cv_sdotusp_b         =    {INSTR_CV_SDOTUSP_B};
            wildcard bins  cv_sdotusp_sc_b      =    {INSTR_CV_SDOTUSP_SC_B};
            wildcard bins  cv_sdotusp_sci_b     =    {INSTR_CV_SDOTUSP_SCI_B};
            wildcard bins  cv_sdotsp_h          =    {INSTR_CV_SDOTSP_H};
            wildcard bins  cv_sdotsp_sc_h       =    {INSTR_CV_SDOTSP_SC_H};
            wildcard bins  cv_sdotsp_sci_h      =    {INSTR_CV_SDOTSP_SCI_H};
            wildcard bins  cv_sdotsp_b          =    {INSTR_CV_SDOTSP_B};
            wildcard bins  cv_sdotsp_sc_b       =    {INSTR_CV_SDOTSP_SC_B};
            wildcard bins  cv_sdotsp_sci_b      =    {INSTR_CV_SDOTSP_SCI_B};
            wildcard bins  cv_extract_h         =    {INSTR_CV_EXTRACT_H};
            wildcard bins  cv_extract_b         =    {INSTR_CV_EXTRACT_B};
            wildcard bins  cv_extractu_h        =    {INSTR_CV_EXTRACTU_H};
            wildcard bins  cv_extractu_b        =    {INSTR_CV_EXTRACTU_B};
            wildcard bins  cv_insert_h          =    {INSTR_CV_INSERT_H};
            wildcard bins  cv_insert_b          =    {INSTR_CV_INSERT_B};
            wildcard bins  cv_shuffle_h         =    {INSTR_CV_SHUFFLE_H};
            wildcard bins  cv_shuffle_sci_h     =    {INSTR_CV_SHUFFLE_SCI_H};
            wildcard bins  cv_shuffle_b         =    {INSTR_CV_SHUFFLE_B};
            wildcard bins  cv_shufflei0_sci_b   =    {INSTR_CV_SHUFFLEI0_SCI_B};
            wildcard bins  cv_shufflei1_sci_b   =    {INSTR_CV_SHUFFLEI1_SCI_B};
            wildcard bins  cv_shufflei2_sci_b   =    {INSTR_CV_SHUFFLEI2_SCI_B};
            wildcard bins  cv_shufflei3_sci_b   =    {INSTR_CV_SHUFFLEI3_SCI_B};
            wildcard bins  cv_shuffle2_h        =    {INSTR_CV_SHUFFLE2_H};
            wildcard bins  cv_shuffle2_b        =    {INSTR_CV_SHUFFLE2_B};
            wildcard bins  cv_pack              =    {INSTR_CV_PACK};
            wildcard bins  cv_pack_h            =    {INSTR_CV_PACK_H};
            wildcard bins  cv_packhi_b          =    {INSTR_CV_PACKHI_B};
            wildcard bins  cv_packlo_b          =    {INSTR_CV_PACKLO_B};
            wildcard bins  cv_cmpeq_h           =    {INSTR_CV_CMPEQ_H};
            wildcard bins  cv_cmpeq_sc_h        =    {INSTR_CV_CMPEQ_SC_H};
            wildcard bins  cv_cmpeq_sci_h       =    {INSTR_CV_CMPEQ_SCI_H};
            wildcard bins  cv_cmpeq_b           =    {INSTR_CV_CMPEQ_B};
            wildcard bins  cv_cmpeq_sc_b        =    {INSTR_CV_CMPEQ_SC_B};
            wildcard bins  cv_cmpeq_sci_b       =    {INSTR_CV_CMPEQ_SCI_B};
            wildcard bins  cv_cmpne_h           =    {INSTR_CV_CMPNE_H};
            wildcard bins  cv_cmpne_sc_h        =    {INSTR_CV_CMPNE_SC_H};
            wildcard bins  cv_cmpne_sci_h       =    {INSTR_CV_CMPNE_SCI_H};
            wildcard bins  cv_cmpne_b           =    {INSTR_CV_CMPNE_B};
            wildcard bins  cv_cmpne_sc_b        =    {INSTR_CV_CMPNE_SC_B};
            wildcard bins  cv_cmpne_sci_b       =    {INSTR_CV_CMPNE_SCI_B};
            wildcard bins  cv_cmpgt_h           =    {INSTR_CV_CMPGT_H};
            wildcard bins  cv_cmpgt_sc_h        =    {INSTR_CV_CMPGT_SC_H};
            wildcard bins  cv_cmpgt_sci_h       =    {INSTR_CV_CMPGT_SCI_H};
            wildcard bins  cv_cmpgt_b           =    {INSTR_CV_CMPGT_B};
            wildcard bins  cv_cmpgt_sc_b        =    {INSTR_CV_CMPGT_SC_B};
            wildcard bins  cv_cmpgt_sci_b       =    {INSTR_CV_CMPGT_SCI_B};
            wildcard bins  cv_cmpge_h           =    {INSTR_CV_CMPGE_H};
            wildcard bins  cv_cmpge_sc_h        =    {INSTR_CV_CMPGE_SC_H};
            wildcard bins  cv_cmpge_sci_h       =    {INSTR_CV_CMPGE_SCI_H};
            wildcard bins  cv_cmpge_b           =    {INSTR_CV_CMPGE_B};
            wildcard bins  cv_cmpge_sc_b        =    {INSTR_CV_CMPGE_SC_B};
            wildcard bins  cv_cmpge_sci_b       =    {INSTR_CV_CMPGE_SCI_B};
            wildcard bins  cv_cmplt_h           =    {INSTR_CV_CMPLT_H};
            wildcard bins  cv_cmplt_sc_h        =    {INSTR_CV_CMPLT_SC_H};
            wildcard bins  cv_cmplt_sci_h       =    {INSTR_CV_CMPLT_SCI_H};
            wildcard bins  cv_cmplt_b           =    {INSTR_CV_CMPLT_B};
            wildcard bins  cv_cmplt_sc_b        =    {INSTR_CV_CMPLT_SC_B};
            wildcard bins  cv_cmplt_sci_b       =    {INSTR_CV_CMPLT_SCI_B};
            wildcard bins  cv_cmple_h           =    {INSTR_CV_CMPLE_H};
            wildcard bins  cv_cmple_sc_h        =    {INSTR_CV_CMPLE_SC_H};
            wildcard bins  cv_cmple_sci_h       =    {INSTR_CV_CMPLE_SCI_H};
            wildcard bins  cv_cmple_b           =    {INSTR_CV_CMPLE_B};
            wildcard bins  cv_cmple_sc_b        =    {INSTR_CV_CMPLE_SC_B};
            wildcard bins  cv_cmple_sci_b       =    {INSTR_CV_CMPLE_SCI_B};
            wildcard bins  cv_cmpgtu_h          =    {INSTR_CV_CMPGTU_H};
            wildcard bins  cv_cmpgtu_sc_h       =    {INSTR_CV_CMPGTU_SC_H};
            wildcard bins  cv_cmpgtu_sci_h      =    {INSTR_CV_CMPGTU_SCI_H};
            wildcard bins  cv_cmpgtu_b          =    {INSTR_CV_CMPGTU_B};
            wildcard bins  cv_cmpgtu_sc_b       =    {INSTR_CV_CMPGTU_SC_B};
            wildcard bins  cv_cmpgtu_sci_b      =    {INSTR_CV_CMPGTU_SCI_B};
            wildcard bins  cv_cmpgeu_h          =    {INSTR_CV_CMPGEU_H};
            wildcard bins  cv_cmpgeu_sc_h       =    {INSTR_CV_CMPGEU_SC_H};
            wildcard bins  cv_cmpgeu_sci_h      =    {INSTR_CV_CMPGEU_SCI_H};
            wildcard bins  cv_cmpgeu_b          =    {INSTR_CV_CMPGEU_B};
            wildcard bins  cv_cmpgeu_sc_b       =    {INSTR_CV_CMPGEU_SC_B};
            wildcard bins  cv_cmpgeu_sci_b      =    {INSTR_CV_CMPGEU_SCI_B};
            wildcard bins  cv_cmpltu_h          =    {INSTR_CV_CMPLTU_H};
            wildcard bins  cv_cmpltu_sc_h       =    {INSTR_CV_CMPLTU_SC_H};
            wildcard bins  cv_cmpltu_sci_h      =    {INSTR_CV_CMPLTU_SCI_H};
            wildcard bins  cv_cmpltu_b          =    {INSTR_CV_CMPLTU_B};
            wildcard bins  cv_cmpltu_sc_b       =    {INSTR_CV_CMPLTU_SC_B};
            wildcard bins  cv_cmpltu_sci_b      =    {INSTR_CV_CMPLTU_SCI_B};
            wildcard bins  cv_cmpleu_h          =    {INSTR_CV_CMPLEU_H};
            wildcard bins  cv_cmpleu_sc_h       =    {INSTR_CV_CMPLEU_SC_H};
            wildcard bins  cv_cmpleu_sci_h      =    {INSTR_CV_CMPLEU_SCI_H};
            wildcard bins  cv_cmpleu_b          =    {INSTR_CV_CMPLEU_B};
            wildcard bins  cv_cmpleu_sc_b       =    {INSTR_CV_CMPLEU_SC_B};
            wildcard bins  cv_cmpleu_sci_b      =    {INSTR_CV_CMPLEU_SCI_B};
            wildcard bins  cv_cplxmul_r         =    {INSTR_CV_CPLXMUL_R};
            wildcard bins  cv_cplxmul_r_div2    =    {INSTR_CV_CPLXMUL_R_DIV2};
            wildcard bins  cv_cplxmul_r_div4    =    {INSTR_CV_CPLXMUL_R_DIV4};
            wildcard bins  cv_cplxmul_r_div8    =    {INSTR_CV_CPLXMUL_R_DIV8};
            wildcard bins  cv_cplxmul_i         =    {INSTR_CV_CPLXMUL_I};
            wildcard bins  cv_cplxmul_i_div2    =    {INSTR_CV_CPLXMUL_I_DIV2};
            wildcard bins  cv_cplxmul_i_div4    =    {INSTR_CV_CPLXMUL_I_DIV4};
            wildcard bins  cv_cplxmul_i_div8    =    {INSTR_CV_CPLXMUL_I_DIV8};
            wildcard bins  cv_cplxconj          =    {INSTR_CV_CPLXCONJ};
            wildcard bins  cv_subrotmj          =    {INSTR_CV_SUBROTMJ};
            wildcard bins  cv_subrotmj_div2     =    {INSTR_CV_SUBROTMJ_DIV2};
            wildcard bins  cv_subrotmj_div4     =    {INSTR_CV_SUBROTMJ_DIV4};
            wildcard bins  cv_subrotmj_div8     =    {INSTR_CV_SUBROTMJ_DIV8};
            wildcard bins  cv_add_div2          =    {INSTR_CV_ADD_DIV2};
            wildcard bins  cv_add_div4          =    {INSTR_CV_ADD_DIV4};
            wildcard bins  cv_add_div8          =    {INSTR_CV_ADD_DIV8};
            wildcard bins  cv_sub_div2          =    {INSTR_CV_SUB_DIV2};
            wildcard bins  cv_sub_div4          =    {INSTR_CV_SUB_DIV4};
            wildcard bins  cv_sub_div8          =    {INSTR_CV_SUB_DIV8};
        }

        //cross xpulp instr while in debug mode
        xpulp_instructions_in_dbg_mode : cross dm, xpulp_instruction;

        //cross xpulp instr excution at debug req
        dbg_req_at_xpulp_instr : cross dbg_req, xpulp_instruction;

        //cross debug single stepping for each xpulp instr
        dbg_single_step_xpulp_instr : cross step, xpulp_instruction;

    endgroup

endclass : uvme_debug_covg

function uvme_debug_covg::new(string name = "debug_covg", uvm_component parent = null);
    super.new(name, parent);

    cg_debug_mode_ext = new();
    cg_ebreak_execute_with_ebreakm = new();
    cg_cebreak_execute_with_ebreakm = new();
    cg_ebreak_execute_without_ebreakm = new();
    cg_cebreak_execute_without_ebreakm = new();
    cg_trigger_match = new();
    cg_trigger_match_disabled = new();
    cg_debug_mode_exception = new();
    cg_debug_mode_ecall = new();
    cg_irq_in_debug = new();
    cg_wfi_in_debug = new();
    cg_wfi_debug_req = new();
    cg_single_step = new();
    cg_mmode_dret = new();
    cg_irq_dreq = new();
    cg_debug_regs_d_mode = new();
    cg_debug_regs_m_mode = new();
    cg_trigger_regs = new();
    cg_counters_enabled = new();
    cg_debug_at_reset = new();
    cg_fence_in_debug = new();
    cg_debug_causes = new();
    cg_debug_with_f_inst = new();
    cg_debug_with_xpulp_inst = new();
endfunction : new

function void uvme_debug_covg::build_phase(uvm_phase phase);
    super.build_phase(phase);

    void'(uvm_config_db#(uvme_cv32e40p_cntxt_c)::get(this, "", "cntxt", cntxt));
    if (cntxt == null) begin
        `uvm_fatal("DEBUGCOVG", "No cntxt object passed to model");
    end
endfunction : build_phase

task uvme_debug_covg::run_phase(uvm_phase phase);
    super.run_phase(phase);

    `uvm_info("DEBUGCOVG", "The debug coverage model is running", UVM_LOW);

    fork
        sample_debug_req_i();
        sample_clk_i();
    join_none
endtask : run_phase

task uvme_debug_covg::sample_debug_req_i();
  while(1) begin
    @(posedge cntxt.debug_cov_vif.mon_cb.debug_req_i);

    cg_debug_mode_ext.sample();
  end
endtask : sample_debug_req_i

task uvme_debug_covg::sample_clk_i();
  while (1) begin
    @(cntxt.debug_cov_vif.mon_cb);

    cg_ebreak_execute_with_ebreakm.sample();
    cg_cebreak_execute_with_ebreakm.sample();
    cg_ebreak_execute_without_ebreakm.sample();
    cg_cebreak_execute_without_ebreakm.sample();
    cg_trigger_match.sample();
    cg_trigger_match_disabled.sample();
    cg_debug_mode_exception.sample();
    cg_debug_mode_ecall.sample();
    cg_irq_in_debug.sample();
    cg_wfi_in_debug.sample();
    cg_wfi_debug_req.sample();
    cg_single_step.sample();
    cg_mmode_dret.sample();
    cg_irq_dreq.sample();
    cg_debug_regs_d_mode.sample();
    cg_debug_regs_m_mode.sample();
    cg_trigger_regs.sample();
    cg_counters_enabled.sample();
    cg_debug_at_reset.sample();
    cg_fence_in_debug.sample();
    cg_debug_causes.sample();
    cg_debug_with_f_inst.sample();
    cg_debug_with_xpulp_inst.sample();
  end
endtask  : sample_clk_i
