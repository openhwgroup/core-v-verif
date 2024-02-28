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
        irq_dreq_trig_ill : cross dreq, irq, trigger, ill; // irq + haltreq + trigger (illegal)
        irq_dreq_trig_cebreak : cross dreq, irq, trigger, cebreak; // irq + haltreq + trigger (cbreak)
        irq_dreq_trig_ebreak : cross dreq, irq, trigger, ebreak; // irq + haltreq + trigger (ebreak)
        irq_dreq_trig_branch : cross dreq, irq, trigger, branch; // irq + haltreq + trigger (branch)
        irq_dreq_trig_multicycle : cross dreq, irq, trigger, mulhsu; // irq + haltreq + trigger (mc)
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

    covergroup cg_debug_with_rv32f_inst;
        `per_instance_fcov

        cp_dbg_req : coverpoint cntxt.debug_cov_vif.mon_cb.debug_req_i & !cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins dbg_req_active = {1'b1};
            bins dbg_req_0_to_1 = (0 => 1);
        }

        cp_step : coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[2] & !cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins dbg_step_mode_set = {1'b1};
            bins dbg_step_mode_not_set = {1'b0};
        }

        cp_ebreak: coverpoint cntxt.debug_cov_vif.mon_cb.is_ebreak {
                bins ebreak_ex = {1};
        }

        cp_cebreak : coverpoint cntxt.debug_cov_vif.mon_cb.is_cebreak {
            bins cebreak_ex= {1'b1};
        }

        cp_ebreakm_set: coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[15] {
                bins ebreakm_is_set = {1};
        }

        cp_trigger_match : coverpoint cntxt.debug_cov_vif.mon_cb.trigger_match_i {
            bins not_match = {0};
            bins match = {1};
        }

        cp_trigger_en : coverpoint cntxt.debug_cov_vif.mon_cb.tdata1[2] {
            bins trig_en = {1};
        }

        cp_dm : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
                bins in_debug_mode = {1};
        }

        cp_irq  : coverpoint (cntxt.debug_cov_vif.mon_cb.irq_i & cntxt.debug_cov_vif.mon_cb.mie_q) {
                wildcard bins irq_31_trans_0_to_1    =   ( {1'b0,31'b?}                 =>  {1'b1,31'b?} );
                wildcard bins irq_30_trans_0_to_1    =   ( {1'b0,1'b0,30'b?}            =>  {1'b0,1'b1,30'b?} );
                wildcard bins irq_29_trans_0_to_1    =   ( {2'b0,1'b0,29'b?}            =>  {2'b0,1'b1,29'b?} );
                wildcard bins irq_28_trans_0_to_1    =   ( {3'b0,1'b0,28'b?}            =>  {3'b0,1'b1,28'b?} );
                wildcard bins irq_27_trans_0_to_1    =   ( {4'b0,1'b0,27'b?}            =>  {4'b0,1'b1,27'b?} );
                wildcard bins irq_26_trans_0_to_1    =   ( {5'b0,1'b0,26'b?}            =>  {5'b0,1'b1,26'b?} );
                wildcard bins irq_25_trans_0_to_1    =   ( {6'b0,1'b0,25'b?}            =>  {6'b0,1'b1,25'b?} );
                wildcard bins irq_24_trans_0_to_1    =   ( {7'b0,1'b0,24'b?}            =>  {7'b0,1'b1,24'b?} );
                wildcard bins irq_23_trans_0_to_1    =   ( {8'b0,1'b0,23'b?}            =>  {8'b0,1'b1,23'b?} );
                wildcard bins irq_22_trans_0_to_1    =   ( {9'b0,1'b0,22'b?}            =>  {9'b0,1'b1,22'b?} );
                wildcard bins irq_21_trans_0_to_1    =   ( {10'b0,1'b0,21'b?}           =>  {10'b0,1'b1,21'b?} );
                wildcard bins irq_20_trans_0_to_1    =   ( {11'b0,1'b0,20'b?}           =>  {11'b0,1'b1,20'b?} );
                wildcard bins irq_19_trans_0_to_1    =   ( {12'b0,1'b0,19'b?}           =>  {12'b0,1'b1,19'b?} );
                wildcard bins irq_18_trans_0_to_1    =   ( {13'b0,1'b0,18'b?}           =>  {13'b0,1'b1,18'b?} );
                wildcard bins irq_17_trans_0_to_1    =   ( {14'b0,1'b0,17'b?}           =>  {14'b0,1'b1,17'b?} );
                wildcard bins irq_16_trans_0_to_1    =   ( {15'b0,1'b0,16'b?}           =>  {15'b0,1'b1,16'b?} );
                wildcard bins irq_11_trans_0_to_1    =   ( {20'b0,1'b0,11'b?}           =>  {20'b0,1'b1,11'b?} );
                wildcard bins irq_3_trans_0_to_1     =   ( {24'b0,1'b0,3'b?,1'b0,3'b?}  =>  {24'b0,1'b?,3'b?,1'b1,3'b?} );
                wildcard bins irq_7_trans_0_to_1     =   ( {24'b0,1'b0,3'b?,1'b0,3'b?}  =>  {24'b0,1'b1,3'b?,1'b0,3'b?} );
        }

        cp_ill : coverpoint cntxt.debug_cov_vif.mon_cb.illegal_insn_i {
            bins ill_inst_hit = {1};
        }

        cp_rv32f_inst : coverpoint cntxt.debug_cov_vif.mon_cb.id_stage_instr_rdata_i iff (cntxt.debug_cov_vif.mon_cb.id_stage_instr_valid_i == 1) {
            `RV32F_INSTR_BINS
        }

        cp_apu_req_valid : coverpoint cntxt.debug_cov_vif.mon_cb.apu_req {
            bins apu_req_valid = {1'b1};
        }

        cp_apu_grant_valid : coverpoint cntxt.debug_cov_vif.mon_cb.apu_gnt {
            bins apu_gnt_valid[] = {1'b1};
        }

        cp_apu_busy : coverpoint cntxt.debug_cov_vif.mon_cb.apu_busy {
            bins apu_busy[] = {1'b0, 1'b1};
            bins apu_busy_0_to_1 = (0 => 1);
            bins apu_busy_1_to_0 = (1 => 0);
        }

        // cross rv32f instr execution at debug req only - no trigger
        cr_dbg_x_rv32f : cross cp_dbg_req, cp_rv32f_inst, cp_trigger_match {
            ignore_bins no_trigger_match = binsof(cp_trigger_match) intersect {1};
        }

        // cross debug single stepping for each rv32f instr - no trigger
        cr_step_x_rv32f : cross cp_step, cp_rv32f_inst, cp_trigger_match {
            ignore_bins single_step_disable = binsof(cp_step) intersect {0};
            ignore_bins no_trigger_match = binsof(cp_trigger_match) intersect {1};
        }

        // cross debug entry with trigger addr match at rv32f inst
        cr_trigger_with_rv32f : cross cp_trigger_match, cp_trigger_en, cp_rv32f_inst;

        cr_rv32f_in_dbg_mode : cross cp_dm, cp_rv32f_inst;

        // debug mode entry with debug_halt_req during multi cycle fp inst
        cr_dbg_while_multi_cyc_f_A : cross cp_apu_req_valid, cp_apu_grant_valid, cp_dbg_req;
        cr_dbg_while_multi_cyc_f_B : cross cp_apu_busy, cp_dbg_req;

        // debug_halt_req with irq during multi cycle fp inst
        cr_dbg_irq_while_multi_cyc_f_A : cross cp_apu_req_valid, cp_apu_grant_valid, cp_dbg_req, cp_irq {
          bins irq_grp_upper16_multi_cyc_f_A = binsof(cp_dbg_req.dbg_req_active) && binsof(cp_apu_grant_valid) && (
                                 binsof(cp_irq.irq_31_trans_0_to_1) || binsof(cp_irq.irq_30_trans_0_to_1) ||
                                 binsof(cp_irq.irq_29_trans_0_to_1) || binsof(cp_irq.irq_28_trans_0_to_1) ||
                                 binsof(cp_irq.irq_27_trans_0_to_1) || binsof(cp_irq.irq_26_trans_0_to_1) ||
                                 binsof(cp_irq.irq_25_trans_0_to_1) || binsof(cp_irq.irq_24_trans_0_to_1) ||
                                 binsof(cp_irq.irq_23_trans_0_to_1) || binsof(cp_irq.irq_22_trans_0_to_1) ||
                                 binsof(cp_irq.irq_21_trans_0_to_1) || binsof(cp_irq.irq_20_trans_0_to_1) ||
                                 binsof(cp_irq.irq_19_trans_0_to_1) || binsof(cp_irq.irq_18_trans_0_to_1) ||
                                 binsof(cp_irq.irq_17_trans_0_to_1) || binsof(cp_irq.irq_16_trans_0_to_1));
          bins irq_grp_lower16_multi_cyc_f_A = binsof(cp_dbg_req.dbg_req_active) && binsof(cp_apu_grant_valid) && (
                                 binsof(cp_irq.irq_11_trans_0_to_1) || 
                                 binsof(cp_irq.irq_3_trans_0_to_1)  ||
                                 binsof(cp_irq.irq_7_trans_0_to_1));
          ignore_bins dbg_req_others = binsof(cp_dbg_req.dbg_req_0_to_1);
        }
        cr_dbg_irq_while_multi_cyc_f_B : cross cp_apu_busy, cp_dbg_req, cp_irq {
          bins irq_grp_upper16_multi_cyc_f_B = binsof(cp_dbg_req.dbg_req_active) && (binsof(cp_apu_busy.apu_busy) intersect {1}) && (
                                 binsof(cp_irq.irq_31_trans_0_to_1) || binsof(cp_irq.irq_30_trans_0_to_1) ||
                                 binsof(cp_irq.irq_29_trans_0_to_1) || binsof(cp_irq.irq_28_trans_0_to_1) ||
                                 binsof(cp_irq.irq_27_trans_0_to_1) || binsof(cp_irq.irq_26_trans_0_to_1) ||
                                 binsof(cp_irq.irq_25_trans_0_to_1) || binsof(cp_irq.irq_24_trans_0_to_1) ||
                                 binsof(cp_irq.irq_23_trans_0_to_1) || binsof(cp_irq.irq_22_trans_0_to_1) ||
                                 binsof(cp_irq.irq_21_trans_0_to_1) || binsof(cp_irq.irq_20_trans_0_to_1) ||
                                 binsof(cp_irq.irq_19_trans_0_to_1) || binsof(cp_irq.irq_18_trans_0_to_1) ||
                                 binsof(cp_irq.irq_17_trans_0_to_1) || binsof(cp_irq.irq_16_trans_0_to_1));
          bins irq_grp_lower16_multi_cyc_f_B = binsof(cp_dbg_req.dbg_req_active) && (binsof(cp_apu_busy.apu_busy) intersect {1}) && (
                                 binsof(cp_irq.irq_11_trans_0_to_1) || 
                                 binsof(cp_irq.irq_3_trans_0_to_1) ||
                                 binsof(cp_irq.irq_7_trans_0_to_1));
          ignore_bins dbg_apu_busy_others = (binsof(cp_apu_busy.apu_busy) intersect {0}) || binsof(cp_apu_busy.apu_busy_0_to_1) || binsof(cp_apu_busy.apu_busy_1_to_0);
          ignore_bins dbg_req_others = binsof(cp_dbg_req.dbg_req_0_to_1);
        }

        // debug_halt_req with illegal instr during multi cycle fp inst
        cr_dbg_ill_while_multi_cyc_f_A : cross cp_apu_req_valid, cp_apu_grant_valid, cp_dbg_req, cp_ill;
        cr_dbg_ill_while_multi_cyc_f_B : cross cp_apu_busy, cp_dbg_req, cp_ill;

        // debug mode entry with ebreak during multi cycle fp inst
        cr_ebreak_while_multi_cyc_f_A : cross cp_apu_req_valid, cp_apu_grant_valid, cp_ebreak, cp_ebreakm_set;
        cr_ebreak_while_multi_cyc_f_B : cross cp_apu_busy, cp_ebreak, cp_ebreakm_set;

        // debug mode entry with cebreak during multi cycle fp inst
        cr_cebreak_while_multi_cyc_f_A : cross cp_apu_req_valid, cp_apu_grant_valid, cp_cebreak, cp_ebreakm_set;
        cr_cebreak_while_multi_cyc_f_B : cross cp_apu_busy, cp_cebreak, cp_ebreakm_set;

        // debug mode entry with trigger during multi cycle fp inst
        cr_dbg_trig_while_multi_cyc_f_A : cross cp_apu_req_valid, cp_apu_grant_valid, cp_trigger_match, cp_trigger_en;
        cr_dbg_trig_while_multi_cyc_f_B : cross cp_apu_busy, cp_trigger_match, cp_trigger_en;

    endgroup

    covergroup cg_debug_with_xpulp_inst;
        `per_instance_fcov

        cp_dbg_req : coverpoint cntxt.debug_cov_vif.mon_cb.debug_req_i & !cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins dbg_req_active = {1'b1};
            bins dbg_req_0_to_1 = (0 => 1);
        }

        cp_step : coverpoint cntxt.debug_cov_vif.mon_cb.dcsr_q[2] & !cntxt.debug_cov_vif.mon_cb.debug_mode_q {
            bins dbg_step_mode_set = {1'b1};
            bins dbg_step_mode_not_set = {1'b0};
        }

        cp_trigger_match : coverpoint cntxt.debug_cov_vif.mon_cb.trigger_match_i {
            bins not_match = {0};
            bins match = {1};
        }

        cp_trigger_en : coverpoint cntxt.debug_cov_vif.mon_cb.tdata1[2] {
            bins trig_en = {1};
        }

        cp_dm : coverpoint cntxt.debug_cov_vif.mon_cb.debug_mode_q {
                bins in_debug_mode = {1};
        }

        cp_xpulp_instr : coverpoint cntxt.debug_cov_vif.mon_cb.id_stage_instr_rdata_i iff (cntxt.debug_cov_vif.mon_cb.id_stage_instr_valid_i == 1) {
            `RV32X_PULP_INSTR_BINS
        }

        // cross xpulp instr while in debug mode
        cr_xpulp_instructions_in_dbg_mode : cross cp_dm, cp_xpulp_instr;

        // cross xpulp instr execution at debug req only - no trigger
        cr_dbg_req_at_xpulp_instr : cross cp_dbg_req, cp_xpulp_instr, cp_trigger_match {
            ignore_bins no_trigger_match = binsof(cp_trigger_match) intersect {1};
        }

        // cross debug single stepping for each xpulp instr - no trigger
        cr_dbg_single_step_xpulp_instr : cross cp_step, cp_xpulp_instr, cp_trigger_match {
            ignore_bins single_step_disable = binsof(cp_step) intersect {0};
            ignore_bins no_trigger_match = binsof(cp_trigger_match) intersect {1};
        }

        // cross debug entry with trigger addr match at xpulp inst
        cr_trigger_with_xpulp_instr : cross cp_trigger_match, cp_trigger_en, cp_xpulp_instr;

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
    cg_debug_with_rv32f_inst = new();
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
    cg_debug_with_rv32f_inst.sample();
    cg_debug_with_xpulp_inst.sample();
  end
endtask  : sample_clk_i
