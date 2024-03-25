///////////////////////////////////////////////////////////////////////////////
// Copyright 2023 OpenHW Group
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

class uvme_cv32e40p_fp_instr_covg extends uvm_component;
    /*
    * Class members
    */
    uvme_cv32e40p_cfg_c    cfg;
    uvme_cv32e40p_cntxt_c  cntxt;

    `uvm_component_utils_begin(uvme_cv32e40p_fp_instr_covg)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
    `uvm_component_utils_end

    extern function new(string name = "cv32e40p_fp_instr_covg", uvm_component parent = null);
    extern function void build_phase(uvm_phase phase);
    extern task run_phase(uvm_phase phase);
    extern task sample_clk_i();

    `include "uvme_cv32e40p_cov_model_macros.sv"

    `define FPU_MULTICYCLE_WINDOW_ILLEGAL_CASES \
     illegal_bins clk_2_19_group_NON_DIVSQRT  = ( (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1}) ) \
                                                   with ( (cp_f_multicycle_clk_window != 0) & (fpu_latency == 0) ); \
     illegal_bins clk_3_19_group_NON_DIVSQRT  = ( (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2}) ) \
                                                   with ( (cp_f_multicycle_clk_window != 0) & (fpu_latency == 1) ); \
     illegal_bins clk_4_19_group_NON_DIVSQRT  = ( (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2, 3}) ) \
                                                   with ( (cp_f_multicycle_clk_window != 0) & (fpu_latency == 2) );

    `define FPU_ZERO_LATENCY_ILLEGAL_BUSY \
     illegal_bins apu_busy_curr_apu_op_not_div_sqrt = ( !binsof(cp_curr_fpu_apu_op_multicycle) intersect {APU_OP_FDIV, APU_OP_FSQRT} ) \
                                                      with ( ((cp_curr_fpu_apu_op_multicycle + 1) * (fpu_latency == 0)) != 0 );

    `define IGNORE_BINS_NON_FD_F_INSTR \
     ignore_bins non_fd_f_inst = binsof(cp_curr_fpu_apu_op) intersect {`APU_INSTR_WITH_NO_FD};

    `define IGNORE_BINS_ZERO_LAT_FPU_OP \
     ignore_bins zero_lat_inst = ( !binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT} ) \
                                 with ( ((cp_curr_fpu_apu_op + 1) * (fpu_latency == 0)) != 0 );

    `define IGNORE_BINS_CONTENTION_IN_LSU_WITH_APU \
     ignore_bins in_contention_lsu_wr = ( binsof(cp_apu_contention) intersect {1} ) \
                                        with ( ((cp_curr_fpu_apu_op + 1) * (fpu_latency == 1)) != 0 );

    `define IGNORE_BINS_NON_FS1_F_INSTR \
     ignore_bins non_fs3_f_inst = !binsof(cp_id_stage_f_inst) intersect {`RV32F_INSTR_WITH_FS1};

    `define IGNORE_BINS_NON_FS2_F_INSTR \
     ignore_bins non_fs3_f_inst = !binsof(cp_id_stage_f_inst) intersect {`RV32F_INSTR_WITH_FS2};

    `define IGNORE_BINS_NON_FS3_F_INSTR \
     ignore_bins non_fs3_f_inst = !binsof(cp_id_stage_f_inst) intersect {`RV32F_INSTR_WITH_FS3};

    `define IGNORE_BINS_NON_RD_F_INSTR \
     ignore_bins non_rd_f_inst = !binsof(cp_curr_fpu_apu_op) intersect {`APU_INSTR_WITH_NO_FD};

    `define IGNORE_BINS_PREV_NON_FPU_OPCODE_WO_RD \
     ignore_bins prev_non_fpu_wo_rd = !binsof(cp_prev_is_non_fpu_opcode) intersect {`RV32_OPCODE_LIST1_WITH_RD};

    `define IGNORE_BINS_CUR_FPU_OPCODE_WO_RS1 \
     ignore_bins cur_fpu_wo_rs1 = !binsof(cp_cur_is_fpu_instr) intersect {`RV32F_INSTR_WITH_RS1};

    `define IGNORE_BINS_NON_RS1_F_INSTR_IN_ID \
     ignore_bins non_rs_id_stage_f_inst = !binsof(cp_id_stage_f_inst) intersect {`RV32F_INSTR_WITH_RS1};

    `define IGNORE_BINS_NON_RS1_CV32E40P_INSTR \
     ignore_bins non_rs1_rv32_instr = binsof(cp_id_stage_non_rv32fc_inst) intersect {TB_OPCODE_LUI,TB_OPCODE_AUIPC,TB_OPCODE_JAL};

    `define IGNORE_BINS_NON_RS2_CV32E40P_INSTR \
     ignore_bins non_rs2_rv32_instr = binsof(cp_id_stage_non_rv32fc_inst) intersect {`RV32_OPCODE_WITH_NO_RS2};

    `define IGNORE_BINS_NON_STALLED_CONTENTION_WR_STATE \
     ignore_bins non_stalled_contention_wr_state = binsof(cp_contention_state) intersect {0,1};

    `define IGNORE_BINS_NON_FD_F_INSTR_AT_CONTENTION \
     ignore_bins non_fd_f_inst = binsof(cp_last_fpu_apu_op_at_contention) intersect {`APU_INSTR_WITH_NO_FD};

    `define IGNORE_BINS_CONTENTION_AT_LSU_REGFILE_WR \
     ignore_bins contention_at_lsu_wr = binsof(cp_apu_contention) intersect {1};

    `define IGNORE_BINS_NON_RD_F_INSTR_AT_CONTENTION \
     ignore_bins non_rd_f_inst = !binsof(cp_last_fpu_apu_op_at_contention) intersect {`APU_INSTR_WITH_NO_FD};

    `define IGNORE_BINS_NO_CONTENTION \
     ignore_bins no_contention = binsof(cp_apu_contention) intersect {1};

    `define IGNORE_BINS_NO_CONTENTION_LSU \
     ignore_bins no_contention_lsu_wr = binsof(cp_apu_contention) intersect {0};

    /*
    * Covergroups
    */

    covergroup cg_f_multicycle(int fpu_latency);
        `per_instance_fcov
        // option.at_least = 10; // this affect ccp as well and some ccp have large cross numbers

        cp_id_stage_f_inst : coverpoint `COVIF_CB.id_stage_instr_rdata_i iff (`COVIF_CB.id_stage_instr_valid_i == 1) {
            `RV32F_INSTR_BINS
            option.weight = 5;
        }

        cp_id_stage_apu_op_ex_o : coverpoint `COVIF_CB.id_stage_apu_op_ex_o iff (`COVIF_CB.id_stage_apu_en_ex_o == 1) {
            `FPU_OP_BINS
            option.weight = 5;
        }

        // from bhv_logic_1
        cp_f_multicycle_clk_window : coverpoint cntxt.cov_vif.if_clk_cycle_window iff ((`COVIF_CB.is_mulh_ex == 0) &&
                                                                                       (`COVIF_CB.is_misaligned_data_req_ex == 0) &&
                                                                                       (`COVIF_CB.is_post_inc_ld_st_inst_ex == 0) &&
                                                                                       (`COVIF_CB.ex_apu_valid_memorised == 0)) {
            bins clk1 = {1};
            bins clk2 = {2};
            bins clk3 = {3};
            bins clk4 = {4};
            bins clk5 = {5};
            bins clk6 = {6};
            bins clk7 = {7};
            bins clk8 = {8};
            bins clk9 = {9};
            bins clk10 = {10};
            bins clk11 = {11};
            bins clk12 = {12};
            bins clk13 = {13};
            bins clk14 = {14};
            bins clk15 = {15};
            bins clk16 = {16};
            bins clk17 = {17};
            bins clk18 = {18};
            bins clk19 = {19};
            ignore_bins ignore_idle = {0};
            illegal_bins clk_more_than_19 = {[20:31]};
        }

        cp_id_stage_inst_valid : coverpoint `COVIF_CB.id_stage_instr_valid_i {
            bins id_stage_instr_valid = {1};
        }

        cp_id_stage_apu_en_ex_o : coverpoint `COVIF_CB.id_stage_apu_en_ex_o {
            bins id_stage_apu_en_ex_1 = {1};
            bins id_stage_apu_en_ex_0_to_1 = (0 => 1);
        }

        cp_apu_req_valid : coverpoint `COVIF_CB.apu_req {
            bins apu_req_valid = {1'b1};
        }

        cp_apu_grant_valid : coverpoint `COVIF_CB.apu_gnt {
            bins apu_gnt_valid = {1'b1};
        }

        cp_apu_busy : coverpoint `COVIF_CB.apu_busy {
            bins apu_busy_high = {1'b1};
        }

        // from bhv_logic_1
        cp_curr_fpu_apu_op : coverpoint cntxt.cov_vif.o_curr_fpu_apu_op_if {
            `FPU_OP_BINS
            option.weight = 5;
        }

        // from bhv_logic_1
        cp_curr_fpu_apu_op_at_apu_req : coverpoint cntxt.cov_vif.o_curr_fpu_apu_op_if iff ( (`COVIF_CB.apu_req == 1) &&
                                                                                            (`COVIF_CB.apu_gnt == 1) )
        {
            `FPU_OP_BINS
            option.weight = 5;
        }

        // from bhv_logic_1
        cp_curr_fpu_apu_op_multicycle : coverpoint cntxt.cov_vif.o_curr_fpu_apu_op_if iff (`COVIF_CB.apu_busy == 1)
        {
            `FPU_OP_BINS
            ignore_bins cfg_0cyclat_insns = {`RV32F_OP_WITHOUT_FDIV_FSQRT} with ((item >= 0) && (fpu_latency == 0));
            option.weight = 5;
        }

        cp_fpu_lat_0_and_2_ex_regfile_alu_wr_no_stall : coverpoint ((`COVIF_CB.is_mulh_ex == 0) &&
                                                                    (`COVIF_CB.is_misaligned_data_req_ex == 0) &&
                                                                    (`COVIF_CB.is_post_inc_ld_st_inst_ex == 0) &&
                                                                    (`COVIF_CB.ex_apu_valid_memorised == 0)) {

            bins no_alu_wr_stall = {1};
        }

        // cross coverage for F-inst in ID-stage with preceeding F-multicycle instr
        cr_f_inst_at_id_stage_inp_with_fpu_multicycle_req : cross cp_id_stage_f_inst,
                                                                  cp_curr_fpu_apu_op_at_apu_req {
            option.weight = 5;
        }

        // cross coverage for F-inst in ID-stage with preceeding F-multicycle
        // case with apu_busy or APU needing more than 1 clock cycle 
        cr_f_inst_at_id_stage_inp_while_fpu_busy : cross cp_id_stage_f_inst,
                                                         cp_curr_fpu_apu_op_multicycle {
            option.weight = 5;
            // For FPU config with Latency=0 , apu_busy is expected to be set only for FDIV and FSQRT case
            `FPU_ZERO_LATENCY_ILLEGAL_BUSY
        }

        // cross coverage for F-inst arriving at ID-stage input at various stages of APU latency
        // clk-cycles of the ongoing/preceeding F-multicycle instr
        cr_f_inst_at_id_stage_inp_with_cyc_window_of_ongoing_fpu_calc : cross cp_id_stage_f_inst,
                                                                              cp_f_multicycle_clk_window,
                                                                              cp_curr_fpu_apu_op,
                                                                              cp_fpu_lat_0_and_2_ex_regfile_alu_wr_no_stall {
            option.weight = 5;
            `FPU_MULTICYCLE_WINDOW_ILLEGAL_CASES
        }

        // cross coverage for F-inst at ID-stage output with preceeding F-multicycle instr
        // Note: Added 2 separate similar cross coverages ID stage because of different
        // arrival times of next instruction w.r.t APU Req
        //cr_f_inst_at_id_stage_out_with_fpu_multicycle_req : cross cp_id_stage_apu_op_ex_o,
        //                                                          cp_curr_fpu_apu_op_at_apu_req
        //{option.weight = 5;}

        // cross coverage for F-inst at ID-stage output with preceeding F-multicycle
        // case with apu_busy or APU needing more than 1 clock cycle 
        // Note: Added 2 separate similar cross coverages ID stage because of different
        // arrival times of next instruction w.r.t APU Req
        cr_f_inst_at_id_stage_out_while_fpu_busy : cross cp_id_stage_apu_op_ex_o,
                                                         cp_curr_fpu_apu_op_multicycle {
            option.weight = 5;
            `FPU_ZERO_LATENCY_ILLEGAL_BUSY
        }

        // cross coverage for F-inst arriving at ID-stage output at various stages of APU latency
        // clk-cycles of the ongoing/preceeding F-multicycle instr
        // Note: Added 2 separate similar cross coverages ID stage because of different
        // arrival times of next instruction w.r.t APU Req
        cr_f_inst_at_id_stage_out_with_cyc_window_of_ongoing_fpu_calc : cross cp_id_stage_apu_op_ex_o,
                                                                              cp_f_multicycle_clk_window,
                                                                              cp_curr_fpu_apu_op,
                                                                              cp_fpu_lat_0_and_2_ex_regfile_alu_wr_no_stall {

            option.weight = 5;
            `FPU_MULTICYCLE_WINDOW_ILLEGAL_CASES
            ignore_bins nolatency = binsof(cp_f_multicycle_clk_window.clk1); // for latency == 1 (a.k.a no latency), cp_id_stage_apu_op_ex_o == cp_curr_fpu_apu_op
        }

    endgroup : cg_f_multicycle


    covergroup cg_f_inst_reg(int fpu_latency);
        `per_instance_fcov

        cp_apu_req_valid : coverpoint `COVIF_CB.apu_req {
            bins apu_req_valid = {1'b1};
        }

        cp_apu_grant_valid : coverpoint `COVIF_CB.apu_gnt {
            bins apu_gnt_valid = {1'b1};
        }

        cp_apu_busy : coverpoint `COVIF_CB.apu_busy {
            bins apu_busy_high = {1'b1};
        }

        cp_apu_rvalid : coverpoint `COVIF_CB.apu_rvalid_i {
            bins apu_rvalid = {1};
        }

        cp_apu_contention : coverpoint `COVIF_CB.apu_perf_wb_o {
            bins no_contention = {0};
            bins has_contention = {1};
        }

        // from bhv_logic_1
        cp_curr_fpu_apu_op : coverpoint cntxt.cov_vif.o_curr_fpu_apu_op_if {
            `FPU_OP_BINS
            option.weight = 5;
        }

        // from bhv_logic_1a
        // f-ext instr only uses rs1 for xreg
        cp_cur_fp_rs1_match_prev_nonfp_rd : coverpoint (cntxt.cov_vif.current_instr_rdata[19:15] == cntxt.cov_vif.previous_instr_rdata[11:7])
          iff (cntxt.cov_vif.current_instr_rdata       inside {`RV32F_INSTR_WITH_RS1} && 
               cntxt.cov_vif.previous_instr_rdata[6:0] inside {`RV32_OPCODE_LIST1_WITH_RD} &&
               cntxt.cov_vif.current_instr_rdata != cntxt.cov_vif.previous_instr_rdata) {
          bins cur_rs1_match_prev_rd = {1};
        }
        cp_cur_is_fpu_instr : coverpoint cntxt.cov_vif.current_instr_rdata {
          `RV32F_INSTR_BINS
        }
        cp_prev_is_non_fpu_opcode : coverpoint cntxt.cov_vif.previous_instr_rdata[6:0] {
          `CV32E40P_INSTR_OPCODE_BIT_6_0_BINS__NO_RV32C_FC_F
        }
        cp_prev_is_non_fpu_rd : coverpoint cntxt.cov_vif.previous_instr_rdata[11:7] {
          bins rd[] = {[0:31]};
        }

        // from bhv_logic_2
        cp_last_fpu_apu_op_at_contention : coverpoint cntxt.cov_vif.o_last_fpu_apu_op_if {
            bins curr_apu_op_fmadd        =    {APU_OP_FMADD}     with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_fnmsub       =    {APU_OP_FNMSUB}    with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_fadd         =    {APU_OP_FADD}      with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_fmul         =    {APU_OP_FMUL}      with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_fdiv         =    {APU_OP_FDIV}      ;
            bins curr_apu_op_fsqrt        =    {APU_OP_FSQRT}     ;
            bins curr_apu_op_fsgnj        =    {APU_OP_FSGNJ}     with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_fminmax      =    {APU_OP_FMINMAX}   with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_fcmp         =    {APU_OP_FCMP}      with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_fclassify    =    {APU_OP_FCLASSIFY} with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_f2i          =    {APU_OP_F2I}       with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_i2f          =    {APU_OP_I2F}       with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_fmsub        =    {APU_OP_FMSUB}     with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_fnmadd       =    {APU_OP_FNMADD}    with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_fsub         =    {APU_OP_FSUB}      with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_fsgnj_se     =    {APU_OP_FSGNJ_SE}  with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_f2i_u        =    {APU_OP_F2I_U}     with ((item >= 0) && (fpu_latency != 0));
            bins curr_apu_op_i2f_u        =    {APU_OP_I2F_U}     with ((item >= 0) && (fpu_latency != 0));
            option.weight = 5;
        }

        // TODO: need to add another cover point for F-inst at ID-EX boundary ?
        cp_id_stage_f_inst : coverpoint `COVIF_CB.id_stage_instr_rdata_i
                                        iff (`COVIF_CB.id_stage_instr_valid_i == 1) {

            `RV32F_INSTR_BINS
            option.weight = 5;
        }

        // TODO: to add rv32c coverage
        cp_id_stage_non_rv32fc_inst : coverpoint `COVIF_CB.id_stage_instr_rdata_i[6:0]
                                                 iff (`COVIF_CB.id_stage_instr_valid_i == 1) {

            `CV32E40P_INSTR_OPCODE_BIT_6_0_BINS__NO_RV32C_FC
            option.weight = 5;
        }

        cp_id_f_inst_fs1 : coverpoint `COVIF_CB.id_stage_instr_rdata_i[19:15]
                                      iff (`COVIF_CB.id_stage_instr_valid_i == 1) {

            bins fs1[] = {[0:31]};
        }

        cp_id_f_inst_fs2 : coverpoint `COVIF_CB.id_stage_instr_rdata_i[24:20]
                                      iff (`COVIF_CB.id_stage_instr_valid_i == 1) {

            bins fs2[] = {[0:31]};
        }

        // from bhv_logic_3
        cp_curr_fpu_inst_fd : coverpoint cntxt.cov_vif.curr_fpu_fd {
            bins fd[] = {[0:31]};
        }

        // from bhv_logic_3
        cp_curr_fpu_inst_fd_for_0_lat_apu_result : coverpoint cntxt.cov_vif.curr_fpu_fd
                                                              iff ( (`COVIF_CB.apu_req == 1) &&
                                                                    (`COVIF_CB.apu_gnt == 1) &&
                                                                    (`COVIF_CB.apu_rvalid_i == 1) ) {

            bins fd[] = {[0:31]};
        }

        // from bhv_logic_3
        cp_curr_fpu_inst_fd_for_multicyc_lat_apu_result : coverpoint cntxt.cov_vif.curr_fpu_fd
                                                                     iff ( (`COVIF_CB.apu_busy == 1) &&
                                                                           (`COVIF_CB.apu_rvalid_i == 1) ) {

            bins fd[] = {[0:31]};
        }

        // from bhv_logic_3
        cp_curr_fpu_inst_rd : coverpoint cntxt.cov_vif.curr_fpu_rd {
            bins rd[] = {[0:31]};
        }

        // from bhv_logic_3
        cp_curr_fpu_inst_rd_for_0_lat_apu_result : coverpoint cntxt.cov_vif.curr_fpu_rd
                                                              iff ( (`COVIF_CB.apu_req == 1) &&
                                                                    (`COVIF_CB.apu_gnt == 1) &&
                                                                    (`COVIF_CB.apu_rvalid_i == 1) ) {

            // FIXME: this is a kludge for a known VCS issue
            //bins rd[] = {[0:31]} with (fpu_latency == 0);
            bins rd[] = {[0:31]} `WITH (fpu_latency == 0);
        }

        // from bhv_logic_3
        cp_curr_fpu_inst_rd_for_multicyc_lat_apu_result : coverpoint cntxt.cov_vif.curr_fpu_rd
                                                                     iff ( (`COVIF_CB.apu_busy == 1) &&
                                                                           (`COVIF_CB.apu_rvalid_i == 1) ) {

            bins rd[] = {[0:31]};
        }

        cp_apu_alu_contention_wr_rd : coverpoint cntxt.cov_vif.curr_rd_at_ex_regfile_wr_contention {
            bins rd[] = {[0:31]}                        with ( ((item + 1) * (fpu_latency != 1)) != 0 );
            illegal_bins rd_addr_32_63 = {[32:63]}      with ( ((item + 1) * (fpu_latency != 1)) != 0 );
        }

        // from bhv_logic_3
        cp_lsu_apu_contention_wr_rd : coverpoint cntxt.cov_vif.curr_rd_at_wb_regfile_wr_contention {
            bins rd[] = {[0:31]}                        with ( ((item + 1) * (fpu_latency == 1)) != 0 );
            bins fd[] = {[32:63]}                       with ( ((item + 1) * (fpu_latency == 1)) != 0 ); // flw uses ls path for load to freq
        }

        // from bhv_logic_2 (revised)
        // [optional] this cp is optional as contention has no relation with rd/fd
        cp_prev_rd_waddr_contention : coverpoint cntxt.cov_vif.prev_rd_waddr_contention {
            bins rd[] = {[1:31]};
            bins fd[] = {[32:63]};
            ignore_bins zero = {0};
        }

        // from bhv_logic_2
        cp_contention_state : coverpoint cntxt.cov_vif.contention_state {
            bins no_contention = {0};
            bins contention_1st_cyc_done = {1};
            bins contention_2nd_cyc_done = {2};
            ignore_bins state3 = {3};
        }

        cp_b2b_contention : coverpoint cntxt.cov_vif.b2b_contention {
            bins b2b_contention_true = {1};
            option.weight = 5;
        }

        // from bhv_logic_3
        // next fp_insn fs1 is fd of current fp_insn
        cp_fd_fs1_eq : coverpoint (`COVIF_CB.id_stage_instr_rdata_i[19:15] == cntxt.cov_vif.curr_fpu_fd)
                                  iff (`COVIF_CB.id_stage_instr_valid_i == 1) {

            bins fd_fs1_equal = {1};
        }

        // from bhv_logic_3
        // next fp_insn fs2 is fd of current fp_insn
        cp_fd_fs2_eq : coverpoint (`COVIF_CB.id_stage_instr_rdata_i[24:20] == cntxt.cov_vif.curr_fpu_fd)
                                  iff (`COVIF_CB.id_stage_instr_valid_i == 1) {

            bins fd_fs2_equal = {1};
        }

        // from bhv_logic_3
        // next fp_insn fs3 is fd of current fp_insn
        cp_fd_fs3_eq : coverpoint (`COVIF_CB.id_stage_instr_rdata_i[31:27] == cntxt.cov_vif.curr_fpu_fd)
                                  iff (`COVIF_CB.id_stage_instr_valid_i == 1) {

            bins fd_fs3_equal = {1};
        }

        // from bhv_logic_3
        // next insn rs1 is rd of current fp_insn
        cp_rd_rs1_eq : coverpoint (`COVIF_CB.id_stage_instr_rdata_i[19:15] == cntxt.cov_vif.curr_fpu_rd)
                                  iff (`COVIF_CB.id_stage_instr_valid_i == 1) {

            bins rd_rs1_equal = {1};
        }

        // from bhv_logic_3
        // next insn rs2 is rd of current fp_insn
        cp_rd_rs2_eq : coverpoint (`COVIF_CB.id_stage_instr_rdata_i[24:20] == cntxt.cov_vif.curr_fpu_rd)
                                  iff (`COVIF_CB.id_stage_instr_valid_i == 1) {

            bins rd_rs1_equal = {1};
        }

        //*********************************************************************************************************
        //     Cross Cov description for reg-to-reg dependency cases in instr sequence with F-multicycle instr
        //*********************************************************************************************************
        // This Cross Coverage captures the cases where latest APU execution's RD addr is same as
        // rs1/rs2/rs3 of the next instruction in pipeline.
        // Design is expected to stall EX in such scenarios until the previous instruction retires.
        // The test scenarios are captured for correct RTL behavior, expecting EX stall in such cases.
        // And for any conflicting design behaviour with EX proceeding without stalls, tests rely on Ref model
        // to flag the resulting errors.
        
        //*********************************************************************************************************
        // CASES WITH/WITHOUT CONTENTION AT THE TIME OF APU RESULT WRITE TO REGFILE
        // WHERE APU WRITE WILL WIN (APU LATENCY CONFIG = 0,1,2)
        //*********************************************************************************************************

        // cross coverage for F-instr following F-instr with fd to fs1 dependency
        cr_fd_fs1_eq_nonzero_lat : cross cp_fd_fs1_eq,
                                         cp_id_stage_f_inst,
                                         cp_curr_fpu_inst_fd_for_multicyc_lat_apu_result,
                                         cp_curr_fpu_apu_op {

            option.weight = 5;
            `IGNORE_BINS_NON_FS1_F_INSTR            // ignore insn that no fs1
            `IGNORE_BINS_NON_FD_F_INSTR             // ignore insn APU_OP_FCMP, APU_OP_FCLASSIFY, APU_OP_F2I, APU_OP_F2I_U
            `IGNORE_BINS_ZERO_LAT_FPU_OP            // only apply in 0cyclat - ignore insn except div and sqrt
        }

        // cross coverage for F-instr following F-instr with fd to fs2 dependency
        cr_fd_fs2_eq_nonzero_lat : cross cp_fd_fs2_eq,
                                         cp_id_stage_f_inst,
                                         cp_curr_fpu_inst_fd_for_multicyc_lat_apu_result,
                                         cp_curr_fpu_apu_op {

            option.weight = 5;
            `IGNORE_BINS_NON_FS2_F_INSTR            // ignore insn that no fs2
            `IGNORE_BINS_NON_FD_F_INSTR
            `IGNORE_BINS_ZERO_LAT_FPU_OP
        }

        // cross coverage for F-instr following F-instr with fd to fs3 dependency
        cr_fd_fs3_eq_nonzero_lat : cross cp_fd_fs3_eq,
                                         cp_id_stage_f_inst,
                                         cp_curr_fpu_inst_fd_for_multicyc_lat_apu_result,
                                         cp_curr_fpu_apu_op {

            option.weight = 5;
            `IGNORE_BINS_NON_FS3_F_INSTR            // ignore insn that no fs3
            `IGNORE_BINS_NON_FD_F_INSTR
            `IGNORE_BINS_ZERO_LAT_FPU_OP
        }

        // cross coverage for F-instr following F-instr with rd to rs1 dependency
        cr_rd_rs1_eq_nonzero_lat  :  cross cp_rd_rs1_eq,
                                           cp_id_stage_f_inst,
                                           cp_curr_fpu_inst_rd_for_multicyc_lat_apu_result,
                                           cp_curr_fpu_apu_op {

            option.weight = 5;
            `IGNORE_BINS_ZERO_LAT_FPU_OP            // only apply in 0cyclat - ignore insn except div and sqrt
            `IGNORE_BINS_NON_RD_F_INSTR             // ignore insn except APU_OP_FCMP, APU_OP_FCLASSIFY, APU_OP_F2I, APU_OP_F2I_U in ex_state
            `IGNORE_BINS_NON_RS1_F_INSTR_IN_ID      // ignore insn except TB_INS_FLW, TB_INS_FSW, TB_INS_FMVSX, TB_INS_FCVTSW, TB_INS_FCVTSWU in dec_state
        }

        // cross coverage for Non F-instr following F-instr with rd to rs1 dependency
        cr_rv32f_rd_non_rv32f_rs1_eq_nonzero_lat : cross cp_rd_rs1_eq,
                                                         cp_id_stage_non_rv32fc_inst,
                                                         cp_curr_fpu_inst_rd_for_multicyc_lat_apu_result,
                                                         cp_curr_fpu_apu_op {

            option.weight = 5;
            `IGNORE_BINS_ZERO_LAT_FPU_OP
            `IGNORE_BINS_NON_RD_F_INSTR
            `IGNORE_BINS_NON_RS1_CV32E40P_INSTR
        }

        // cross coverage for Non F-instr following F-instr with rd to rs2 dependency
        cr_rv32f_rd_non_rv32f_rs2_eq_nonzero_lat : cross cp_rd_rs2_eq,
                                                         cp_id_stage_non_rv32fc_inst,
                                                         cp_curr_fpu_inst_rd_for_multicyc_lat_apu_result,
                                                         cp_curr_fpu_apu_op {

            option.weight = 5;
            `IGNORE_BINS_ZERO_LAT_FPU_OP
            `IGNORE_BINS_NON_RD_F_INSTR
            `IGNORE_BINS_NON_RS2_CV32E40P_INSTR
        }

        // cross coverage for F-instr following Non F-instr with rd to rs1 dependency
        // e.g prev.non_fp(rd) == cur.fp(rs1)
        cr_non_rv32f_rd_rv32f_rs1                : cross cp_cur_fp_rs1_match_prev_nonfp_rd,
                                                         cp_cur_is_fpu_instr,
                                                         cp_prev_is_non_fpu_opcode,
                                                         cp_prev_is_non_fpu_rd {

            option.weight = 5;
            `IGNORE_BINS_PREV_NON_FPU_OPCODE_WO_RD
            `IGNORE_BINS_CUR_FPU_OPCODE_WO_RS1
        }

        // cross coverage for contention case 2nd cycle with ALU regfile write
        cr_waddr_rd_apu_alu_ex_contention : cross cp_apu_alu_contention_wr_rd,
                                                  cp_contention_state,
                                                  cp_apu_contention {

            bins main_cr_bin              = cr_waddr_rd_apu_alu_ex_contention with ((cp_contention_state < 3) && (fpu_latency != 1));
            ignore_bins skip_if_other_cfg = cr_waddr_rd_apu_alu_ex_contention with ((cp_contention_state < 3) && (fpu_latency == 1));

            `IGNORE_BINS_NON_STALLED_CONTENTION_WR_STATE
            `IGNORE_BINS_NO_CONTENTION
        }

        //*********************************************************************************************************
        // CASES WITH/WITHOUT CONTENTION AT APU RESULT WRITE TO REGFILE. APU_LATENCY=0 PRIOIRTY APU WRITE WINS
        //*********************************************************************************************************

        // cross coverage for F-instr following F-instr with fd to fs1 dependency - 0 Latency
        cr_fd_fs1_eq_no_lat  :  cross cp_fd_fs1_eq,
                                      cp_id_stage_f_inst,
                                      cp_curr_fpu_inst_fd_for_0_lat_apu_result,
                                      cp_curr_fpu_apu_op {

            option.weight = 5;
            bins main_cr_bin              = cr_fd_fs1_eq_no_lat with ((cp_fd_fs1_eq == 1) && (fpu_latency == 0));
            ignore_bins skip_if_other_cfg = cr_fd_fs1_eq_no_lat with ((cp_fd_fs1_eq == 1) && (fpu_latency != 0));
            `IGNORE_BINS_NON_FD_F_INSTR
            `IGNORE_BINS_NON_FS1_F_INSTR
        }

        // cross coverage for F-instr following F-instr with fd to fs2 dependency - 0 Latency
        cr_fd_fs2_eq_no_lat  :  cross cp_fd_fs2_eq,
                                      cp_id_stage_f_inst,
                                      cp_curr_fpu_inst_fd_for_0_lat_apu_result,
                                      cp_curr_fpu_apu_op {

            option.weight = 5;
            bins main_cr_bin              = cr_fd_fs2_eq_no_lat with ((cp_fd_fs2_eq == 1) && (fpu_latency == 0));
            ignore_bins skip_if_other_cfg = cr_fd_fs2_eq_no_lat with ((cp_fd_fs2_eq == 1) && (fpu_latency != 0));
            `IGNORE_BINS_NON_FD_F_INSTR
            `IGNORE_BINS_NON_FS2_F_INSTR
        }

        // cross coverage for F-instr following F-instr with fd to fs3 dependency - 0 Latency
        cr_fd_fs3_eq_no_lat  :  cross cp_fd_fs3_eq,
                                      cp_id_stage_f_inst,
                                      cp_curr_fpu_inst_fd_for_0_lat_apu_result,
                                      cp_curr_fpu_apu_op {

            option.weight = 5;
            bins main_cr_bin              = cr_fd_fs3_eq_no_lat with ((cp_fd_fs3_eq == 1) && (fpu_latency == 0));
            ignore_bins skip_if_other_cfg = cr_fd_fs3_eq_no_lat with ((cp_fd_fs3_eq == 1) && (fpu_latency != 0));
            `IGNORE_BINS_NON_FD_F_INSTR
            `IGNORE_BINS_NON_FS3_F_INSTR
        }

        // cross coverage for F-instr following F-instr with rd to rs1 dependency - 0 latency
        // example: insn[0].rd == insn[1].rs1 (both are fp_insn)
        cr_rd_rs1_eq_no_lat  :  cross cp_rd_rs1_eq,
                                      cp_id_stage_f_inst,
                                      cp_curr_fpu_inst_rd_for_0_lat_apu_result,
                                      cp_curr_fpu_apu_op {

            option.weight = 5;
            bins main_cr_bin              = cr_rd_rs1_eq_no_lat with ((cp_rd_rs1_eq == 1) && (fpu_latency == 0));
            ignore_bins skip_if_other_cfg = cr_rd_rs1_eq_no_lat with ((cp_rd_rs1_eq == 1) && (fpu_latency != 0));
            `IGNORE_BINS_NON_RD_F_INSTR
            `IGNORE_BINS_NON_RS1_F_INSTR_IN_ID
        }

        // cross coverage for Non F-instr following F-instr with rd to rs1 dependency - 0 Latency
        cr_rv32f_rd_non_rv32fc_rs1_eq_no_lat  :  cross cp_rd_rs1_eq,
                                                       cp_id_stage_non_rv32fc_inst,
                                                       cp_curr_fpu_inst_rd_for_0_lat_apu_result,
                                                       cp_curr_fpu_apu_op {

            option.weight = 5;
            bins main_cr_bin              = cr_rv32f_rd_non_rv32fc_rs1_eq_no_lat with ((cp_rd_rs1_eq == 1) && (fpu_latency == 0));
            ignore_bins skip_if_other_cfg = cr_rv32f_rd_non_rv32fc_rs1_eq_no_lat with ((cp_rd_rs1_eq == 1) && (fpu_latency != 0));
            `IGNORE_BINS_NON_RD_F_INSTR
            `IGNORE_BINS_NON_RS1_CV32E40P_INSTR
        }
        // cross coverage for Non F-instr following F-instr with rd to rs2 dependency - 0 Latency
        cr_rv32f_rd_non_rv32fc_rs2_eq_no_lat  :  cross cp_rd_rs2_eq,
                                                       cp_id_stage_non_rv32fc_inst,
                                                       cp_curr_fpu_inst_rd_for_0_lat_apu_result,
                                                       cp_curr_fpu_apu_op {

            option.weight = 5;
            bins main_cr_bin              = cr_rv32f_rd_non_rv32fc_rs2_eq_no_lat with ((cp_rd_rs2_eq == 1) && (fpu_latency == 0));
            ignore_bins skip_if_other_cfg = cr_rv32f_rd_non_rv32fc_rs2_eq_no_lat with ((cp_rd_rs2_eq == 1) && (fpu_latency != 0));
            `IGNORE_BINS_NON_RD_F_INSTR
            `IGNORE_BINS_NON_RS2_CV32E40P_INSTR
        }

        //*********************************************************************************************************
        // CONTENTION DURING APU RESULT WRITE TO REGFILE WHERE APU RESULT WRITE STALLS. APU LATENCY = 1
        //*********************************************************************************************************

        // cp_apu_contention = 1 cases
        // cp_contention_state = 1 indicates that there was contention in WB at LSU-APU regfile wr mux

        // cross coverage for F-instr following F-instr with fd to fs1 dependency
        // case with APU latency = 1 and contention with LSU
        cr_fd_fs1_eq_nonzero_lat_with_contention : cross cp_fd_fs1_eq,
                                                         cp_id_stage_f_inst,
                                                         cp_curr_fpu_inst_fd,
                                                         cp_last_fpu_apu_op_at_contention,
                                                         cp_contention_state,
                                                         cp_apu_contention {

            option.weight = 5;
            bins main_cr_bin              = cr_fd_fs1_eq_nonzero_lat_with_contention with ((cp_fd_fs1_eq == 1) && (fpu_latency == 1));
            ignore_bins skip_if_other_cfg = cr_fd_fs1_eq_nonzero_lat_with_contention with ((cp_fd_fs1_eq == 1) && (fpu_latency != 1));
            `IGNORE_BINS_NON_FS1_F_INSTR
            `IGNORE_BINS_NON_STALLED_CONTENTION_WR_STATE
            `IGNORE_BINS_NON_FD_F_INSTR_AT_CONTENTION
            `IGNORE_BINS_CONTENTION_AT_LSU_REGFILE_WR
        }

        // cross coverage for F-instr following F-instr with fd to fs2 dependency
        // case with APU latency = 1 and contention with LSU
        cr_fd_fs2_eq_nonzero_lat_with_contention : cross cp_fd_fs2_eq,
                                                         cp_id_stage_f_inst,
                                                         cp_curr_fpu_inst_fd,
                                                         cp_last_fpu_apu_op_at_contention,
                                                         cp_contention_state,
                                                         cp_apu_contention {

            option.weight = 5;
            bins main_cr_bin              = cr_fd_fs2_eq_nonzero_lat_with_contention with ((cp_fd_fs2_eq == 1) && (fpu_latency == 1));
            ignore_bins skip_if_other_cfg = cr_fd_fs2_eq_nonzero_lat_with_contention with ((cp_fd_fs2_eq == 1) && (fpu_latency != 1));
            `IGNORE_BINS_NON_FS2_F_INSTR
            `IGNORE_BINS_NON_STALLED_CONTENTION_WR_STATE
            `IGNORE_BINS_NON_FD_F_INSTR_AT_CONTENTION
            `IGNORE_BINS_CONTENTION_AT_LSU_REGFILE_WR
        }

        // cross coverage for F-instr following F-instr with fd to fs3 dependency
        // case with APU latency = 1 and contention with LSU
        cr_fd_fs3_eq_nonzero_lat_with_contention : cross cp_fd_fs3_eq,
                                                         cp_id_stage_f_inst,
                                                         cp_curr_fpu_inst_fd,
                                                         cp_last_fpu_apu_op_at_contention,
                                                         cp_contention_state,
                                                         cp_apu_contention {

            option.weight = 5;
            bins main_cr_bin              = cr_fd_fs3_eq_nonzero_lat_with_contention with ((cp_fd_fs3_eq == 1) && (fpu_latency == 1));
            ignore_bins skip_if_other_cfg = cr_fd_fs3_eq_nonzero_lat_with_contention with ((cp_fd_fs3_eq == 1) && (fpu_latency != 1));
            `IGNORE_BINS_NON_FS3_F_INSTR
            `IGNORE_BINS_NON_STALLED_CONTENTION_WR_STATE
            `IGNORE_BINS_NON_FD_F_INSTR_AT_CONTENTION
            `IGNORE_BINS_CONTENTION_AT_LSU_REGFILE_WR
        }

        // cross coverage for F-instr following F-instr with rd to rs1 dependency - 1 latency
        // case with APU latency = 1 and contention with LSU
        cr_rd_rs1_eq_nonzero_lat_with_contention : cross cp_rd_rs1_eq,
                                                         cp_id_stage_f_inst,
                                                         cp_curr_fpu_inst_rd,
                                                         cp_last_fpu_apu_op_at_contention,
                                                         cp_contention_state,
                                                         cp_apu_contention {

            option.weight = 5;
            bins main_cr_bin              = cr_rd_rs1_eq_nonzero_lat_with_contention with ((cp_rd_rs1_eq == 1) && (fpu_latency == 1));
            ignore_bins skip_if_other_cfg = cr_rd_rs1_eq_nonzero_lat_with_contention with ((cp_rd_rs1_eq == 1) && (fpu_latency != 1));
            `IGNORE_BINS_NON_FS1_F_INSTR
            `IGNORE_BINS_NON_STALLED_CONTENTION_WR_STATE
            `IGNORE_BINS_CONTENTION_AT_LSU_REGFILE_WR
            `IGNORE_BINS_NON_RD_F_INSTR_AT_CONTENTION
        }

        // cross coverage for Non F-instr following F-instr with rd to rs1 dependency
        // case with APU latency = 1 and contention with LSU
        cr_rv32f_rd_non_rv32fc_rs1_eq_nonzero_lat_with_contention : cross cp_rd_rs1_eq,
                                                                          cp_id_stage_non_rv32fc_inst,
                                                                          cp_curr_fpu_inst_rd,
                                                                          cp_last_fpu_apu_op_at_contention,
                                                                          cp_contention_state,
                                                                          cp_apu_contention {

            option.weight = 5;
            bins main_cr_bin              = cr_rv32f_rd_non_rv32fc_rs1_eq_nonzero_lat_with_contention with ((cp_rd_rs1_eq == 1) && (fpu_latency == 1));
            ignore_bins skip_if_other_cfg = cr_rv32f_rd_non_rv32fc_rs1_eq_nonzero_lat_with_contention with ((cp_rd_rs1_eq == 1) && (fpu_latency != 1));
            `IGNORE_BINS_NON_RS1_CV32E40P_INSTR
            `IGNORE_BINS_NON_STALLED_CONTENTION_WR_STATE
            `IGNORE_BINS_CONTENTION_AT_LSU_REGFILE_WR
            `IGNORE_BINS_NON_RD_F_INSTR_AT_CONTENTION
        }

        // cross coverage for Non F-instr following F-instr with rd to rs2 dependency
        // case with APU latency = 1 and contention with LSU
        cr_rv32f_rd_non_rv32fc_rs2_eq_nonzero_lat_with_contention : cross cp_rd_rs2_eq,
                                                                          cp_id_stage_non_rv32fc_inst,
                                                                          cp_curr_fpu_inst_rd,
                                                                          cp_last_fpu_apu_op_at_contention,
                                                                          cp_contention_state,
                                                                          cp_apu_contention {

            option.weight = 5;
            bins main_cr_bin              = cr_rv32f_rd_non_rv32fc_rs2_eq_nonzero_lat_with_contention with ((cp_rd_rs2_eq == 1) && (fpu_latency == 1));
            ignore_bins skip_if_other_cfg = cr_rv32f_rd_non_rv32fc_rs2_eq_nonzero_lat_with_contention with ((cp_rd_rs2_eq == 1) && (fpu_latency != 1));
            `IGNORE_BINS_NON_RS2_CV32E40P_INSTR
            `IGNORE_BINS_NON_STALLED_CONTENTION_WR_STATE
            `IGNORE_BINS_CONTENTION_AT_LSU_REGFILE_WR
            `IGNORE_BINS_NON_RD_F_INSTR_AT_CONTENTION
        }

        // TODO: does it require checking rd to rs1/rs2 equal in this case?
        // cross coverage for contention case 1st cycle with LSU regfile write win
        cr_waddr_rd_lsu_apu_wb_contention : cross cp_apu_busy,
                                                  cp_apu_rvalid,
                                                  cp_lsu_apu_contention_wr_rd,
                                                  cp_apu_contention {

            bins main_cr_bin              = cr_waddr_rd_lsu_apu_wb_contention with ((cp_apu_rvalid == 1) && (fpu_latency == 1));
            ignore_bins skip_if_other_cfg = cr_waddr_rd_lsu_apu_wb_contention with ((cp_apu_rvalid == 1) && (fpu_latency != 1));
            `IGNORE_BINS_NO_CONTENTION_LSU
        }

    endgroup : cg_f_inst_reg

endclass : uvme_cv32e40p_fp_instr_covg

function uvme_cv32e40p_fp_instr_covg::new(string name = "cv32e40p_fp_instr_covg", uvm_component parent = null);
    super.new(name, parent);
    void'(uvm_config_db#(uvme_cv32e40p_cfg_c)::get(this, "", "cfg", cfg));
    if (cfg == null) begin
      `uvm_fatal("cv32e40p_fp_instr_covg", "Configuration handle is null")
    end

    cg_f_multicycle = new(.fpu_latency(cfg.fpu_latency));
    cg_f_inst_reg = new(.fpu_latency(cfg.fpu_latency));

endfunction : new

function void uvme_cv32e40p_fp_instr_covg::build_phase(uvm_phase phase);
    super.build_phase(phase);

    void'(uvm_config_db#(uvme_cv32e40p_cntxt_c)::get(this, "", "cntxt", cntxt));
    if (cntxt == null) begin
        `uvm_fatal("cv32e40p_fp_instr_covg", "No cntxt object passed to model");
    end
endfunction : build_phase

task uvme_cv32e40p_fp_instr_covg::run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("cv32e40p_fp_instr_covg", "The RV32_F coverage model is running", UVM_LOW);
    fork
        sample_clk_i();
    join_none
endtask : run_phase


task uvme_cv32e40p_fp_instr_covg::sample_clk_i();
    while (1) begin
        @(`COVIF_CB);
        if ((`COVIF_CB.debug_req_i == 0) && (`COVIF_CB.debug_mode_q == 0) &&
            (`COVIF_CB.trigger_match_i == 0) && (cntxt.debug_cov_vif.mon_cb.dcsr_q[2] == 0)) begin // Only sample in M-mode without debug entry cases
            cg_f_multicycle.sample();
            cg_f_inst_reg.sample();
        end
    end
endtask  : sample_clk_i
