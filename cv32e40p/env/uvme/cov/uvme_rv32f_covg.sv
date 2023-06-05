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

class uvme_rv32f_zfinx_covg extends uvm_component;
    /*
    * Class members
    */
    uvme_cv32e40p_cntxt_c  cntxt;
    logic [5:0]     curr_fpu_apu_op;

    `uvm_component_utils(uvme_rv32f_zfinx_covg);

    extern function new(string name = "rv32f_zfinx_covg", uvm_component parent = null);
    extern function void build_phase(uvm_phase phase);
    extern task run_phase(uvm_phase phase);
    extern task sample_clk_i();

    /*
    * Covergroups
    */

    covergroup cg_f_multicycle;
        `per_instance_fcov
        option.at_least = 10;

        cp_if_stage_f_inst : coverpoint cntxt.cov_vif.mon_cb.if_stage_instr_rdata_i {
            wildcard bins if_fadd = {cv32e40p_tracer_pkg::INSTR_FADD};
            wildcard bins if_fsub = {cv32e40p_tracer_pkg::INSTR_FSUB};
            wildcard bins if_fmul = {cv32e40p_tracer_pkg::INSTR_FMUL};
            wildcard bins if_fdiv = {cv32e40p_tracer_pkg::INSTR_FDIV};
            wildcard bins if_fsqrt = {cv32e40p_tracer_pkg::INSTR_FSQRT};
            wildcard bins if_fsgnjs = {cv32e40p_tracer_pkg::INSTR_FSGNJS};
            wildcard bins if_fsgnjns = {cv32e40p_tracer_pkg::INSTR_FSGNJNS};
            wildcard bins if_fsgnjxs = {cv32e40p_tracer_pkg::INSTR_FSGNJXS};
            wildcard bins if_fmin = {cv32e40p_tracer_pkg::INSTR_FMIN};
            wildcard bins if_fmax = {cv32e40p_tracer_pkg::INSTR_FMAX};
            wildcard bins if_fcvtws = {cv32e40p_tracer_pkg::INSTR_FCVTWS};
            wildcard bins if_fcvtwus = {cv32e40p_tracer_pkg::INSTR_FCVTWUS};
            wildcard bins if_fmvxs = {cv32e40p_tracer_pkg::INSTR_FMVXS};
            wildcard bins if_feqs = {cv32e40p_tracer_pkg::INSTR_FEQS};
            wildcard bins if_flts = {cv32e40p_tracer_pkg::INSTR_FLTS};
            wildcard bins if_fles = {cv32e40p_tracer_pkg::INSTR_FLES};
            wildcard bins if_fclass = {cv32e40p_tracer_pkg::INSTR_FCLASS};
            wildcard bins if_fcvtsw = {cv32e40p_tracer_pkg::INSTR_FCVTSW};
            wildcard bins if_fcvtswu = {cv32e40p_tracer_pkg::INSTR_FCVTSWU};
            wildcard bins if_fmvsw = {cv32e40p_tracer_pkg::INSTR_FMVSX};
            wildcard bins if_fmadd = {cv32e40p_tracer_pkg::INSTR_FMADD};
            wildcard bins if_fmsub = {cv32e40p_tracer_pkg::INSTR_FMSUB};
            wildcard bins if_fnmsub = {cv32e40p_tracer_pkg::INSTR_FNMSUB};
            wildcard bins if_fnmadd = {cv32e40p_tracer_pkg::INSTR_FNMADD};
            option.weight = 5;
        }

        cp_id_stage_f_inst : coverpoint cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i {
            wildcard bins id_fadd = {cv32e40p_tracer_pkg::INSTR_FADD};
            wildcard bins id_fsub = {cv32e40p_tracer_pkg::INSTR_FSUB};
            wildcard bins id_fmul = {cv32e40p_tracer_pkg::INSTR_FMUL};
            wildcard bins id_fdiv = {cv32e40p_tracer_pkg::INSTR_FDIV};
            wildcard bins id_fsqrt = {cv32e40p_tracer_pkg::INSTR_FSQRT};
            wildcard bins id_fsgnjs = {cv32e40p_tracer_pkg::INSTR_FSGNJS};
            wildcard bins id_fsgnjns = {cv32e40p_tracer_pkg::INSTR_FSGNJNS};
            wildcard bins id_fsgnjxs = {cv32e40p_tracer_pkg::INSTR_FSGNJXS};
            wildcard bins id_fmin = {cv32e40p_tracer_pkg::INSTR_FMIN};
            wildcard bins id_fmax = {cv32e40p_tracer_pkg::INSTR_FMAX};
            wildcard bins id_fcvtws = {cv32e40p_tracer_pkg::INSTR_FCVTWS};
            wildcard bins id_fcvtwus = {cv32e40p_tracer_pkg::INSTR_FCVTWUS};
            wildcard bins id_fmvxs = {cv32e40p_tracer_pkg::INSTR_FMVXS};
            wildcard bins id_feqs = {cv32e40p_tracer_pkg::INSTR_FEQS};
            wildcard bins id_flts = {cv32e40p_tracer_pkg::INSTR_FLTS};
            wildcard bins id_fles = {cv32e40p_tracer_pkg::INSTR_FLES};
            wildcard bins id_fclass = {cv32e40p_tracer_pkg::INSTR_FCLASS};
            wildcard bins id_fcvtsw = {cv32e40p_tracer_pkg::INSTR_FCVTSW};
            wildcard bins id_fcvtswu = {cv32e40p_tracer_pkg::INSTR_FCVTSWU};
            wildcard bins id_fmvsw = {cv32e40p_tracer_pkg::INSTR_FMVSX};
            wildcard bins id_fmadd = {cv32e40p_tracer_pkg::INSTR_FMADD};
            wildcard bins id_fmsub = {cv32e40p_tracer_pkg::INSTR_FMSUB};
            wildcard bins id_fnmsub = {cv32e40p_tracer_pkg::INSTR_FNMSUB};
            wildcard bins id_fnmadd = {cv32e40p_tracer_pkg::INSTR_FNMADD};
            option.weight = 5;
        }

        cp_id_stage_apu_op_ex_o : coverpoint cntxt.cov_vif.mon_cb.id_stage_apu_op_ex_o {
            bins next_apu_op_fmadd       =    {APU_OP_FMADD};
            bins next_apu_op_fnmsub      =    {APU_OP_FNMSUB};
            bins next_apu_op_fadd        =    {APU_OP_FADD};
            bins next_apu_op_fmul        =    {APU_OP_FMUL};
            bins next_apu_op_fdiv        =    {APU_OP_FDIV};
            bins next_apu_op_fsqrt       =    {APU_OP_FSQRT};
            bins next_apu_op_fsgnj       =    {APU_OP_FSGNJ};
            bins next_apu_op_fminmax     =    {APU_OP_FMINMAX};
            bins next_apu_op_fcmp        =    {APU_OP_FCMP};
            bins next_apu_op_fclassify   =    {APU_OP_FCLASSIFY};
            bins next_apu_op_f2f         =    {APU_OP_F2F};
            bins next_apu_op_f2i         =    {APU_OP_F2I};
            bins next_apu_op_i2f         =    {APU_OP_I2F};
            bins next_apu_op_fmsub       =    {APU_OP_FMSUB};
            bins next_apu_op_fnmadd      =    {APU_OP_FNMADD};
            bins next_apu_op_fsub        =    {APU_OP_FSUB};
            bins next_apu_op_fsgnj_se    =    {APU_OP_FSGNJ_SE};
            bins next_apu_op_f2i_u       =    {APU_OP_F2I_U};
            bins next_apu_op_i2f_u       =    {APU_OP_I2F_U};
            option.weight = 5;
        }

        cp_f_multicycle_clk_window : coverpoint cntxt.cov_vif.if_clk_cycle_window {
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
            ignore_bins ignore_idle = {0};
            illegal_bins clk_more_than_12 = {[13:31]};
        }

        cp_id_stage_inst_valid : coverpoint cntxt.cov_vif.mon_cb.id_stage_instr_valid_i {
            bins id_stage_instr_valid = {1};
            option.weight = 1;
        }

        cp_if_stage_inst_valid : coverpoint cntxt.cov_vif.mon_cb.if_stage_instr_rvalid_i {
            bins if_stage_instr_valid = {1};
            option.weight = 1;
        }

        cp_id_stage_apu_en_ex_o : coverpoint cntxt.cov_vif.mon_cb.id_stage_apu_en_ex_o {
            bins id_stage_apu_en_ex_1 = {1};
            bins id_stage_apu_en_ex_0_to_1 = (0 => 1);
            option.weight = 1;
        }

        cp_apu_req_valid : coverpoint cntxt.cov_vif.mon_cb.apu_req {
            bins apu_req_valid = {1'b1};
            option.weight = 1;
        }

        cp_apu_grant_valid : coverpoint cntxt.cov_vif.mon_cb.apu_gnt {
            bins apu_gnt_valid = {1'b1};
            option.weight = 1;
        }

        cp_apu_busy : coverpoint cntxt.cov_vif.mon_cb.apu_busy {
            bins apu_busy_high = {1'b1};
            option.weight = 1;
        }

        cp_curr_fpu_apu_op : coverpoint cntxt.cov_vif.o_curr_fpu_apu_op_if {
            bins curr_apu_op_fmadd       =    {APU_OP_FMADD};
            bins curr_apu_op_fnmsub      =    {APU_OP_FNMSUB};
            bins curr_apu_op_fadd        =    {APU_OP_FADD};
            bins curr_apu_op_fmul        =    {APU_OP_FMUL};
            bins curr_apu_op_fdiv        =    {APU_OP_FDIV};
            bins curr_apu_op_fsqrt       =    {APU_OP_FSQRT};
            bins curr_apu_op_fsgnj       =    {APU_OP_FSGNJ};
            bins curr_apu_op_fminmax     =    {APU_OP_FMINMAX};
            bins curr_apu_op_fcmp        =    {APU_OP_FCMP};
            bins curr_apu_op_fclassify   =    {APU_OP_FCLASSIFY};
            bins curr_apu_op_f2f         =    {APU_OP_F2F};
            bins curr_apu_op_f2i         =    {APU_OP_F2I};
            bins curr_apu_op_i2f         =    {APU_OP_I2F};
            bins curr_apu_op_fmsub       =    {APU_OP_FMSUB};
            bins curr_apu_op_fnmadd      =    {APU_OP_FNMADD};
            bins curr_apu_op_fsub        =    {APU_OP_FSUB};
            bins curr_apu_op_fsgnj_se    =    {APU_OP_FSGNJ_SE};
            bins curr_apu_op_f2i_u       =    {APU_OP_F2I_U};
            bins curr_apu_op_i2f_u       =    {APU_OP_I2F_U};
            option.weight = 5;
        }

        //cross coverage for F-inst in ID-stage with preceeding F-multicycle instr
        cr_f_inst_at_id_stage_inp_with_fpu_multicycle_req : cross cp_id_stage_inst_valid, cp_id_stage_f_inst, cp_apu_req_valid, cp_apu_grant_valid, cp_curr_fpu_apu_op {option.weight = 50;}

        //cross coverage for F-inst in ID-stage with preceeding F-multicycle - case with apu_busy or APU needing more than 1 clock cycle 
        cr_f_inst_at_id_stage_inp_while_fpu_busy : cross cp_id_stage_inst_valid, cp_id_stage_f_inst, cp_apu_busy, cp_curr_fpu_apu_op {
            option.weight = 50;
`ifdef FPU_LAT_0_CYC
            //For FPU config with Latency=0 , apu_busy is expected to be set only for FDIV and FSQRT case  
            illegal_bins apu_busy_curr_apu_op_not_div_sqrt = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (binsof(cp_apu_busy) intersect{1});
`endif
        }
        
        //cross coverage for F-inst arriving at ID-stage input at various stages of APU latency clk-cycles of the ongoing/preceeding F-multicycle instr
        cr_f_inst_at_id_stage_inp_with_cyc_window_of_ongoing_fpu_calc : cross cp_id_stage_inst_valid, cp_id_stage_f_inst, cp_f_multicycle_clk_window, cp_curr_fpu_apu_op {
            option.weight = 50;
`ifdef FPU_LAT_0_CYC
            illegal_bins clk_2_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1});
`elsif FPU_LAT_1_CYC
            illegal_bins clk_3_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2});
`elsif FPU_LAT_2_CYC
            illegal_bins clk_4_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2, 3});
`elsif FPU_LAT_3_CYC
            illegal_bins clk_5_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2, 3, 4});
`elsif FPU_LAT_4_CYC
            illegal_bins clk_6_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2, 3, 4, 5});
`endif
        }

        //cross coverage for F-inst at ID-stage output with preceeding F-multicycle instr
        //Note: Added 2 separate similar cross coverages ID stage because of different arrival times of next instruction w.r.t APU Req
        cr_f_inst_at_id_stage_out_with_fpu_multicycle_req : cross cp_id_stage_apu_en_ex_o, cp_id_stage_apu_op_ex_o, cp_apu_req_valid, cp_apu_grant_valid, cp_curr_fpu_apu_op {option.weight = 50;}

        //cross coverage for F-inst at ID-stage output with preceeding F-multicycle - case with apu_busy or APU needing more than 1 clock cycle 
        //Note: Added 2 separate similar cross coverages ID stage because of different arrival times of next instruction w.r.t APU Req
        cr_f_inst_at_id_stage_out_while_fpu_busy : cross cp_id_stage_apu_en_ex_o, cp_id_stage_apu_op_ex_o, cp_apu_busy, cp_curr_fpu_apu_op {
            option.weight = 50;
`ifdef FPU_LAT_0_CYC
            illegal_bins apu_busy_curr_apu_op_not_div_sqrt = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (binsof(cp_apu_busy) intersect{1});
`endif
        }

        //cross coverage for F-inst arriving at ID-stage output at various stages of APU latency clk-cycles of the ongoing/preceeding F-multicycle instr
        //Note: Added 2 separate similar cross coverages ID stage because of different arrival times of next instruction w.r.t APU Req
        cr_f_inst_at_id_stage_out_with_cyc_window_of_ongoing_fpu_calc : cross cp_id_stage_apu_en_ex_o, cp_id_stage_apu_op_ex_o, cp_f_multicycle_clk_window, cp_curr_fpu_apu_op {
            option.weight = 50;
`ifdef FPU_LAT_0_CYC
            illegal_bins clk_2_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1});
`elsif FPU_LAT_1_CYC
            illegal_bins clk_3_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2});
`elsif FPU_LAT_2_CYC
            illegal_bins clk_4_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2, 3});
`elsif FPU_LAT_3_CYC
            illegal_bins clk_5_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2, 3, 4});
`elsif FPU_LAT_4_CYC
            illegal_bins clk_6_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2, 3, 4, 5});
`endif
        }

        //cross coverage for F-inst at IF-stage with preceeding F-multicycle instr
        cr_f_inst_at_if_stage_inp_with_fpu_multicycle_req : cross cp_if_stage_inst_valid, cp_if_stage_f_inst, cp_apu_req_valid, cp_apu_grant_valid, cp_curr_fpu_apu_op {option.weight = 50;}

        //cross coverage for F-inst at IF-stage with preceeding F-multicycle - case with apu_busy or APU needing more than 1 clock cycle 
        cr_f_inst_at_if_stage_inp_while_fpu_busy : cross cp_if_stage_inst_valid, cp_if_stage_f_inst, cp_apu_busy, cp_curr_fpu_apu_op {
            option.weight = 50;
`ifdef FPU_LAT_0_CYC
            illegal_bins apu_busy_curr_apu_op_not_div_sqrt = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (binsof(cp_apu_busy) intersect{1});
`endif
        }

        //cross coverage for F-inst arriving at IF-stage output at various stages of APU latency clk-cycles of the ongoing/preceeding F-multicycle instr
        cr_f_inst_at_if_stage_inp_with_cyc_window_of_ongoing_fpu_calc : cross cp_if_stage_inst_valid, cp_if_stage_f_inst, cp_f_multicycle_clk_window, cp_curr_fpu_apu_op {
            option.weight = 50;
`ifdef FPU_LAT_0_CYC
            illegal_bins clk_2_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1});
`elsif FPU_LAT_1_CYC
            illegal_bins clk_3_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2});
`elsif FPU_LAT_2_CYC
            illegal_bins clk_4_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2, 3});
`elsif FPU_LAT_3_CYC
            illegal_bins clk_5_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2, 3, 4});
`elsif FPU_LAT_4_CYC
            illegal_bins clk_6_12_group_NON_DIVSQRT  = (!binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT}) && (!binsof(cp_f_multicycle_clk_window) intersect {1, 2, 3, 4, 5});
`endif
        }

    endgroup : cg_f_multicycle

    
    covergroup cg_f_inst_reg;
        `per_instance_fcov

        cp_apu_req_valid : coverpoint cntxt.cov_vif.mon_cb.apu_req {
            bins apu_req_valid = {1'b1};
            option.weight = 1;
        }

        cp_apu_grant_valid : coverpoint cntxt.cov_vif.mon_cb.apu_gnt {
            bins apu_gnt_valid = {1'b1};
            option.weight = 1;
        }

        cp_apu_busy : coverpoint cntxt.cov_vif.mon_cb.apu_busy {
            bins apu_busy_high = {1'b1};
            option.weight = 1;
        }

        cp_id_inst_valid : coverpoint cntxt.cov_vif.mon_cb.id_stage_instr_valid_i {
            bins id_stage_instr_valid = {1};
            option.weight = 1;
        }

        cp_curr_fpu_apu_op : coverpoint cntxt.cov_vif.o_curr_fpu_apu_op_if {
            bins curr_apu_op_fmadd       =    {APU_OP_FMADD};
            bins curr_apu_op_fnmsub      =    {APU_OP_FNMSUB};
            bins curr_apu_op_fadd        =    {APU_OP_FADD};
            bins curr_apu_op_fmul        =    {APU_OP_FMUL};
            bins curr_apu_op_fdiv        =    {APU_OP_FDIV};
            bins curr_apu_op_fsqrt       =    {APU_OP_FSQRT};
            bins curr_apu_op_fsgnj       =    {APU_OP_FSGNJ};
            bins curr_apu_op_fminmax     =    {APU_OP_FMINMAX};
            bins curr_apu_op_fcmp        =    {APU_OP_FCMP};
            bins curr_apu_op_fclassify   =    {APU_OP_FCLASSIFY};
            bins curr_apu_op_f2f         =    {APU_OP_F2F};
            bins curr_apu_op_f2i         =    {APU_OP_F2I};
            bins curr_apu_op_i2f         =    {APU_OP_I2F};
            bins curr_apu_op_fmsub       =    {APU_OP_FMSUB};
            bins curr_apu_op_fnmadd      =    {APU_OP_FNMADD};
            bins curr_apu_op_fsub        =    {APU_OP_FSUB};
            bins curr_apu_op_fsgnj_se    =    {APU_OP_FSGNJ_SE};
            bins curr_apu_op_f2i_u       =    {APU_OP_F2I_U};
            bins curr_apu_op_i2f_u       =    {APU_OP_I2F_U};
            option.weight = 5;
        }

        cp_id_stage_f_inst : coverpoint cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i {
            wildcard bins id_fadd = {cv32e40p_tracer_pkg::INSTR_FADD};
            wildcard bins id_fsub = {cv32e40p_tracer_pkg::INSTR_FSUB};
            wildcard bins id_fmul = {cv32e40p_tracer_pkg::INSTR_FMUL};
            wildcard bins id_fdiv = {cv32e40p_tracer_pkg::INSTR_FDIV};
            wildcard bins id_fsqrt = {cv32e40p_tracer_pkg::INSTR_FSQRT};
            wildcard bins id_fsgnjs = {cv32e40p_tracer_pkg::INSTR_FSGNJS};
            wildcard bins id_fsgnjns = {cv32e40p_tracer_pkg::INSTR_FSGNJNS};
            wildcard bins id_fsgnjxs = {cv32e40p_tracer_pkg::INSTR_FSGNJXS};
            wildcard bins id_fmin = {cv32e40p_tracer_pkg::INSTR_FMIN};
            wildcard bins id_fmax = {cv32e40p_tracer_pkg::INSTR_FMAX};
            wildcard bins id_fcvtws = {cv32e40p_tracer_pkg::INSTR_FCVTWS};
            wildcard bins id_fcvtwus = {cv32e40p_tracer_pkg::INSTR_FCVTWUS};
            wildcard bins id_fmvxs = {cv32e40p_tracer_pkg::INSTR_FMVXS};
            wildcard bins id_feqs = {cv32e40p_tracer_pkg::INSTR_FEQS};
            wildcard bins id_flts = {cv32e40p_tracer_pkg::INSTR_FLTS};
            wildcard bins id_fles = {cv32e40p_tracer_pkg::INSTR_FLES};
            wildcard bins id_fclass = {cv32e40p_tracer_pkg::INSTR_FCLASS};
            wildcard bins id_fcvtsw = {cv32e40p_tracer_pkg::INSTR_FCVTSW};
            wildcard bins id_fcvtswu = {cv32e40p_tracer_pkg::INSTR_FCVTSWU};
            wildcard bins id_fmvsw = {cv32e40p_tracer_pkg::INSTR_FMVSX};
            wildcard bins id_fmadd = {cv32e40p_tracer_pkg::INSTR_FMADD};
            wildcard bins id_fmsub = {cv32e40p_tracer_pkg::INSTR_FMSUB};
            wildcard bins id_fnmsub = {cv32e40p_tracer_pkg::INSTR_FNMSUB};
            wildcard bins id_fnmadd = {cv32e40p_tracer_pkg::INSTR_FNMADD};
            option.weight = 5;
        }

        cp_id_f_inst_fs1 : coverpoint cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i[19:15] {
            bins fs1[] = {[0:31]};
            option.weight = 1;
        }
        cp_id_f_inst_fs2 : coverpoint cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i[24:20] {
            bins fs2[] = {[0:31]};
            option.weight = 1;
        }
        cp_curr_fpu_inst_fd : coverpoint cntxt.cov_vif.curr_fpu_fd {
            bins fd[] = {[0:31]};
            option.weight = 1;
        }
        cp_curr_fpu_inst_rd : coverpoint cntxt.cov_vif.curr_fpu_rd {
            bins rd[] = {[0:31]};
            option.weight = 1;
        }
        cp_id_x_inst_rs1 : coverpoint cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i[19:15] {
            bins rs1[] = {[0:31]};
            option.weight = 1;
        }

        cp_fd_fs1_eq : coverpoint (cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i[19:15] == cntxt.cov_vif.curr_fpu_fd) {
            bins fd_fs1_equal = {1};
        }
        cp_fd_fs2_eq : coverpoint (cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i[24:20] == cntxt.cov_vif.curr_fpu_fd) {
            bins fd_fs2_equal = {1};
        }
        cp_rd_rs1_eq : coverpoint (cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i[19:15] == cntxt.cov_vif.curr_fpu_rd) {
            bins rd_rs1_equal = {1};
        }

//*************************************************************************************************************************************************
//      Cross Coverage description for various cases of reg-to-reg dependencies in instruction sequence with F-multicycle cases
//*************************************************************************************************************************************************

        //cross coverage for F-instructions with fd to fs1 dependency - case with APU latency greater than 1 
        cr_fd_fs1_eq_nonzero_lat : cross cp_fd_fs1_eq, cp_id_inst_valid, cp_id_stage_f_inst, cp_apu_busy, cp_curr_fpu_inst_fd, cp_curr_fpu_apu_op {
            option.weight = 50;
            ignore_bins non_fd_f_inst = binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FCMP, APU_OP_FCLASSIFY, APU_OP_F2I, APU_OP_F2I_U};
`ifdef FPU_LAT_0_CYC
            ignore_bins zero_lat_inst = !binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT};
`endif
        }

        //cross coverage for F-instructions with fd to fs2 dependency - case with APU latency greater than 1 
        cr_fd_fs2_eq_nonzero_lat : cross cp_fd_fs2_eq, cp_id_inst_valid, cp_id_stage_f_inst, cp_apu_busy, cp_curr_fpu_inst_fd, cp_curr_fpu_apu_op {
            option.weight = 50;
            ignore_bins non_fd_f_inst = binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FCMP, APU_OP_FCLASSIFY, APU_OP_F2I, APU_OP_F2I_U};
`ifdef FPU_LAT_0_CYC
            ignore_bins zero_lat_inst = !binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT};
`endif
        }

        //cross coverage for F-instructions with fd to fs1 dependency 
        cr_fd_fs1_eq_no_lat  :  cross cp_fd_fs1_eq, cp_apu_req_valid, cp_id_stage_f_inst, cp_apu_grant_valid, cp_curr_fpu_inst_fd, cp_curr_fpu_apu_op {
            option.weight = 50;
            ignore_bins non_fd_f_inst = binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FCMP, APU_OP_FCLASSIFY, APU_OP_F2I, APU_OP_F2I_U};
        }

        //cross coverage for F-instructions with fd to fs2 dependency 
        cr_fd_fs2_eq_no_lat  :  cross cp_fd_fs2_eq, cp_apu_req_valid, cp_id_stage_f_inst, cp_apu_grant_valid, cp_curr_fpu_inst_fd, cp_curr_fpu_apu_op {
            option.weight = 50;
            ignore_bins non_fd_f_inst = binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FCMP, APU_OP_FCLASSIFY, APU_OP_F2I, APU_OP_F2I_U};
        }

        //cross coverage for F-instructions with rd to rs1 dependency - case with APU latency greater than 1
        cr_rd_rs1_eq_nonzero_lat  :  cross cp_rd_rs1_eq, cp_id_inst_valid, cp_id_stage_f_inst, cp_apu_busy, cp_curr_fpu_inst_rd, cp_curr_fpu_apu_op {
            option.weight = 50;
            ignore_bins non_rd_f_inst = !binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FCMP, APU_OP_FCLASSIFY, APU_OP_F2I, APU_OP_F2I_U};
            ignore_bins non_rs_id_stage_f_inst = !binsof(cp_id_stage_f_inst) intersect {APU_OP_I2F, APU_OP_I2F_U};
`ifdef FPU_LAT_0_CYC
            ignore_bins zero_lat_inst = !binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT};
`endif
        }

        //cross coverage for F-instructions with rd to rs1 dependency 
        cr_rd_rs1_eq_no_lat  :  cross cp_rd_rs1_eq, cp_id_inst_valid, cp_id_stage_f_inst, cp_apu_req_valid, cp_apu_grant_valid, cp_curr_fpu_inst_rd, cp_curr_fpu_apu_op {
            option.weight = 50;
            ignore_bins non_rd_f_inst = !binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FCMP, APU_OP_FCLASSIFY, APU_OP_F2I, APU_OP_F2I_U};
            ignore_bins non_rs_id_stage_f_inst = !binsof(cp_id_stage_f_inst) intersect {APU_OP_I2F, APU_OP_I2F_U};
        }
        
        //TODO : need for cross with non-fpu inst in pipeline with same reg dependency?
        //cr_rd_rs1_eq_nonzero_lat  :  cross cp_rd_rs1_eq, cp_id_inst_valid, cp_apu_busy, cp_curr_fpu_inst_rd, cp_curr_fpu_apu_op {
        //    option.weight = 50;
        //    ignore_bins non_rd_f_inst = !binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FCMP, APU_OP_FCLASSIFY, APU_OP_F2I, APU_OP_F2I_U};
        //    ignore_bins zero_lat_inst = !binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT};
        //}
        //cr_rd_rs1_eq_no_lat  :  cross cp_rd_rs1_eq, cp_id_inst_valid, cp_apu_req_valid, cp_apu_grant_valid, cp_curr_fpu_inst_rd, cp_curr_fpu_apu_op {
        //    option.weight = 50;
        //    ignore_bins non_rd_f_inst = !binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FCMP, APU_OP_FCLASSIFY, APU_OP_F2I, APU_OP_F2I_U};
        //}



    endgroup : cg_f_inst_reg

    covergroup cg_zfinx_inst_reg;
        `per_instance_fcov

        cp_apu_req_valid : coverpoint cntxt.cov_vif.mon_cb.apu_req {
            bins apu_req_valid = {1'b1};
            option.weight = 1;
        }

        cp_apu_grant_valid : coverpoint cntxt.cov_vif.mon_cb.apu_gnt {
            bins apu_gnt_valid = {1'b1};
            option.weight = 1;
        }

        cp_apu_busy : coverpoint cntxt.cov_vif.mon_cb.apu_busy {
            bins apu_busy_high = {1'b1};
            option.weight = 1;
        }

        cp_id_inst_valid : coverpoint cntxt.cov_vif.mon_cb.id_stage_instr_valid_i {
            bins id_stage_instr_valid = {1};
            option.weight = 1;
        }

        cp_curr_fpu_apu_op : coverpoint cntxt.cov_vif.o_curr_fpu_apu_op_if {
            bins curr_apu_op_fmadd       =    {APU_OP_FMADD};
            bins curr_apu_op_fnmsub      =    {APU_OP_FNMSUB};
            bins curr_apu_op_fadd        =    {APU_OP_FADD};
            bins curr_apu_op_fmul        =    {APU_OP_FMUL};
            bins curr_apu_op_fdiv        =    {APU_OP_FDIV};
            bins curr_apu_op_fsqrt       =    {APU_OP_FSQRT};
            bins curr_apu_op_fsgnj       =    {APU_OP_FSGNJ};
            bins curr_apu_op_fminmax     =    {APU_OP_FMINMAX};
            bins curr_apu_op_fcmp        =    {APU_OP_FCMP};
            bins curr_apu_op_fclassify   =    {APU_OP_FCLASSIFY};
            bins curr_apu_op_f2f         =    {APU_OP_F2F};
            bins curr_apu_op_f2i         =    {APU_OP_F2I};
            bins curr_apu_op_i2f         =    {APU_OP_I2F};
            bins curr_apu_op_fmsub       =    {APU_OP_FMSUB};
            bins curr_apu_op_fnmadd      =    {APU_OP_FNMADD};
            bins curr_apu_op_fsub        =    {APU_OP_FSUB};
            bins curr_apu_op_fsgnj_se    =    {APU_OP_FSGNJ_SE};
            bins curr_apu_op_f2i_u       =    {APU_OP_F2I_U};
            bins curr_apu_op_i2f_u       =    {APU_OP_I2F_U};
            option.weight = 5;
        }

        cp_id_stage_f_inst : coverpoint cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i[7:0] {
            bins f_inst_opcode_in_id_stage[] = {    
                                        cv32e40p_pkg::OPCODE_OP_FP,
                                        cv32e40p_pkg::OPCODE_OP_FMADD,
                                        cv32e40p_pkg::OPCODE_OP_FMSUB,
                                        cv32e40p_pkg::OPCODE_OP_FNMSUB,
                                        cv32e40p_pkg::OPCODE_OP_FNMADD,
                                        cv32e40p_pkg::OPCODE_STORE_FP,
                                        cv32e40p_pkg::OPCODE_LOAD_FP
            };
            option.weight = 5;
        }

        cp_id_f_inst_fs1 : coverpoint cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i[19:15] {
            bins fs1[] = {[0:31]};
            option.weight = 1;
        }
        cp_id_f_inst_fs2 : coverpoint cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i[24:20] {
            bins fs2[] = {[0:31]};
            option.weight = 1;
        }
        cp_curr_fpu_inst_fd : coverpoint cntxt.cov_vif.curr_fpu_fd {
            bins fd[] = {[0:31]};
            option.weight = 1;
        }
        cp_curr_fpu_inst_rd : coverpoint cntxt.cov_vif.curr_fpu_rd {
            bins rd[] = {[0:31]};
            option.weight = 1;
        }
        cp_id_x_inst_rs1 : coverpoint cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i[19:15] {
            bins rs1[] = {[0:31]};
            option.weight = 1;
        }

        cp_rd_rs1_eq : coverpoint (cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i[19:15] == cntxt.cov_vif.curr_fpu_rd) {
            bins rd_rs1_equal = {1};
        }
        cp_rd_rs2_eq : coverpoint (cntxt.cov_vif.mon_cb.id_stage_instr_rdata_i[24:20] == cntxt.cov_vif.curr_fpu_rd) {
            bins rd_rs2_equal = {1};
        }
 
//*************************************************************************************************************************************************
//      Cross Coverage description for various cases of reg-to-reg dependencies in instruction sequence with F-multicycle cases
//*************************************************************************************************************************************************

        //cross coverage for F-instructions with rd to rs1 dependency - case with APU latency greater than 1 
        cr_rd_rs1_eq_nonzero_lat  :  cross cp_rd_rs1_eq, cp_id_inst_valid, cp_id_stage_f_inst, cp_apu_busy, cp_curr_fpu_inst_rd, cp_curr_fpu_apu_op {
            option.weight = 50;
`ifdef FPU_LAT_0_CYC
            ignore_bins zero_lat_inst = !binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT};
`endif
        }

        //cross coverage for F-instructions with rd to rs1 dependency
        cr_rd_rs1_eq_no_lat  :  cross cp_rd_rs1_eq, cp_id_inst_valid, cp_id_stage_f_inst, cp_apu_req_valid, cp_apu_grant_valid, cp_curr_fpu_inst_rd, cp_curr_fpu_apu_op {
            option.weight = 50;
        }

        //cross coverage for F-instructions with rd to rs2 dependency - case with APU latency greater than 1 
        cr_rd_rs2_eq_nonzero_lat  :  cross cp_rd_rs2_eq, cp_id_inst_valid, cp_id_stage_f_inst, cp_apu_busy, cp_curr_fpu_inst_rd, cp_curr_fpu_apu_op {
            option.weight = 50;
`ifdef FPU_LAT_0_CYC
            ignore_bins zero_lat_inst = !binsof(cp_curr_fpu_apu_op) intersect {APU_OP_FDIV, APU_OP_FSQRT};
`endif
        }
        
        //cross coverage for F-instructions with rd to rs2 dependency
        cr_rd_rs2_eq_no_lat  :  cross cp_rd_rs2_eq, cp_id_inst_valid, cp_id_stage_f_inst, cp_apu_req_valid, cp_apu_grant_valid, cp_curr_fpu_inst_rd, cp_curr_fpu_apu_op {
            option.weight = 50;
        }
        
    endgroup : cg_zfinx_inst_reg

endclass : uvme_rv32f_zfinx_covg

function uvme_rv32f_zfinx_covg::new(string name = "rv32f_zfinx_covg", uvm_component parent = null);
    super.new(name, parent);
    cg_f_multicycle = new();
`ifdef ZFINX
    cg_zfinx_inst_reg = new();
`else
    cg_f_inst_reg = new();
`endif

endfunction : new

function void uvme_rv32f_zfinx_covg::build_phase(uvm_phase phase);
    super.build_phase(phase);

    void'(uvm_config_db#(uvme_cv32e40p_cntxt_c)::get(this, "", "cntxt", cntxt));
    if (cntxt == null) begin
        `uvm_fatal("rv32f_zfinx_covg", "No cntxt object passed to model");
    end
endfunction : build_phase

task uvme_rv32f_zfinx_covg::run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("rv32f_zfinx_covg", "The RV32_F_ZFINX coverage model is running", UVM_LOW);
    fork
        sample_clk_i();
    join_none
endtask : run_phase


task uvme_rv32f_zfinx_covg::sample_clk_i();
    while (1) begin
        @(cntxt.cov_vif.mon_cb);
        cg_f_multicycle.sample();
`ifdef ZFINX
        cg_zfinx_inst_reg.sample();
`else
        cg_f_inst_reg.sample();
`endif
    end
endtask  : sample_clk_i
