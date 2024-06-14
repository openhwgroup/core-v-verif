// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2024 Dolphin Design
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

// This file specifies all interfaces used by the CV32E40P test bench (uvmt_cv32e40p_tb), related to coverage.
// Most interfaces support tasks to allow control by the ENV or test cases.

`ifndef __UVMT_CV32E40P_TB_CVG_IFS_SV__
`define __UVMT_CV32E40P_TB_CVG_IFS_SV__

/**
 * ISA coverage interface
 * ISS wrapper will fill in ins (instruction) and fire ins_valid event
 */
 interface uvmt_cv32e40p_isa_covg_if;

  import uvm_pkg::*;
  import uvme_cv32e40p_pkg::*;

  event ins_valid;
  ins_t ins;

endinterface : uvmt_cv32e40p_isa_covg_if


//
//Interface for custom TB coverage component
//
  interface uvmt_cv32e40p_cov_if

    import uvm_pkg::*;
    import uvme_cv32e40p_pkg::*;
    (
      input               clk_i,
      input               rst_ni,
      input               if_stage_instr_rvalid_i,
      input  [31:0]       if_stage_instr_rdata_i,
      input               id_stage_instr_valid_i,
      input               id_stage_id_valid_o,
      input  [31:0]       id_stage_instr_rdata_i,
      input               apu_req,
      input               apu_gnt,
      input               apu_busy,
      input  [5:0]        apu_op,
      input               apu_rvalid_i,
      input               apu_perf_wb_o,
      input  [5:0]        id_stage_apu_op_ex_o,
      input               id_stage_apu_en_ex_o,
      input  [5:0]        regfile_waddr_wb_o,  // regfile write port A addr from WB stage (lsu write-back)
      input               regfile_we_wb_o,
      input  [5:0]        regfile_alu_waddr_ex_o, // regfile write port B addr from EX stage (forwarding)
      input               regfile_alu_we_ex_o,
      input               ex_mulh_active,
      input  [2:0]        ex_mult_op_ex,
      input               ex_data_misaligned_i,
      input               ex_data_misaligned_ex_i,
      input               ex_data_req_i,
      input               ex_data_rvalid_i,
      input               ex_regfile_alu_we_i,
      input               ex_apu_valid,
      input               ex_apu_rvalid_q,
      input               debug_req_i,
      input               debug_mode_q,
      input  [31:0]       dcsr_q,
      input               trigger_match_i,

      output logic[5:0]   o_curr_fpu_apu_op_if,
      output logic[5:0]   o_last_fpu_apu_op_if,
      output logic[4:0]   if_clk_cycle_window,
      output [4:0]        curr_fpu_fd,
      output [4:0]        curr_fpu_rd,
      output [5:0]        curr_rd_at_ex_regfile_wr_contention,
      output [5:0]        curr_rd_at_wb_regfile_wr_contention,
      output [5:0]        prev_rd_waddr_contention,
      output logic[1:0]   contention_state,
      output              b2b_contention,
      output              is_mulh_ex,
      output              is_misaligned_data_req_ex,
      output              is_post_inc_ld_st_inst_ex,
      output              ex_apu_valid_memorised
    );

    `ifdef FPU_ADDMUL_LAT
    parameter int FPU_LAT_1_CYC = `FPU_ADDMUL_LAT;
    `else
    parameter int FPU_LAT_1_CYC = 0;
    `endif
    parameter int MAX_FP_XACT_CYCLE = 19;

    logic [4:0]       clk_cycle_window;
    logic [5:0]       curr_fpu_apu_op_if;
    logic [5:0]       last_fpu_contention_op_if;
    logic [5:0]       prev_regfile_waddr_contention;
    logic [4:0]       regfile_waddr_wb_fd;
    logic [4:0]       regfile_alu_waddr_ex_fd;
    logic [4:0]       regfile_waddr_wb_rd;
    logic [4:0]       regfile_alu_waddr_ex_rd;
    logic [5:0]       regfile_waddr_ex_contention;
    logic [5:0]       regfile_waddr_wb_contention;
    logic [1:0]       contention_valid;
    logic             b2b_contention_valid;
    logic [31:0]      current_instr_rdata;
    logic [31:0]      previous_instr_rdata;

    initial begin
        clk_cycle_window = 0;
        curr_fpu_apu_op_if = 0;
        regfile_waddr_wb_fd = 0;
        regfile_alu_waddr_ex_fd = 0;
        regfile_waddr_wb_rd = 0;
        regfile_alu_waddr_ex_rd = 0;
        regfile_waddr_ex_contention = 0;
        regfile_waddr_wb_contention = 0;
        contention_valid = 0;
        b2b_contention_valid = 0;
    end

    clocking mon_cb @(posedge clk_i);
        default input #1step output #1ns;
        input if_stage_instr_rvalid_i;
        input if_stage_instr_rdata_i;
        input id_stage_instr_valid_i;
        input id_stage_id_valid_o;
        input id_stage_instr_rdata_i;
        input apu_req;
        input apu_gnt;
        input apu_busy;
        input apu_op;
        input apu_rvalid_i;
        input apu_perf_wb_o;
        input id_stage_apu_op_ex_o;
        input id_stage_apu_en_ex_o;
        input debug_req_i;
        input debug_mode_q;
        input trigger_match_i;
        input dcsr_q;
        inout is_mulh_ex;
        inout is_misaligned_data_req_ex;
        inout is_post_inc_ld_st_inst_ex;
        inout ex_apu_valid_memorised;
    endclocking : mon_cb

    // bhv_logic_1
    // calculate each APU operation's current clock cycle number during execution for functional coverage use
    // input(s): apu_op,
    bit detect_apu_rvalid = 1;
    bit is_apu_addr_phase = 0;
    always @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          clk_cycle_window    = 0;
          curr_fpu_apu_op_if  = 0;
          detect_apu_rvalid   = 1;
          is_apu_addr_phase   = 0;
        end
        else begin
            assert (clk_cycle_window <= MAX_FP_XACT_CYCLE)
              else `uvm_error("uvmt_cv32e40p_cov_if", $sformatf("clk_cycle_window (%0d) > MAX_FP_XACT_CYCLE (%0d)", clk_cycle_window, MAX_FP_XACT_CYCLE));
            if (apu_req && apu_gnt && apu_rvalid_i) begin : IS_0_CYC_FPU
              clk_cycle_window  = (is_apu_addr_phase) ? 1 : 0; // if b2b addr then 1
              detect_apu_rvalid = (is_apu_addr_phase) ? 0 : 1; // if b2b addr then 0
              is_apu_addr_phase = 1;
              curr_fpu_apu_op_if = apu_op;
            end
            else if (apu_req && apu_gnt && !apu_rvalid_i) begin : NOT_0_CYC_FPU
              clk_cycle_window  = 1;
              detect_apu_rvalid = 0;
              is_apu_addr_phase = 1;
              curr_fpu_apu_op_if = apu_op;
            end
            else if (apu_busy && !apu_rvalid_i && !detect_apu_rvalid) begin : FPU_MULT_CYC
              // fpu write delay should not increase the cyc cnt
              clk_cycle_window += 1;
            end
            else if (apu_busy && apu_rvalid_i && !detect_apu_rvalid) begin : DONE_FPU_CYCLE
              clk_cycle_window  = 0;
              detect_apu_rvalid = 1;
              is_apu_addr_phase = 0;
            end
            else if (!apu_busy && detect_apu_rvalid) begin
              clk_cycle_window  = 0;
            end
        end
    end

    // bhv_logic_1a
    // sample decoded instr that execute in progress
    always @(posedge clk_i or negedge rst_ni) begin
      if(!rst_ni) begin
        previous_instr_rdata <= 0;
        current_instr_rdata  <= 0;
      end
      else begin
        if (id_stage_instr_valid_i && id_stage_id_valid_o) begin
          previous_instr_rdata <= current_instr_rdata;
          current_instr_rdata  <= id_stage_instr_rdata_i;
        end
        else begin
          previous_instr_rdata <= current_instr_rdata;
        end
      end
    end

    // bhv_logic_2 (revised)
    // Model APU contention state in EX/WB for functional coverage
    // input(s): apu_perf_wb_o, regfile_waddr_wb_o, regfile_alu_waddr_ex_o
    always @(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni) begin
            contention_valid <= 0;
            b2b_contention_valid <= 0;
            last_fpu_contention_op_if <= 0;
            prev_regfile_waddr_contention <= 0;
        end
        else begin
            if (((contention_valid == 0) || (contention_valid == 2)) && (apu_perf_wb_o)) begin
              contention_valid <= 1; //set contention_valid
              b2b_contention_valid <= 0;
              last_fpu_contention_op_if <= curr_fpu_apu_op_if;
            end
            else if((contention_valid == 1) && (apu_perf_wb_o)) begin
              contention_valid <= 1; //reset contention_valid
              b2b_contention_valid <= 1;
              // if no APU execution during contention then nothing to do
              // during contention another APU transaction cannot go through
            end
            else if((contention_valid == 1) && (!apu_perf_wb_o)) begin
                contention_valid <= 2; //stalled write complete after contention
                b2b_contention_valid <= 1;
                if (FPU_LAT_1_CYC != 1) begin // IS_0_OR_2_CYCLAT
                  prev_regfile_waddr_contention <= regfile_alu_waddr_ex_o; // port B
                end
                else begin // IS_1_CYCLAT
                  prev_regfile_waddr_contention <= regfile_waddr_wb_o; // port A
                end
            end
            else begin
                contention_valid <= 0;
                b2b_contention_valid <= 0;
                prev_regfile_waddr_contention <= 0;
            end
        end
    end


    // bhv_logic_3
    // sample each APU operation's destination register address for functional coverage
    // input(s): apu_req, apu_busy, regfile_alu_we_ex_o, regfile_we_wb_o,  apu_rvalid_i
    always @(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni) begin
            regfile_alu_waddr_ex_fd <= 0;
            regfile_alu_waddr_ex_rd <= 0;
            regfile_waddr_wb_fd <= 0;
            regfile_waddr_wb_rd <= 0;
            regfile_waddr_wb_contention <= 0;
            regfile_waddr_ex_contention <= 0;
        end
        else begin
          if (FPU_LAT_1_CYC != 1) begin // IS_0_OR_2_CYCLAT
            //Case for FPU Latency {0,2,3,4}, with regfile write from EX stage with highest priority of APU
            if (((apu_req == 1) || (apu_busy == 1)) && (regfile_alu_we_ex_o == 1) && (apu_rvalid_i == 1)) begin
                regfile_alu_waddr_ex_fd <= (regfile_alu_waddr_ex_o - 32);
                regfile_alu_waddr_ex_rd <= (regfile_alu_waddr_ex_o < 32) ? regfile_alu_waddr_ex_o : 0;
                regfile_waddr_ex_contention <= 0;
                regfile_waddr_wb_contention <= 0;
            end
            else if ((contention_valid == 1) && (regfile_alu_we_ex_o == 1) && !apu_perf_wb_o) begin // write for stalled regfile wr at contention
                regfile_alu_waddr_ex_fd <= 0;
                regfile_alu_waddr_ex_rd <= 0;
                regfile_waddr_ex_contention <= regfile_alu_waddr_ex_o; //should not be >31, check for illegal in coverage
                regfile_waddr_wb_contention <= 0;
            end
            else begin
                regfile_alu_waddr_ex_fd <= 0;
                regfile_alu_waddr_ex_rd <= 0;
                regfile_waddr_wb_fd <= 0;
                regfile_waddr_wb_rd <= 0;
                regfile_waddr_ex_contention <= 0;
                regfile_waddr_wb_contention <= 0;
            end
          end // IS_0_OR_2_CYCLAT
          else begin // IS_1_CYCLAT
            //Case FPU Latency = 1; regfile wr from WB;LSU > priority;no LSU contention, F-inst regfile wr succeed
            if ((apu_busy == 1) && (regfile_we_wb_o == 1) && (apu_rvalid_i == 1) && (!apu_perf_wb_o)) begin
                regfile_waddr_wb_fd <= (regfile_waddr_wb_o - 32);
                regfile_waddr_wb_rd <= (regfile_waddr_wb_o < 32) ? regfile_waddr_wb_o : 0;
                regfile_waddr_ex_contention <= 0;
                regfile_waddr_wb_contention <= 0;
            end
            //Case FPU Latency = 1; regfile wr from WB;LSU > priority;LSU contention,F-inst regfile wr stall
            else if((apu_busy == 1) && (regfile_we_wb_o == 1) && (apu_rvalid_i == 1) && (apu_perf_wb_o)) begin
                regfile_waddr_wb_fd <= 0;
                regfile_waddr_wb_rd <= 0;
                regfile_waddr_ex_contention <= 0;
                regfile_waddr_wb_contention = regfile_waddr_wb_o; // contention between lsu and fpu using wb path
            end
            //Case FPU Latency = 1;regfile wr from WB;LSU > priority;LSU contention - FPU reg write cycle after contention
            else if((contention_valid == 1) && (regfile_we_wb_o == 1) && !apu_perf_wb_o) begin
                regfile_waddr_wb_fd <= (regfile_waddr_wb_o - 32);
                regfile_waddr_wb_rd <= (regfile_waddr_wb_o < 32) ? regfile_waddr_wb_o : 0;
                regfile_waddr_ex_contention <= 0;
                regfile_waddr_wb_contention <= 0;
            end
            else begin
                regfile_alu_waddr_ex_fd <= 0;
                regfile_alu_waddr_ex_rd <= 0;
                regfile_waddr_wb_fd <= 0;
                regfile_waddr_wb_rd <= 0;
                regfile_waddr_ex_contention <= 0;
                regfile_waddr_wb_contention <= 0;
            end
          end // IS_1_CYCLAT
        end
    end

    assign curr_fpu_fd = regfile_alu_waddr_ex_fd | regfile_waddr_wb_fd;
    assign curr_fpu_rd = regfile_alu_waddr_ex_rd | regfile_waddr_wb_rd;
    assign if_clk_cycle_window = clk_cycle_window;
    assign o_curr_fpu_apu_op_if = curr_fpu_apu_op_if;
    assign o_last_fpu_apu_op_if = last_fpu_contention_op_if;
    assign curr_rd_at_ex_regfile_wr_contention = regfile_waddr_ex_contention;
    assign curr_rd_at_wb_regfile_wr_contention = regfile_waddr_wb_contention;
    assign contention_state = contention_valid;
    assign b2b_contention = b2b_contention_valid;
    assign prev_rd_waddr_contention = prev_regfile_waddr_contention;
    assign is_mulh_ex = ex_mulh_active && (ex_mult_op_ex == 3'h6);
    assign is_misaligned_data_req_ex = ex_data_misaligned_i || ex_data_misaligned_ex_i;
    assign is_post_inc_ld_st_inst_ex = (ex_data_req_i || ex_data_rvalid_i) && ex_regfile_alu_we_i;
    assign ex_apu_valid_memorised = ex_apu_valid & ex_apu_rvalid_q;

  endinterface : uvmt_cv32e40p_cov_if


`endif // __UVMT_CV32E40P_TB_CVG_IFS_SV__
