// Copyright 2024 Torje Nygaard Eikenes
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0.
//
// You may obtain a copy of the License at
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef __PIPELINE_SHELL_SV__
`define __PIPELINE_SHELL_SV__

module pipeline_shell 
    import uvma_rvfi_pkg::*;
    import iss_wrap_pkg::*;
    (
        uvma_clknrst_if_t clknrst_if,
        uvma_rvfi_instr_if_t rvfi_i,
        uvma_interrupt_if_t interrupt_if_i,
        logic debug_req_i,
        rvfi_if_t rvfi_o
    );

    pipe_stage_t if_id_pipe;
    pipe_stage_t id_ex_pipe;
    pipe_stage_t ex_wb_pipe;
    pipe_stage_t wb_pipe;
    logic if_step;
    logic id_step;
    logic ex_step;
    logic wb_step;
    logic if_flush;
    logic id_flush;
    logic ex_flush;
    logic wb_flush;
    logic interrupt_allowed;
    logic interrupt_taken;

    controller controller_i(
        .clk                    (clknrst_if.clk     ),
        .rst_n                  (clknrst_if.reset_n ),
        .valid                  (rvfi_i.rvfi_valid  ),
        .irq_i                  (interrupt_if_i.irq ),
        .debug_req_i            (debug_req_i        ),
        .if_id_pipe_i           (if_id_pipe         ),
        .id_ex_pipe_i           (id_ex_pipe         ),
        .ex_wb_pipe_i           (ex_wb_pipe         ),
        .wb_pipe_i              (wb_pipe            ),
        .if_step_o              (if_step            ),
        .id_step_o              (id_step            ),
        .ex_step_o              (ex_step            ),
        .wb_step_o              (wb_step            ),
        .if_flush_o             (if_flush           ),
        .id_flush_o             (id_flush           ),
        .ex_flush_o             (ex_flush           ),
        .wb_flush_o             (wb_flush           )
    );

    if_stage if_stage_i(
        .clk            (clknrst_if.clk     ),
        .rst_n          (clknrst_if.reset_n ),
        .step           (if_step            ),
        .flush_i        (if_flush           ),
        .if_id_pipe_o   (if_id_pipe         )
        );
    
    id_stage id_stage_i(
        .clk            (clknrst_if.clk     ),
        .rst_n          (clknrst_if.reset_n ),
        .step           (id_step            ),
        .flush_i        (id_flush           ),
        .pipe_i         (if_id_pipe         ),
        .pipe_o         (id_ex_pipe         )
    );

    ex_stage ex_stage_i(
        .clk            (clknrst_if.clk     ),
        .rst_n          (clknrst_if.reset_n ),
        .step           (ex_step            ),
        .flush_i        (ex_flush           ),
        .pipe_i         (id_ex_pipe         ),
        .pipe_o         (ex_wb_pipe         )
    );

    wb_stage wb_stage_i(
        .clk            (clknrst_if.clk     ),
        .rst_n          (clknrst_if.reset_n ),
        .step           (wb_step            ),
        .flush_i        (wb_flush           ),
        .pipe_i         (ex_wb_pipe         ),
        .pipe_o         (wb_pipe            )
    );



    always_comb begin
        rvfi_o.clk          <= clknrst_if.clk;
        rvfi_o.valid        <= wb_pipe.valid;
        rvfi_o.order        <= wb_pipe.rvfi.order;
        rvfi_o.insn         <= wb_pipe.rvfi.insn;
        rvfi_o.trap         <= wb_pipe.rvfi.trap;
        rvfi_o.halt         <= wb_pipe.rvfi.halt;
        rvfi_o.dbg          <= wb_pipe.rvfi.dbg;
        rvfi_o.dbg_mode     <= wb_pipe.rvfi.dbg_mode;
        rvfi_o.nmip         <= wb_pipe.rvfi.nmip;
        rvfi_o.intr         <= wb_pipe.rvfi.intr;
        rvfi_o.mode         <= wb_pipe.rvfi.mode;
        rvfi_o.ixl          <= wb_pipe.rvfi.ixl;
        rvfi_o.pc_rdata     <= wb_pipe.rvfi.pc_rdata;
        rvfi_o.pc_wdata     <= wb_pipe.rvfi.pc_wdata;
        rvfi_o.rs1_addr     <= wb_pipe.rvfi.rs1_addr;
        rvfi_o.rs1_rdata    <= wb_pipe.rvfi.rs1_rdata;
        rvfi_o.rs2_addr     <= wb_pipe.rvfi.rs2_addr;
        rvfi_o.rs2_rdata    <= wb_pipe.rvfi.rs2_rdata;
        rvfi_o.rs3_addr     <= wb_pipe.rvfi.rs3_addr;
        rvfi_o.rs3_rdata    <= wb_pipe.rvfi.rs3_rdata;
        rvfi_o.rd1_addr     <= wb_pipe.rvfi.rd1_addr;
        rvfi_o.rd1_wdata    <= wb_pipe.rvfi.rd1_wdata;
        rvfi_o.rd2_addr     <= wb_pipe.rvfi.rd2_addr;
        rvfi_o.rd2_wdata    <= wb_pipe.rvfi.rd2_wdata;
        rvfi_o.mem_addr     <= wb_pipe.rvfi.mem_addr;
        rvfi_o.mem_rdata    <= wb_pipe.rvfi.mem_rdata;
        rvfi_o.mem_rmask    <= wb_pipe.rvfi.mem_rmask;
        rvfi_o.mem_wdata    <= wb_pipe.rvfi.mem_wdata;
        rvfi_o.mem_wmask    <= wb_pipe.rvfi.mem_wmask;
    end

endmodule //pipeline_shell

`endif //__PIPELINE_SHELL_SV__
