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

`ifndef __PIPELINE_SHELL_STAGE_SV__
`define __PIPELINE_SHELL_STAGE_SV__


import uvma_rvfi_pkg::*;

typedef struct packed {
    st_rvfi rvfi;
    logic valid;
} pipe_stage_t;

module if_stage
    import iss_wrap_pkg::*;
    (
        input logic clk,
        input logic rst_n,
        input logic step, 
        input logic flush_i,

        output pipe_stage_t if_id_pipe_o
    );

    always_ff @(posedge clk) begin
        if(flush_i) begin
            if_id_pipe_o.rvfi <= '0;
            if_id_pipe_o.valid <= 1'b0;
        end else if(step) begin
            if_id_pipe_o.rvfi <= iss_step();
            if_id_pipe_o.valid <= 1'b1;
        end
        else begin
            if_id_pipe_o.rvfi <= if_id_pipe_o.rvfi;
            if_id_pipe_o.valid <= if_id_pipe_o.valid;
        end
    end
endmodule

module id_stage
    import iss_wrap_pkg::*;
    (
        input logic clk,
        input logic rst_n,
        input logic step, 
        input logic flush_i,
        input pipe_stage_t pipe_i,

        output pipe_stage_t pipe_o
    );

    always_ff @(posedge clk) begin
        if (flush_i) begin
            pipe_o.rvfi <= '0;
            pipe_o.valid <= 1'b0;
        end else if(step) begin
            pipe_o.rvfi <= pipe_i.rvfi;
            pipe_o.valid <= pipe_i.valid;
        end
        else begin
            pipe_o.rvfi <= pipe_o.rvfi;
            pipe_o.valid <= pipe_o.valid;
        end
    end
endmodule

module ex_stage
    import iss_wrap_pkg::*;
    (
        input logic clk,
        input logic rst_n,
        input logic step, 
        input logic flush_i,
        input pipe_stage_t pipe_i,

        output pipe_stage_t pipe_o
    );

    always_ff @(posedge clk) begin
        if (flush_i) begin
            pipe_o.rvfi <= '0;
            pipe_o.valid <= 1'b0;
        end else if(step) begin
            pipe_o.rvfi <= pipe_i.rvfi;
            pipe_o.valid <= pipe_i.valid;
        end
        else begin
            pipe_o.rvfi <= pipe_o.rvfi;
            pipe_o.valid <= pipe_i.valid; 
        end
    end
endmodule

module wb_stage
    import iss_wrap_pkg::*;
    (
        input logic clk,
        input logic rst_n,
        input logic step, 
        input logic flush_i,
        input pipe_stage_t pipe_i,

        output pipe_stage_t pipe_o
    );

    always_ff @(posedge clk) begin
        if (flush_i) begin
            pipe_o.rvfi <= '0;
            pipe_o.valid <= 1'b0;
        end else if(step) begin
            pipe_o.rvfi <= pipe_i.rvfi;
            pipe_o.valid <= pipe_i.valid;
        end
        else begin
            pipe_o.rvfi <= pipe_o.rvfi;
            pipe_o.valid <= 1'b0; //Only output valid at first valid clock cycle
        end
    end

endmodule

`endif //__PIPELINE_SHELL_STAGE_SV__
