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

`ifndef __REFERENCE_MODEL_SV__
`define __REFERENCE_MODEL_SV__


module reference_model
    import iss_wrap_pkg::*;
    import uvma_rvfi_pkg::*;
    (
        uvma_clknrst_if_t clknrst_if,
        uvma_rvfi_instr_if_t rvfi_i,
        uvma_interrupt_if_t interrupt_if_i,
        logic debug_req_i,
        rvfi_if_t rvfi_o
    );

    string binary;

    initial begin
        @(clknrst_if.clk);
        if ($value$plusargs("elf_file=%s", binary))
            $display("Setting up ISS with binary %s...", binary);
        
        iss_init(binary);

        $display("Reference Model: Starting");
    end

    pipeline_shell pipeline_shell_i(
        .clknrst_if(clknrst_if),
        .rvfi_i(rvfi_i),
        .interrupt_if_i(interrupt_if_i),
        .debug_req_i(debug_req_i),
        .rvfi_o(rvfi_o)
    );

endmodule //reference_model

`endif //__REFERENCE_MODEL_SV__