//
// Copyright (c) 2022 Imperas Software Ltd., www.imperas.com
// 
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
// either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.
//
//
 
package RISCV_coverage_pkg;

`include "coverage/RISCV_coverage_common.svh"

class RISCV_coverage;

    // Todo: Copied these here for now to make a delayed csr for getting before and after values.  
    //       Look into moving these delayed/pipelined values up to rvvi or trace2cov level instead.
    parameter int ILEN   = 32;  // Instruction length in bits
    parameter int XLEN   = `COVER_XLEN;  // GPR length in bits
    parameter int FLEN   = 32;  // FPR length in bits
    parameter int VLEN   = 256; // Vector register size in bits
    parameter int NHART  = 1;   // Number of harts reported
    parameter int RETIRE = 1;    // Number of instructions that can retire during valid event

    `include "coverage/RISCV_coverage_csr.svh"

    `ifdef COVER_RV32ZCA
        `ifdef COVER_RV32ZCA_ILLEGAL
            $fatal("Cannot select both COVER_RV32ZCA and COVER_RV32ZCA_ILLEGAL");
        `endif
        `ifdef COVER_BASE_RV64I
              $fatal("Cannot use COVER_RV32ZCA with COVER_BASE_RV64I");
        `else
            `include "coverage/RV32ZCA_coverage.svh"     
        `endif
    `endif
    `ifdef COVER_RV32ZCA_ILLEGAL
        `include "coverage/RV32ZCA_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCB
        `ifdef COVER_RV32ZCB_ILLEGAL
            $fatal("Cannot select both COVER_RV32ZCB and COVER_RV32ZCB_ILLEGAL");
        `endif
        `ifdef COVER_BASE_RV64I
              $fatal("Cannot use COVER_RV32ZCB with COVER_BASE_RV64I");
        `else
            `include "coverage/RV32ZCB_coverage.svh"     
        `endif
    `endif
    `ifdef COVER_RV32ZCB_ILLEGAL
        `include "coverage/RV32ZCB_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCBZBB
        `ifdef COVER_RV32ZCBZBB_ILLEGAL
            $fatal("Cannot select both COVER_RV32ZCBZBB and COVER_RV32ZCBZBB_ILLEGAL");
        `endif
        `ifdef COVER_BASE_RV64I
              $fatal("Cannot use COVER_RV32ZCBZBB with COVER_BASE_RV64I");
        `else
            `include "coverage/RV32ZCBZBB_coverage.svh"     
        `endif
    `endif
    `ifdef COVER_RV32ZCBZBB_ILLEGAL
        `include "coverage/RV32ZCBZBB_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCBZMUL
        `ifdef COVER_RV32ZCBZMUL_ILLEGAL
            $fatal("Cannot select both COVER_RV32ZCBZMUL and COVER_RV32ZCBZMUL_ILLEGAL");
        `endif
        `ifdef COVER_BASE_RV64I
              $fatal("Cannot use COVER_RV32ZCBZMUL with COVER_BASE_RV64I");
        `else
            `include "coverage/RV32ZCBZMUL_coverage.svh"     
        `endif
    `endif
    `ifdef COVER_RV32ZCBZMUL_ILLEGAL
        `include "coverage/RV32ZCBZMUL_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCMP
        `ifdef COVER_RV32ZCMP_ILLEGAL
            $fatal("Cannot select both COVER_RV32ZCMP and COVER_RV32ZCMP_ILLEGAL");
        `endif
        `ifdef COVER_BASE_RV64I
              $fatal("Cannot use COVER_RV32ZCMP with COVER_BASE_RV64I");
        `else
            `include "coverage/RV32ZCMP_coverage.svh"     
        `endif
    `endif
    `ifdef COVER_RV32ZCMP_ILLEGAL
        `include "coverage/RV32ZCMP_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCMT
        `ifdef COVER_RV32ZCMT_ILLEGAL
            $fatal("Cannot select both COVER_RV32ZCMT and COVER_RV32ZCMT_ILLEGAL");
        `endif
        `ifdef COVER_BASE_RV64I
              $fatal("Cannot use COVER_RV32ZCMT with COVER_BASE_RV64I");
        `else
            `include "coverage/RV32ZCMT_coverage.svh"     
        `endif
    `endif
    `ifdef COVER_RV32ZCMT_ILLEGAL
        `include "coverage/RV32ZCMT_illegal_coverage.svh"
    `endif

    virtual rvviTrace #(ILEN, XLEN, FLEN, VLEN, NHART, RETIRE) rvvi;

    // Todo: Look into moving these delayed/pipelined values up to rvvi or trace2cov level instead.
    reg [4095:0][(XLEN-1):0] csr_prev        [(NHART-1):0][(RETIRE-1):0];

    

    function new(virtual rvviTrace #(ILEN, XLEN, FLEN, VLEN, NHART, RETIRE) rvvi);
   
        this.rvvi = rvvi;

    `ifdef COVER_RV32ZCA
    `include "coverage/RV32ZCA_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCA_ILLEGAL
        `include "coverage/RV32ZCA_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCB
    `include "coverage/RV32ZCB_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCB_ILLEGAL
        `include "coverage/RV32ZCB_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCBZBB
    `include "coverage/RV32ZCBZBB_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCBZBB_ILLEGAL
        `include "coverage/RV32ZCBZBB_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCBZMUL
    `include "coverage/RV32ZCBZMUL_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCBZMUL_ILLEGAL
        `include "coverage/RV32ZCBZMUL_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCMP
    `include "coverage/RV32ZCMP_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCMP_ILLEGAL
        `include "coverage/RV32ZCMP_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCMT
    `include "coverage/RV32ZCMT_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCMT_ILLEGAL
        `include "coverage/RV32ZCMT_coverage_init.svh"
    `endif


    fork
        forever @(posedge this.rvvi.clk) 
            begin
                this.csr_prev <= this.rvvi.csr;
            end
    join_none

    endfunction

    function string get_inst_name(bit trap, int hart, int issue, string disass); // break and move this first bit out
        string insbin, ins_str, ops;
        int num = $sscanf (disass, "%s %s %s", insbin, ins_str, ops);
        return ins_str;
    endfunction

    function void sample_extensions(bit trap, int hart, int issue, string disass);

        string inst_name = get_inst_name(trap, hart, issue, disass);
        
    `ifdef COVER_RV32ZCA
        rv32zca_sample(inst_name, trap, hart, issue, disass);
    `endif
    `ifdef COVER_RV32ZCA_ILLEGAL
        rv32zca_sample(inst_name, trap, hart, issue, disass);
    `endif
    `ifdef COVER_RV32ZCB
        rv32zcb_sample(inst_name, trap, hart, issue, disass);
    `endif
    `ifdef COVER_RV32ZCB_ILLEGAL
        rv32zcb_sample(inst_name, trap, hart, issue, disass);
    `endif
    `ifdef COVER_RV32ZCBZBB
        rv32zcbzbb_sample(inst_name, trap, hart, issue, disass);
    `endif
    `ifdef COVER_RV32ZCBZBB_ILLEGAL
        rv32zcbzbb_sample(inst_name, trap, hart, issue, disass);
    `endif
    `ifdef COVER_RV32ZCBZMUL
        rv32zcbzmul_sample(inst_name, trap, hart, issue, disass);
    `endif
    `ifdef COVER_RV32ZCBZMUL_ILLEGAL
        rv32zcbzmul_sample(inst_name, trap, hart, issue, disass);
    `endif
    `ifdef COVER_RV32ZCMP
        rv32zcmp_sample(inst_name, trap, hart, issue, disass);
    `endif
    `ifdef COVER_RV32ZCMP_ILLEGAL
        rv32zcmp_sample(inst_name, trap, hart, issue, disass);
    `endif
    `ifdef COVER_RV32ZCMT
        rv32zcmt_sample(inst_name, trap, hart, issue, disass);
    `endif
    `ifdef COVER_RV32ZCMT_ILLEGAL
        rv32zcmt_sample(inst_name, trap, hart, issue, disass);
    `endif
    endfunction

endclass


endpackage

