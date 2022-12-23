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
 
// Check that only one COVER_BASE_* is set
`ifdef COVER_BASE_RV32I
    `define COVER_XLEN 32
    `ifdef COVER_BASE_RV32E
        $fatal("Cannot select both COVER_BASE_RV32I and COVER_BASE_RV32E!");
    `else 
       `ifdef COVER_BASE_RV64I
          $fatal("Cannot select both COVER_BASE_RV32I and COVER_BASE_RV64I!");
        `endif
    `endif
`else 
    `ifdef COVER_BASE_RV32E
        `define COVER_XLEN 32
        `ifdef COVER_BASE_RV64I
            $fatal("Cannot select both COVER_BASE_RV32E and COVER_BASE_RV64I!");
        `endif
    `else 
        `define COVER_XLEN 64
        `ifndef COVER_BASE_RV64I
            $fatal("No Base ISA (COVER_BASE_*) selected!");
        `endif
    `endif
`endif

`ifdef COVER_LEVEL_COMPL_BAS
`endif
`ifdef COVER_LEVEL_COMPL_EXT
  `ifndef COVER_LEVEL_COMPL_BAS
    `define COVER_LEVEL_COMPL_BAS
  `endif
`endif
`ifdef COVER_LEVEL_DV_UP_BAS
  `ifndef COVER_LEVEL_COMPL_BAS
    `define COVER_LEVEL_COMPL_BAS
  `endif
  `ifndef COVER_LEVEL_COMPL_EXT
    `define COVER_LEVEL_COMPL_EXT
  `endif
`endif
`ifdef COVER_LEVEL_DV_UP_EXT
  `ifndef COVER_LEVEL_COMPL_BAS
    `define COVER_LEVEL_COMPL_BAS
  `endif
  `ifndef COVER_LEVEL_COMPL_EXT
    `define COVER_LEVEL_COMPL_EXT
  `endif
  `ifndef COVER_LEVEL_DV_UP_BAS
    `define COVER_LEVEL_DV_UP_BAS
  `endif
`endif
`ifdef COVER_LEVEL_DV_PR_BAS
  `ifndef COVER_LEVEL_COMPL_BAS
    `define COVER_LEVEL_COMPL_BAS
  `endif
  `ifndef COVER_LEVEL_COMPL_EXT
    `define COVER_LEVEL_COMPL_EXT
  `endif
  `ifndef COVER_LEVEL_DV_UP_BAS
    `define COVER_LEVEL_DV_UP_BAS
  `endif
  `ifndef COVER_LEVEL_DV_UP_EXT
    `define COVER_LEVEL_DV_UP_EXT
  `endif
`endif
`ifdef COVER_LEVEL_DV_PR_EXT
  `ifndef COVER_LEVEL_COMPL_BAS
    `define COVER_LEVEL_COMPL_BAS
  `endif
  `ifndef COVER_LEVEL_COMPL_EXT
    `define COVER_LEVEL_COMPL_EXT
  `endif
  `ifndef COVER_LEVEL_DV_UP_BAS
    `define COVER_LEVEL_DV_UP_BAS
  `endif
  `ifndef COVER_LEVEL_DV_UP_EXT
    `define COVER_LEVEL_DV_UP_EXT
  `endif
  `ifndef COVER_LEVEL_DV_PR_BAS
    `define COVER_LEVEL_DV_PR_BAS
  `endif
`endif

`define SAMPLE_BEFORE 0
`define SAMPLE_AFTER 1
`define MCAUSE_ILLEGAL_INST 2

typedef struct { 
    string key;
    string val;
} ops_t;

typedef enum {
    x0,
    x1,
    x2,
    x3,
    x4,
    x5,
    x6,
    x7,
    x8,
    x9,
    x10,
    x11,
    x12,
    x13,
    x14,
    x15
`ifndef COVER_BASE_RV32E
    ,
    x16,
    x17,
    x18,
    x19,
    x20,
    x21,
    x22,
    x23,
    x24,
    x25,
    x26,
    x27,
    x28,
    x29,
    x30,
    x31
`endif
} gpr_name_t;

typedef enum {
    c_x8,
    c_x9,
    c_x10,
    c_x11,
    c_x12,
    c_x13,
    c_x14,
    c_x15
} gpr_reduced_name_t;

typedef enum {
    f0,
    f1,
    f2,
    f3,
    f4,
    f5,
    f6,
    f7,
    f8,
    f9,
    f10,
    f11,
    f12,
    f13,
    f14,
    f15,
    f16,
    f17,
    f18,
    f19,
    f20,
    f21,
    f22,
    f23,
    f24,
    f25,
    f26,
    f27,
    f28,
    f29,
    f30,
    f31
} fpr_name_t;

typedef enum {
    c_f8,
    c_f9,
    c_f10,
    c_f11,
    c_f12,
    c_f13,
    c_f14,
    c_f15
} fpr_reduced_name_t;

typedef enum {
        s0,
        s1,
        s2,
        s3,
        s4,
        s5,
        s6,
        s7
    } sreg_name_t;

typedef enum {
    c_ra = 4,
    c_ra_s0,
    c_ra_s0_s1,
    c_ra_s0_s2,
    c_ra_s0_s3,
    c_ra_s0_s4,
    c_ra_s0_s5,
    c_ra_s0_s6,
    c_ra_s0_s7,
    c_ra_s0_s8,
    c_ra_s0_s9,
    c_ra_s0_s11
} stack_reg_list_t;

function stack_reg_list_t get_sreg_list (string key); 
    case (key)
        "{ra}":    return c_ra;
        "{ra,s0}": return c_ra_s0;
        "{ra,s0-s1}": return c_ra_s0_s1;
        "{ra,s0-s2}": return c_ra_s0_s2;
        "{ra,s0-s3}": return c_ra_s0_s3;
        "{ra,s0-s4}": return c_ra_s0_s4;
        "{ra,s0-s5}": return c_ra_s0_s5;
        "{ra,s0-s6}": return c_ra_s0_s6;
        "{ra,s0-s7}": return c_ra_s0_s7;
        "{ra,s0-s8}": return c_ra_s0_s8;
        "{ra,s0-s9}": return c_ra_s0_s9;
        "{ra,s0-s11}": return c_ra_s0_s11;
        default: begin
            $display("ERROR: SystemVerilog Functional Coverage: get_sreg_list(%0s) not found sreg list", key);
            $finish(-1);
        end
    endcase
endfunction

function gpr_name_t get_gpr_reg (string key); 
    case (key)
        "x0": return x0;
        "x1": return x1;
        "x2": return x2;
        "x3": return x3;
        "x4": return x4;
        "x5": return x5;
        "x6": return x6;
        "x7": return x7;
        "x8": return x8;
        "x9": return x9;
        "x10": return x10;
        "x11": return x11;
        "x12": return x12;
        "x13": return x13;
        "x14": return x14;
        "x15": return x15;
`ifndef COVER_BASE_RV32E
        "x16": return x16;
        "x17": return x17;
        "x18": return x18;
        "x19": return x19;
        "x20": return x20;
        "x21": return x21;
        "x22": return x22;
        "x23": return x23;
        "x24": return x24;
        "x25": return x25;
        "x26": return x26;
        "x27": return x27;
        "x28": return x28;
        "x29": return x29;
        "x30": return x30;
        "x31": return x31;
`endif
        default: begin
            $display("ERROR: SystemVerilog Functional Coverage: get_gpr_reg(%0s) not found gpr", key);
            $finish(-1);
        end
        endcase
endfunction

function sreg_name_t get_stack_reg (string key); 
    case (key)
        "s0": return s0;
        "s1": return s1;
        "s2": return s2;
        "s3": return s3;
        "s4": return s4;
        "s5": return s5;
        "s6": return s6;
        "s7": return s7;
        default: begin
            $display("ERROR: SystemVerilog Functional Coverage: get_stack_reg(%0s) not found sreg for", key);
            $finish(-1);
        end
        endcase
endfunction

function gpr_reduced_name_t get_gpr_c_reg (string key); 
    case (key)
        "x8": return c_x8;
        "x9": return c_x9;
        "x10": return c_x10;
        "x11": return c_x11;
        "x12": return c_x12;
        "x13": return c_x13;
        "x14": return c_x14;
        "x15": return c_x15;
        default: begin
            $display("ERROR: SystemVerilog Functional Coverage: get_gpr_c_reg(%0s) not found gpr", key);
            $finish(-1);
        end
        endcase
endfunction

function int get_gpr_num(string key);
    case(key)
        "x0": return 0;
        "x1": return 1;
        "x2": return 2;
        "x3": return 3;
        "x4": return 4;
        "x5": return 5;
        "x6": return 6;
        "x7": return 7;
        "x8": return 8;
        "x9": return 9;
        "x10": return 10;
        "x11": return 11;
        "x12": return 12;
        "x13": return 13;
        "x14": return 14;
        "x15": return 15;
        "x16": return 16;
        "x17": return 17;
        "x18": return 18;
        "x19": return 19;
        "x20": return 20;
        "x21": return 21;
        "x22": return 22;
        "x23": return 23;
        "x24": return 24;
        "x25": return 25;
        "x26": return 26;
        "x27": return 27;
        "x28": return 28;
        "x29": return 29;
        "x30": return 30;
        "x31": return 31;
    endcase
    return -1;
endfunction

function fpr_name_t get_fpr_reg (string key);
    case (key)
        "f0": return f0;
        "f1": return f1;
        "f2": return f2;
        "f3": return f3;
        "f4": return f4;
        "f5": return f5;
        "f6": return f6;
        "f7": return f7;
        "f8": return f8;
        "f9": return f9;
        "f10": return f10;
        "f11": return f11;
        "f12": return f12;
        "f13": return f13;
        "f14": return f14;
        "f15": return f15;
        "f16": return f16;
        "f17": return f17;
        "f18": return f18;
        "f19": return f19;
        "f20": return f20;
        "f21": return f21;
        "f22": return f22;
        "f23": return f23;
        "f24": return f24;
        "f25": return f25;
        "f26": return f26;
        "f27": return f27;
        "f28": return f28;
        "f29": return f29;
        "f30": return f30;
        "f31": return f31;
        default: begin
            $display("ERROR: SystemVerilog Functional Coverage: get_fpr_reg(%0s) not found fpr", key);
            $finish(-1);
        end
    endcase
endfunction

function fpr_reduced_name_t get_fpr_c_reg (string key);
    case (key)
        "f8": return c_f8;
        "f9": return c_f9;
        "f10": return c_f10;
        "f11": return c_f11;
        "f12": return c_f12;
        "f13": return c_f13;
        "f14": return c_f14;
        "f15": return c_f15;
        default: begin
            $display("ERROR: SystemVerilog Functional Coverage: get_fpr_c_reg(%0s) not found fpr", key);
            $finish(-1);
        end
    endcase
endfunction

function int get_fpr_num(string key);
    case(key)
        "f0": return 0;
        "f1": return 1;
        "f2": return 2;
        "f3": return 3;
        "f4": return 4;
        "f5": return 5;
        "f6": return 6;
        "f7": return 7;
        "f8": return 8;
        "f9": return 9;
        "f10": return 10;
        "f11": return 11;
        "f12": return 12;
        "f13": return 13;
        "f14": return 14;
        "f15": return 15;
        "f16": return 16;
        "f17": return 17;
        "f18": return 18;
        "f19": return 19;
        "f20": return 20;
        "f21": return 21;
        "f22": return 22;
        "f23": return 23;
        "f24": return 24;
        "f25": return 25;
        "f26": return 26;
        "f27": return 27;
        "f28": return 28;
        "f29": return 29;
        "f30": return 30;
        "f31": return 31;
    endcase
    return -1;
endfunction

function int get_imm(string s);
    int val;
    if (s[1] == "x") begin
        s = s.substr(2,s.len()-1);
        val = s.atohex ();
    end else if (s[0] == "-") begin
        s = s.substr(1,s.len()-1);
        val = 0 - s.atoi();
    end else begin
        val = s.atoi();
    end
    return val;
endfunction

function int get_spimm(string s);
    int val;
    if (s[1] == "x") begin
        s = s.substr(2,s.len()-1);
        val = s.atohex ();
    end else if (s[0] == "-") begin
        s = s.substr(1,s.len()-1);
        val = 0 - s.atoi();
    end else begin
        val = s.atoi();
    end
    return val;
endfunction


