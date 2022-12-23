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
 


typedef struct {
    string ins_str;
    ops_t ops[6];
    int hart;
    int issue;
    bit trap;
} ins_rv32zcbzbb_t;


covergroup c_sext_b_cg with function sample(ins_rv32zcbzbb_t ins);
    option.per_instance = 1; 
    option.comment = "Sign extend byte, 16-bit encoding";
    
    cp_illegal_inst : coverpoint get_csr_val(ins.hart, ins.issue, `SAMPLE_AFTER, "mcause", "") == `MCAUSE_ILLEGAL_INST  iff (ins.trap == 1) {
        option.comment = "Number of illegal instructions";
        bins count[]  = {1};
    }
    cp_no_trap : coverpoint ins.trap  iff (ins.trap == 0) {
        option.comment = "Unexpected execution without trap";
        option.weight = 0;
        illegal_bins trap  = {0};
    }
endgroup

covergroup c_zext_h_cg with function sample(ins_rv32zcbzbb_t ins);
    option.per_instance = 1; 
    option.comment = "Zero extend halfword, 16-bit encoding";
    
    cp_illegal_inst : coverpoint get_csr_val(ins.hart, ins.issue, `SAMPLE_AFTER, "mcause", "") == `MCAUSE_ILLEGAL_INST  iff (ins.trap == 1) {
        option.comment = "Number of illegal instructions";
        bins count[]  = {1};
    }
    cp_no_trap : coverpoint ins.trap  iff (ins.trap == 0) {
        option.comment = "Unexpected execution without trap";
        option.weight = 0;
        illegal_bins trap  = {0};
    }
endgroup

covergroup c_sext_h_cg with function sample(ins_rv32zcbzbb_t ins);
    option.per_instance = 1; 
    option.comment = "Sign extend halfword, 16-bit encoding";
    
    cp_illegal_inst : coverpoint get_csr_val(ins.hart, ins.issue, `SAMPLE_AFTER, "mcause", "") == `MCAUSE_ILLEGAL_INST  iff (ins.trap == 1) {
        option.comment = "Number of illegal instructions";
        bins count[]  = {1};
    }
    cp_no_trap : coverpoint ins.trap  iff (ins.trap == 0) {
        option.comment = "Unexpected execution without trap";
        option.weight = 0;
        illegal_bins trap  = {0};
    }
endgroup


function ins_rv32zcbzbb_t get_rv32zcbzbb_inst(bit trap, int hart, int issue, string disass); // break and move this first bit out
    string insbin, ins_str, op[6], key, val;
    ins_rv32zcbzbb_t ins;
    int num, i, j;
    string s = disass;
    foreach (disass[c]) begin
        s[c] = (disass[c] == ",")? " " : disass[c];
    end
    ins.hart = hart;
    ins.issue = issue;
    ins.trap = trap;
    num = $sscanf (s, "%s %s %s %s %s %s %s %s", insbin, ins_str, op[0], op[1], op[2], op[3], op[4], op[5]);
    ins.ins_str = ins_str;
    for (i=0; i<num-2; i++) begin
        key = op[i];
        ins.ops[i].key=op[i]; // in case we dont update it as an indexed
        ins.ops[i].val=""; // not used
        for (j = 0; j < key.len(); j++) begin // if indexed addressing, convert offset(rs1) to op[i].key=rs1 op[i+1].key=offset
            if (key[j] == "(") begin
                ins.ops[i].key = key.substr(0,j-1); // offset
                ins.ops[i+1].key = key.substr(j+1,key.len()-2);
                i++; // step over +1
                //$display("indirect ins_str(%s) op[0](%0s).key(%s) op[1](%s).key(%s) op[2](%s).key(%s) op[3](%s).key(%s)", 
                //    ins_str, op[0], ins.ops[0].key, op[1], ins.ops[1].key, op[2], ins.ops[2].key, op[3], ins.ops[3].key);
                break;
            end
        end
    end
    for (i=0; i<num-2; i++) begin
        if (ins.ops[i].key[0] == "x") begin
            int idx = get_gpr_num(ins.ops[i].key);
            //$display("SAMPLE: %0s op[%0d]=%0s gpr(%0d)", ins_str,i, ins.ops[i].key, idx);
            if (idx < 0) begin
                ins.ops[i].val = ins.ops[i].key; // it is an immed already there
            end else begin
                ins.ops[i].val = string'(this.rvvi.x_wdata[hart][issue][idx]);
            end
        end else begin
            ins.ops[i].val = ins.ops[i].key;
        end       
    end
    return ins;
endfunction

function void rv32zcbzbb_sample(string inst_name, bit trap, int hart, int issue, string disass);
    case (inst_name)
        "c.sext.b"     : begin ins_rv32zcbzbb_t ins = get_rv32zcbzbb_inst(trap, hart, issue, disass); c_sext_b_cg.sample(ins); end
        "c.zext.h"     : begin ins_rv32zcbzbb_t ins = get_rv32zcbzbb_inst(trap, hart, issue, disass); c_zext_h_cg.sample(ins); end
        "c.sext.h"     : begin ins_rv32zcbzbb_t ins = get_rv32zcbzbb_inst(trap, hart, issue, disass); c_sext_h_cg.sample(ins); end
    endcase
endfunction


