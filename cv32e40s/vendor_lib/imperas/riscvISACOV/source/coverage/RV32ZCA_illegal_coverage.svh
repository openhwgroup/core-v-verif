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
} ins_rv32zca_t;


covergroup c_add_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_mv_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_addi_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_addi16sp_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
endgroup

covergroup c_addi4spn_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
endgroup

covergroup c_li_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_lui_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_and_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_or_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_sub_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_xor_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_andi_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_beqz_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_bnez_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_j_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_jal_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_jalr_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_jr_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_lw_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_lwsp_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_slli_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_srai_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_srli_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_sw_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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

covergroup c_swsp_cg with function sample(ins_rv32zca_t ins);
    option.per_instance = 1; 
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


function ins_rv32zca_t get_rv32zca_inst(bit trap, int hart, int issue, string disass); // break and move this first bit out
    string insbin, ins_str, op[6], key, val;
    ins_rv32zca_t ins;
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

function void rv32zca_sample(string inst_name, bit trap, int hart, int issue, string disass);
    case (inst_name)
        "c.add"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_add_cg.sample(ins); end
        "c.mv"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_mv_cg.sample(ins); end
        "c.addi"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_addi_cg.sample(ins); end
        "c.addi16sp"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_addi16sp_cg.sample(ins); end
        "c.addi4spn"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_addi4spn_cg.sample(ins); end
        "c.li"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_li_cg.sample(ins); end
        "c.lui"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_lui_cg.sample(ins); end
        "c.and"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_and_cg.sample(ins); end
        "c.or"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_or_cg.sample(ins); end
        "c.sub"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_sub_cg.sample(ins); end
        "c.xor"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_xor_cg.sample(ins); end
        "c.andi"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_andi_cg.sample(ins); end
        "c.beqz"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_beqz_cg.sample(ins); end
        "c.bnez"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_bnez_cg.sample(ins); end
        "c.j"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_j_cg.sample(ins); end
        "c.jal"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_jal_cg.sample(ins); end
        "c.jalr"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_jalr_cg.sample(ins); end
        "c.jr"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_jr_cg.sample(ins); end
        "c.lw"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_lw_cg.sample(ins); end
        "c.lwsp"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_lwsp_cg.sample(ins); end
        "c.slli"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_slli_cg.sample(ins); end
        "c.srai"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_srai_cg.sample(ins); end
        "c.srli"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_srli_cg.sample(ins); end
        "c.sw"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_sw_cg.sample(ins); end
        "c.swsp"     : begin ins_rv32zca_t ins = get_rv32zca_inst(trap, hart, issue, disass); c_swsp_cg.sample(ins); end
    endcase
endfunction


