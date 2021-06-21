// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
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


class uvma_isacov_mon_c extends uvm_monitor;

  `uvm_component_utils(uvma_isacov_mon_c);

  uvma_isacov_cntxt_c                        cntxt;
  uvm_analysis_port #(uvma_isacov_mon_trn_c) ap;
  instr_name_t                               instr_name_lookup[string];

  extern function new(string name = "uvma_isacov_mon", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);  

  extern task sample_instr();

endclass : uvma_isacov_mon_c


function uvma_isacov_mon_c::new(string name = "uvma_isacov_mon", uvm_component parent = null);

  super.new(name, parent);

endfunction : new


function void uvma_isacov_mon_c::build_phase(uvm_phase phase);

  instr_name_t in;

  super.build_phase(phase);

  void'(uvm_config_db#(uvma_isacov_cntxt_c)::get(this, "", "cntxt", cntxt));
  if (!cntxt) begin
    `uvm_fatal("CNTXT", "Context handle is null")
  end

  ap = new("ap", this);
  
  dasm_set_config(32, "rv32imc", 0);

  in = in.first;
  repeat(in.num) begin
    instr_name_lookup[in.name().tolower()] = in;
    in = in.next;
  end  

endfunction : build_phase


task uvma_isacov_mon_c::run_phase(uvm_phase phase);

  forever sample_instr();

endtask : run_phase

task uvma_isacov_mon_c::sample_instr();

  uvma_isacov_mon_trn_c mon_trn;
  string                instr_name;
  bit [63:0]            instr;

  @(cntxt.vif.retire);

  mon_trn = uvma_isacov_mon_trn_c::type_id::create("mon_trn");
  mon_trn.instr = uvma_isacov_instr_c::type_id::create("mon_instr");

  instr_name = dasm_name(cntxt.vif.instr);
  if (instr_name_lookup.exists(instr_name)) begin
    mon_trn.instr.name = instr_name_lookup[instr_name];    
  end else begin
    mon_trn.instr.name = UNKNOWN;
    `uvm_warning("ISACOVMON", $sformatf("error couldn't look up '%s'", instr_name));
  end
  
  mon_trn.instr.itype = get_instr_type(mon_trn.instr.name);
  mon_trn.instr.group = get_instr_group(mon_trn.instr.name);

  instr = $signed(cntxt.vif.instr);  // dpi_dasm expects even 32-bit words as 64 bits

  mon_trn.instr.rs1  = dasm_rs1(instr);
  mon_trn.instr.rs2  = dasm_rs2(instr);
  mon_trn.instr.rd   = dasm_rd(instr);
  mon_trn.instr.immi = dasm_i_imm(instr);
  mon_trn.instr.imms = dasm_s_imm(instr);
  mon_trn.instr.immb = dasm_sb_imm(instr) >> 1;
  mon_trn.instr.immu = dasm_u_imm(instr) >> 12;
  mon_trn.instr.immj = dasm_uj_imm(instr);
  
  mon_trn.instr.c_immj = dasm_rvc_j_imm(instr);
  mon_trn.instr.c_rs1p = instr[9:7];  // TODO use disassembler
  mon_trn.instr.c_rdp = instr[4:2];  // TODO use disassembler
  // TODO make sure RVC instrs don't arrive as decompressed instrs
  
  if (mon_trn.instr.group == CSR_GROUP) begin
    if (!$cast(mon_trn.instr.csr, dasm_csr(instr))) begin
      `uvm_warning("ISACOVMON", $sformatf("CSR: 0x%03x unmappable", dasm_csr(instr)));
    end
  end

  mon_trn.instr.set_valid_flags();

  ap.write(mon_trn);

endtask : sample_instr
