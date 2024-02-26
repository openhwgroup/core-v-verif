///////////////////////////////////////////////////////////////////////////////
//
// Copyright 2023 OpenHW Group
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
// SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0
//*******************************************************************************************************************************************

// Note: 
// 1) This coverage model is to replace v1 model (uvme_interrupt_covg)
// 2) all cvg have similar cvgs as defined in v1 model
// 3) It uses uvmt_cv32e40p_rvvi_if

`ifndef UVME_INTERRUPT_COVG_V2
`define UVME_INTERRUPT_COVG_V2

class uvme_interrupt_covg_v2 # (
  parameter int ILEN    = 32,
  parameter int XLEN    = 32
) extends uvm_component;

  // PROPERTIES - START
  virtual             uvmt_cv32e40p_rvvi_if #( .XLEN(XLEN), .ILEN(ILEN)) cv32e40p_rvvi_vif;

  string              _header           = "INTERRUPT_COVG_V2";
  bit                 en_cvg_sampling   = 1;
  int unsigned        irq_nested_count  = 0;
  bit                 is_irq            = 0;
  bit                 is_wfi            = 0;
  bit                 is_trap           = 0;
  logic [(ILEN-1):0]  current_insn      = '{default:0};
  logic [(ILEN-1):0]  prev_insn         = '{default:0};
  logic [(ILEN-1):0]  prev_insn_d       = '{default:0};
  // PROPERTIES - END
    
  // COVERGROUPS DEFINE HERE - START
  `define CG_INTERRUPT(EVENT) cg_``EVENT``
  `define DEF_CG_INTERRUPT(EVENT) covergroup cg_``EVENT`` (bit has_ignore_irq_entry=0, bit has_ignore_irq_exit=0) with function sample(logic [31:0] insn=32'b0); \
    option.per_instance         = 1; \
    `ifdef MODEL_TECH \
    option.get_inst_coverage    = 1; \
    `endif \
    type_option.merge_instances = 1; \
    cp_insn_list : coverpoint (insn) iff (en_cvg_sampling) { \
      wildcard bins lui     = {TB_INSTR_LUI}; \
      wildcard bins auipc   = {TB_INSTR_AUIPC}; \
      // BRANCH / JUMP \
      `JUMP_INSTR_BINS \
      `BRANCH_INSTR_BINS \
      // OPIMM -  \
      `OPIMM_INSTR_BINS \
      // OP - \
      `OP_INSTR_BINS \
      // SYSTEM - \
      wildcard bins csrrw   = {TB_INSTR_CSRRW}; \
      wildcard bins csrrs   = {TB_INSTR_CSRRS}; \
      wildcard bins csrrc   = {TB_INSTR_CSRRC}; \
      wildcard bins csrrwi  = {TB_INSTR_CSRRWI}; \
      wildcard bins csrrsi  = {TB_INSTR_CSRRSI}; \
      wildcard bins csrrci  = {TB_INSTR_CSRRCI}; \
      wildcard bins mret    = {TB_INSTR_MRET}; \
      wildcard bins dret    = {TB_INSTR_DRET}; \
      wildcard bins wfi     = {TB_INSTR_WFI}; \
      // FENCE - \
      `FENCE_INSTR_BINS \
      // RV32M - \
      `RV32M_INSTR_BINS \
      // LOAD STORE - \
      `LOAD_STORE_INSTR_BINS \
      // RV32C \
      `RV32C_INSTR_BINS \
      // RV32F/ZFINX - \
      `ifdef FPU \
        `ifdef ZFINX \
          `ZFINX_INSTR_BINS \
        `else \
          `RV32F_INSTR_BINS \
        `endif \
      `endif \
      // RV32X - \
      `RV32X_PULP_INSTR_BINS \
      // Ignore bins \
      ignore_bins ebreak_excp   = {TB_INSTR_EBREAK}   with ((item == TB_INSTR_EBREAK)   && has_ignore_irq_entry); \
      ignore_bins c_ebreak_excp = {TB_INSTR_C_EBREAK} with ((item == TB_INSTR_C_EBREAK) && has_ignore_irq_entry); \
      ignore_bins ecal_excp     = {TB_INSTR_ECALL}    with ((item == TB_INSTR_ECALL)    && has_ignore_irq_entry); \
      ignore_bins mret_excp     = {TB_INSTR_MRET}     with ((item == TB_INSTR_MRET)     && has_ignore_irq_exit); \
      ignore_bins dret_excp     = {TB_INSTR_DRET}     with ((item == TB_INSTR_DRET)     && has_ignore_irq_exit); \
    } \
  endgroup : cg_``EVENT``

  `DEF_CG_INTERRUPT(irq_entry)
  `DEF_CG_INTERRUPT(irq_exit)
  `DEF_CG_INTERRUPT(wfi_entry)
  `DEF_CG_INTERRUPT(wfi_exit)
  // COVERGROUPS DEFINE HERE - END

  `uvm_component_utils(uvme_interrupt_covg_v2)

  function new(string name="uvme_interrupt_covg_v2", uvm_component parent=null);
    super.new(name, parent);
    `CG_INTERRUPT(irq_entry) = new(.has_ignore_irq_entry(1), .has_ignore_irq_exit(0));
    `CG_INTERRUPT(irq_exit)  = new(.has_ignore_irq_entry(0), .has_ignore_irq_exit(1));
    `CG_INTERRUPT(wfi_entry) = new(.has_ignore_irq_entry(0), .has_ignore_irq_exit(0));
    `CG_INTERRUPT(wfi_exit)  = new(.has_ignore_irq_entry(0), .has_ignore_irq_exit(0));
    `CG_INTERRUPT(irq_entry).set_inst_name($sformatf("cg_irq_entry"));
    `CG_INTERRUPT(irq_exit).set_inst_name( $sformatf("cg_irq_exit"));
    `CG_INTERRUPT(wfi_entry).set_inst_name($sformatf("cg_wfi_entry"));
    `CG_INTERRUPT(wfi_exit).set_inst_name( $sformatf("cg_wfi_exit"));
  endfunction: new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!(uvm_config_db#(virtual uvmt_cv32e40p_rvvi_if)::get(this, "", "cv32e40p_rvvi_vif", cv32e40p_rvvi_vif))) begin
        `uvm_fatal(_header, "cv32e40p_rvvi_vif no found in uvm_config_db");
    end
    if ($test$plusargs("skip_sampling_uvme_interrupt_covg_v2")) begin
      `uvm_info(_header, "Skip uvme_interrupt_covg_v2 cvg sampling due to test intention", UVM_WARNING);
      en_cvg_sampling = 0;
    end
  endfunction : build_phase

  function bit pc_is_mtvec_addr();
    if (cv32e40p_rvvi_vif.pc_rdata >= cv32e40p_rvvi_vif.mtvec_base_addr && cv32e40p_rvvi_vif.pc_rdata < (cv32e40p_rvvi_vif.mtvec_base_addr + 32*4)) return 1; // direct or vector mode
    else return 0;
  endfunction : pc_is_mtvec_addr

  function bit is_mcause_irq();
    return cv32e40p_rvvi_vif.csr_mcause_irq;
  endfunction : is_mcause_irq

  // illegal instruction - ecall - ebreak - compress
  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    forever begin
      @(posedge cv32e40p_rvvi_vif.clk);
      if (cv32e40p_rvvi_vif.valid) begin : VALID_IS_HIGH

        current_insn = get_user_def_c_insn_if_true(cv32e40p_rvvi_vif.insn);
        if (cv32e40p_rvvi_vif.trap) is_trap = 1;
        else is_trap = 0;

        // IRQ related - START
        if (current_insn == TB_INSTR_MRET && is_irq) begin
          irq_nested_count--;
        end
        if (prev_insn == TB_INSTR_MRET && is_irq) begin : IRQ_EXIT
          `uvm_info(_header, $sformatf("DEBUG - IRQ Exit  - current_insn is '%8h", current_insn), UVM_DEBUG);
          `CG_INTERRUPT(irq_exit).sample(current_insn); // sample insn after irq exit
          is_irq = 0;
        end
        if (pc_is_mtvec_addr() && is_mcause_irq()) begin : IRQ_ENTRY
          `uvm_info(_header, $sformatf("DEBUG - IRQ Entry - prev_insn    is '%8h", (is_trap) ? prev_insn_d : prev_insn), UVM_DEBUG);
          irq_nested_count++;
          if (is_trap) begin `CG_INTERRUPT(irq_entry).sample(prev_insn_d); end  // sample insn before irq entry (insn prior trap)
          else begin         `CG_INTERRUPT(irq_entry).sample(prev_insn); end    // sample insn before irq entry
          is_irq = 1;
        end
        // IRQ related - END

        // WFI related - START
        if (is_wfi && prev_insn == TB_INSTR_WFI) begin : WFI_EXIT
          `uvm_info(_header, $sformatf("DEBUG - WFI Exit  - current_insn is '%8h", current_insn), UVM_DEBUG);
          `CG_INTERRUPT(wfi_exit).sample(current_insn); // sample insn after wfi exit
          is_wfi = 0;
        end
        if (current_insn == TB_INSTR_WFI) begin : WFI_ENTRY
          `uvm_info(_header, $sformatf("DEBUG - WFI Entry - prev_insn    is '%8h", prev_insn), UVM_DEBUG);
          `CG_INTERRUPT(wfi_entry).sample(prev_insn); // sample insn before wfi entry
          is_wfi = 1;
        end
        // WFI related - END

        prev_insn_d = prev_insn;
        prev_insn   = current_insn;
      end
    end // forever

  endtask : run_phase

  function void final_phase(uvm_phase phase);
    super.final_phase(phase);
    // assert(irq_nested_count == 0);
  endfunction : final_phase

endclass : uvme_interrupt_covg_v2

`endif
