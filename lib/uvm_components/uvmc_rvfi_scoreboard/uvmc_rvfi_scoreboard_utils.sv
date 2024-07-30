// Copyright 2023 OpenHW Group
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

`ifndef __UVMC_RVFI_UTILS_SV__
`define __UVMC_RVFI_UTILS_SV__

import "DPI-C" function int spike_create(string filename);

import "DPI-C" function void spike_set_param_uint64_t(string base, string name, longint unsigned value);
import "DPI-C" function void spike_set_param_str(string base, string name, string value);
import "DPI-C" function void spike_set_param_bool(string base, string name, bit value);
import "DPI-C" function void spike_set_default_params(string profile);
import "DPI-C" function void spike_set_params_from_file(string paramFilePath);

    st_core_cntrl_cfg m_core_cfg;

    static st_rvfi core_queue [$];
    static st_rvfi reference_model_queue [$];
    static longint unsigned instr_count;
    static longint unsigned csrs_match_count;
    static longint unsigned instr_mismatch_count;

    localparam INSTR_MISMATCH_MAX = 5;

    bit tb_sim_finished;

    function automatic string rvfi_print_struct(ref st_rvfi st);
            uvma_rvfi_mode mode;

            $cast(mode, st.mode[1:0]);

            return $sformatf(`FORMAT_INSTR_STR_MACRO, $sformatf("%t", $time), st.intr,
                            st.trap,
                            st.pc_rdata,
                            $sformatf("%08x", st.insn),
                            get_mode_str(mode),
                            st.rs1_addr, st.rs1_rdata,
                            st.rs2_addr, st.rs2_rdata,
                            st.rd1_addr, st.rd1_wdata,
                            dasm_insn(st.insn));

    endfunction : rvfi_print_struct

    function automatic string rvfi_print_yaml(string tab, ref st_rvfi st);

        return $sformatf("%spc_rdata: %h\n%spc_wdata: %h\n%smode: %h\n%strap: %h\n%sinsn: %h\n%sinsn_disasm: \"%s\"\n%srs1_addr: %h\n%srs1_rdata: %h\n%srs2_addr: %h\n%srs2_rdata: %h\n%srd1_addr: %h\n%srd1_rdata: %h",
            tab, st.pc_rdata,
            tab, st.pc_wdata,
            tab, st.mode,
            tab, st.trap,
            tab, st.insn,
            tab, dasm_insn(st.insn),
            tab, st.rs1_addr, tab, st.rs1_rdata,
            tab, st.rs2_addr, tab, st.rs2_rdata,
            tab, st.rd1_addr, tab, st.rd1_wdata);

    endfunction : rvfi_print_yaml

    function void rvfi_gen_report(string exit_cause, longint exit_code, string mismatch_description = "");
        string filename;
        int file_handle;

        if($value$plusargs("report_file=%s", filename)) begin

          `uvm_info("rvfi_scoreboard_utils", $sformatf("Opening file for YAML report: %s", filename), UVM_LOW);
          file_handle = $fopen(filename, "w");
          if (file_handle != 0) begin
              $fdisplay(file_handle, "exit_cause: %s", exit_cause);
              $fdisplay(file_handle, "exit_code: 0x%4h", exit_code);
              $fdisplay(file_handle, "instr_count: 0x%h", instr_count);
              $fdisplay(file_handle, "csrs_match_count: 0x%h", csrs_match_count);
              $fdisplay(file_handle, "mismatches_count: 0x%h", core_queue.size());
              $fdisplay(file_handle, "mismatches:");
              for(int i = 0; i < core_queue.size() && i < reference_model_queue.size(); i++) begin
                  st_rvfi st_core, st_reference_model;

                  st_core = core_queue[i];
                  st_reference_model = reference_model_queue[i];

                  $fdisplay(file_handle, "  - %h:", i);
                  $fdisplay(file_handle, "    core:");
                  $fdisplay(file_handle, rvfi_print_yaml("      ", st_core));
                  $fdisplay(file_handle, "    reference_model:");
                  $fdisplay(file_handle, rvfi_print_yaml("      ", st_reference_model));
              end
              $fdisplay(file_handle, "mismatch_description: \"%s\"", mismatch_description.substr(1,mismatch_description.len()-1));
              $fclose(file_handle);
              `uvm_info("rvfi_scoreboard_utils", $sformatf("Generated YAML report: %s", filename), UVM_LOW);
          end
          else begin
              $display("Error: Unable to open file for writing.");
          end
        end
        else begin
          `uvm_info("rvfi_scoreboard_utils", "YAML report not produced", UVM_LOW);
        end
    endfunction

    function automatic void rvfi_initialize(st_core_cntrl_cfg core_cfg);

        m_core_cfg = core_cfg;
        void '(dasm_set_config(core_cfg.xlen, get_isa_str(core_cfg), 0));

    endfunction : rvfi_initialize

    function automatic void rvfi_compare(st_rvfi t_core, st_rvfi t_reference_model);
        int core_pc64, reference_model_pc64;
        string cause_str = "";
        bit error;

        core_pc64 = t_core.pc_rdata;
        reference_model_pc64 = t_reference_model.pc_rdata;
        if (m_core_cfg.xlen == MXL_32) begin
            core_pc64 = core_pc64 & 'hFFFFFFFF;
            reference_model_pc64 = reference_model_pc64 & 'hFFFFFFFF;
        end

        `define COMPARE(field, error_str) \
            if (t_core.``field !== t_reference_model.``field) begin \
                error = 1; \
                cause_str = $sformatf("%s\n%s Mismatch [REF]: 0x%-16h [CORE]: 0x%-16h", cause_str, error_str, t_reference_model.``field, t_core.``field); \
            end

        if (t_core.dbg[2:0] | t_reference_model.dbg[2:0]) begin
            `COMPARE(dbg[2:0] , "Debug cause")
        end
        else if (0 && t_core.intr[0] | t_reference_model.intr[0]) begin
            `COMPARE(intr[0], "INTR bit")
            else begin
                `uvm_info("scoreboard_utils", $sformatf("             INTR correctly compared core %h iss %h", t_reference_model.intr, t_core.intr), UVM_MEDIUM)
            end
        end
        else if (t_core.trap[0] | t_reference_model.trap[0]) begin
            `COMPARE(trap[0], "TRAP Mismatch")
        end
        else begin
            if (t_core.insn !== t_reference_model.insn) begin
                error = 1;
                cause_str = $sformatf("%s\nINSN Mismatch    [REF]: 0x%-16h [CORE]: 0x%-16h", cause_str, t_reference_model.insn, t_core.insn);
            end
            if (t_core.rd1_addr != 0 || t_reference_model.rd1_addr != 0) begin
                `COMPARE(rd1_addr[4:0], "RD ADDR")
                `COMPARE(rd1_wdata, "RD VAL")
            end
            `COMPARE(mode, "PRIV")
            if (core_pc64 !== reference_model_pc64) begin
                error = 1;
                cause_str = $sformatf("%s\nPC Mismatch      [REF]: 0x%-16h [CORE]: 0x%-16h", cause_str, reference_model_pc64, core_pc64);
            end
        end


        if (!m_core_cfg.disable_all_csr_checks) begin
            for (int i = 0; i < CSR_MAX_SIZE; i++) begin
                bit found = 0;
                longint unsigned addr = t_reference_model.csr_addr[i];
                bit valid = t_reference_model.csr_valid[addr] & ~m_core_cfg.unsupported_csr_mask[addr];

                if (valid && t_core.csr_valid[addr]) begin
                    bit core_value_condition = (m_core_cfg.unified_traps && (t_core.intr[0] | t_core.dbg[2:0])) && !(is_csr_insn(t_core) && addr == get_insn_rs1(t_core));
                    longint unsigned core_value = (core_value_condition) ? t_core.csr_rdata[addr] : t_core.csr_wdata[addr];
                    longint unsigned ref_value = t_reference_model.csr_wdata[addr];
                    if (m_core_cfg.xlen == MXL_32)
                        ref_value = ref_value & 'hFFFF_FFFF;
                    found = 1;
                    if (ref_value !== core_value) begin
                        error = 1; cause_str = $sformatf("%s\nCSR %-4h Mismatch   [REF]: 0x%-16h [CORE]: 0x%-16h",
                            cause_str, addr, ref_value, core_value);
                    end
                    else begin
                        csrs_match_count += 1;
                        `uvm_info("scoreboard_utils", $sformatf("             Correctly compared CSR %h with WDATA %h", addr, t_reference_model.csr_wdata[addr]), UVM_MEDIUM)
                    end
                end
                if (!found && valid) begin
                    error = 1; cause_str = $sformatf("%s\nCSR %-4h not found  [REF]: 0x%-16h [CORE]: 0x%-16h",
                        cause_str, addr, t_reference_model.csr_wdata[addr], 0);
                end
            end
        end

        instr_count = instr_count + 1;

        if (error) begin
            string instr_core = rvfi_print_struct(t_core);
            string instr_rm =   rvfi_print_struct(t_reference_model);

            core_queue = {core_queue, t_core};
            reference_model_queue = {reference_model_queue, t_reference_model};

            instr_mismatch_count += 1;
            rvfi_gen_report("MISMATCH", (t_reference_model.halt >> 1), cause_str);

            `uvm_info("spike_tandem", {cause_str}, UVM_NONE);
            `uvm_info("spike_tandem", {instr_rm}, UVM_NONE);
            if (instr_mismatch_count >= INSTR_MISMATCH_MAX) begin
                `uvm_fatal("spike_tandem", {instr_core, " <- CORE\n"});
            end
            else begin
                `uvm_error("spike_tandem", {instr_core, " <- CORE\n"});
            end
        end
        else begin
            `uvm_info("spike_tandem", rvfi_print_struct(t_reference_model) , UVM_MEDIUM)
            if (t_reference_model.halt[0] && !tb_sim_finished) begin
              tb_sim_finished = 1;
              rvfi_gen_report("SUCCESS", (t_reference_model.halt >> 1), "");
            end
        end

    endfunction : rvfi_compare

`endif

