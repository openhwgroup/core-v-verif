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

    st_core_cntrl_cfg m_core_cfg;

    function automatic string rvfi_print_struct(ref st_rvfi st);
            uvma_rvfi_mode mode;

            $cast(mode, st.mode[1:0]);

            return $sformatf(`FORMAT_INSTR_STR_MACRO, $sformatf("%t", $time), 0,
                            st.trap,
                            st.pc_rdata,
                            $sformatf("%08x", st.insn),
                            get_mode_str(mode),
                            st.rs1_addr, st.rs1_rdata,
                            st.rs2_addr, st.rs2_rdata,
                            st.rd1_addr, st.rd1_wdata,
                            dasm_insn(st.insn));

    endfunction : rvfi_print_struct

    function automatic void rvfi_initialize(st_core_cntrl_cfg core_cfg);

        m_core_cfg = core_cfg;
        void '(dasm_set_config(core_cfg.xlen, rvfi_get_isa_str(core_cfg), 0));

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

        if (t_core.trap[0] | t_reference_model.trap[0]) begin
            if (t_core.trap[0] !== t_reference_model.trap[0]) begin
                error = 1;
                cause_str = $sformatf("%s\nException Mismatch [REF]: 0x%-16h [CORE]: 0x%-16h", cause_str, t_reference_model.trap[0], t_core.trap[0]);
            end
        end
        else begin
            if (t_core.insn !== t_reference_model.insn) begin
                error = 1;
                cause_str = $sformatf("%s\nINSN Mismatch    [REF]: 0x%-16h [CORE]: 0x%-16h", cause_str, t_reference_model.insn, t_core.insn);
            end
            if (t_core.rd1_addr != 0 || t_reference_model.rd1_addr != 0) begin
                if (t_core.rd1_addr[4:0] !== t_reference_model.rd1_addr[4:0]) begin
                    error = 1;
                    cause_str = $sformatf("%s\nRD ADDR Mismatch [REF]: 0x%-16h [CORE]: 0x%-16h", cause_str, t_reference_model.rd1_addr[4:0], t_core.rd1_addr[4:0]);
                end
                if (t_core.rd1_wdata !== t_reference_model.rd1_wdata) begin
                    error = 1;
                    cause_str = $sformatf("%s\nRD VAL Mismatch  [REF]: 0x%-16h [CORE]: 0x%-16h", cause_str, t_reference_model.rd1_wdata, t_core.rd1_wdata);
                end
            end
            if (t_core.mode !== t_reference_model.mode) begin
                error = 1;
                cause_str = $sformatf("%s\nPRIV Mismatch    [REF]: 0x%-16h [CORE]: 0x%-16h", cause_str, t_reference_model.mode, t_core.mode);
            end
        end

        if (core_pc64 !== reference_model_pc64) begin
            error = 1;
            cause_str = $sformatf("%s\nPC Mismatch      [REF]: 0x%-16h [CORE]: 0x%-16h", cause_str, reference_model_pc64, core_pc64);
        end

        if (!m_core_cfg.disable_all_csr_checks) begin
            for (int i = 0; i < CSR_QUEUE_SIZE; i++) begin
                bit found = 0;
                longint unsigned addr = t_reference_model.csr_addr[i];
                bit valid = t_reference_model.csr_valid[i] & ~m_core_cfg.unsupported_csr_mask[addr];

                for (int j = 0; j < CSR_QUEUE_SIZE && !found && valid; j++) begin
                    if (addr == t_core.csr_addr[j] && t_core.csr_valid[j]) begin
                        found = 1;
                        if (t_reference_model.csr_wdata[i] !== t_core.csr_wdata[j]) begin
                            error = 1; cause_str = $sformatf("%s\nCSR %-4h Mismatch   [REF]: 0x%-16h [CORE]: 0x%-16h",
                                cause_str, addr, t_reference_model.csr_wdata[i], t_core.csr_wdata[j]);
                        end
                    end
                end
                if (!found && valid) begin
                    error = 1; cause_str = $sformatf("%s\nCSR %-4h not found  [REF]: 0x%-16h [CORE]: 0x%-16h",
                        cause_str, addr, t_reference_model.csr_wdata[i], 0);
                end
            end
        end

        if (error) begin
            string instr_core = rvfi_print_struct(t_core);
            string instr_rm =   rvfi_print_struct(t_reference_model);
            `uvm_info("spike_tandem", {instr_rm}, UVM_LOW);
            `uvm_error("spike_tandem", {instr_core, " <- CORE\n", cause_str});
        end
        else begin
            `uvm_info("spike_tandem", rvfi_print_struct(t_reference_model) , UVM_LOW)
        end

    endfunction : rvfi_compare

`endif

