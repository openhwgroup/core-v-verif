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


`ifndef __UVMA_RVFI_UTILS_SV__
`define __UVMA_RVFI_UTILS_SV__

import "DPI-C" function int spike_create(string filename);

import "DPI-C" function void spike_set_param_uint64_t(string base, string name, longint unsigned value);
import "DPI-C" function void spike_set_param_str(string base, string name, string value);
import "DPI-C" function void spike_set_default_params(string profile);

localparam config_pkg::cva6_cfg_t CVA6Cfg = cva6_config_pkg::cva6_cfg;

    function void rvfi_initialize_spike(bit testharness);
       string binary, rtl_isa;

        `ifdef VERILATOR
            `uvm_fatal("spike_tandem", "Verilator not supported in tandem mode, please unset SPIKE_TANDEM");
        `endif
        if ($value$plusargs("elf_file=%s", binary))
            `uvm_info("spike_tandem", $sformatf("Setting up Spike with binary %s...", binary), UVM_LOW);

       rtl_isa = $sformatf("RV%-2dIM",
                            riscv::XLEN);
        if (CVA6Cfg.RVA) begin
            rtl_isa = {rtl_isa, "A"};
        end
        if (CVA6Cfg.RVF | CVA6Cfg.FpuEn) begin
            rtl_isa = {rtl_isa, "F"};
        end
        if (CVA6Cfg.RVD) begin
            rtl_isa = {rtl_isa, "D"};
        end
        if (CVA6Cfg.RVC) begin
            rtl_isa = {rtl_isa, "C"};
        end
       if (cva6_config_pkg::CVA6ConfigBExtEn) begin
           rtl_isa = $sformatf("%s_zba_zbb_zbc_zbs", rtl_isa);
       end

       assert(binary != "") else `uvm_fatal("spike_tandem", "We need a preloaded binary for tandem verification");

       void'(spike_set_default_params("cva6"));
       void'(spike_set_param_uint64_t("/top/core/0/", "boot_addr", testharness ? 'h10000 : 'h80000000));
       void'(spike_set_param_str("/top/", "isa", rtl_isa));
       void'(spike_set_param_str("/top/core/0/", "isa", rtl_isa));
       void'(spike_create(binary));

    endfunction : rvfi_initialize_spike

    function void rvfi_compare(st_rvfi t_core, st_rvfi t_reference_model);
        int core_pc64, reference_model_pc64;
        string cause_str = "";
        bit error;
        string instr;
        uvma_rvfi_mode mode;

        core_pc64 = {{riscv::XLEN-riscv::VLEN{t_core.pc_rdata[riscv::VLEN-1]}}, t_core.pc_rdata};
        reference_model_pc64 = {{riscv::XLEN-riscv::VLEN{t_reference_model.pc_rdata[riscv::VLEN-1]}}, t_reference_model.pc_rdata};

        if (t_core.trap || t_reference_model.trap) begin
            assert (t_core.trap === t_reference_model.trap) else begin
                error = 1;
                cause_str = $sformatf("%s\nException Mismatch [REF]: 0x%-16h [CVA6]: 0x%-16h", cause_str, t_reference_model.trap, t_core.trap);
            end
            assert (t_core.cause === t_reference_model.cause) else begin
                error = 1;
                cause_str = $sformatf("%s\nException Cause Mismatch [REF]: 0x%-16h [CVA6]: 0x%-16h", cause_str, t_reference_model.cause, t_core.cause);
            end
        end
        else begin
            assert (t_core.insn === t_reference_model.insn) else begin
                error = 1;
                cause_str = $sformatf("%s\nINSN Mismatch    [REF]: 0x%-16h [CVA6]: 0x%-16h", cause_str, t_reference_model.insn, t_core.insn);
            end
            if (t_core.rd1_addr != 0 || t_reference_model.rd1_addr != 0) begin
                assert (t_core.rd1_addr[4:0] === t_reference_model.rd1_addr[4:0]) else begin
                    error = 1;
                    cause_str = $sformatf("%s\nRD ADDR Mismatch [REF]: 0x%-16h [CVA6]: 0x%-16h", cause_str, t_reference_model.rd1_addr[4:0], t_core.rd1_addr[4:0]);
                end
                assert (t_core.rd1_wdata === t_reference_model.rd1_wdata) else begin
                    error = 1;
                    cause_str = $sformatf("%s\nRD VAL Mismatch  [REF]: 0x%-16h [CVA6]: 0x%-16h", cause_str, t_reference_model.rd1_wdata, t_core.rd1_wdata);
                end
            end
            assert (t_core.mode === t_reference_model.mode) else begin
                error = 1;
                cause_str = $sformatf("%s\nPRIV Mismatch    [REF]: 0x%-16h [CVA6]: 0x%-16h", cause_str, t_reference_model.mode, t_core.mode);
            end
        end

        assert (core_pc64 === reference_model_pc64) else begin
            error = 1;
            cause_str = $sformatf("%s\nPC Mismatch      [REF]: 0x%-16h [CVA6]: 0x%-16h", cause_str, reference_model_pc64, core_pc64);
        end

        $cast(mode, t_reference_model.mode);

        // TODO Add more fields from Spike side
        instr = $sformatf(format_instr_str, $sformatf("%t", $time),
                        0,
                        t_reference_model.trap,
                        t_reference_model.pc_rdata,
                        $sformatf("%08x", t_reference_model.insn),
                        get_mode_str(mode),
                        t_reference_model.rs1_addr, t_reference_model.rs1_rdata,
                        t_reference_model.rs2_addr, t_reference_model.rs2_rdata,
                        t_reference_model.rd1_addr, t_reference_model.rd1_wdata);
        `uvm_info("spike_tandem", instr, UVM_NONE)
        if (error) begin
            `uvm_fatal("spike_tandem", cause_str)
        end

    endfunction : rvfi_compare

`endif

