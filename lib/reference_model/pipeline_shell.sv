`ifndef __PIPELINE_SHELL_SV__
`define __PIPELINE_SHELL_SV__
//`include "iss_wrap.sv"

import uvma_rvfi_pkg::*;

import "DPI-C" function void spike_init(string filename);
import "DPI-C" function void spike_step(inout st_rvfi rvfi_o);

module pipeline_shell 
    import uvma_rvfi_pkg::*;
    (
        input logic clk_i,
        uvma_rvfi_instr_if_t rvfi_i
        //uvma_rvfi_instr_if_t rvfi_o
    );

    st_rvfi rvfi;
    string binary;

    initial begin
        if ($value$plusargs("elf_file=%s", binary))
            $display("Setting up Spike with binary %s...", binary);

        spike_init(binary);
        $display("Pipeline Shell: Starting");
    end

    always_ff @( posedge clk_i ) begin
        if(rvfi_i.rvfi_valid) begin
            spike_step(rvfi);
            //$monitor("insn: %x", st_rvfi.insn);
            //rvfi_o.rvfi_insn = st_rvfi.insn;
        end
    end


endmodule //pipeline_shell

`endif //__PIPELINE_SHELL_SV__
