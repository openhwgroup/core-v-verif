`ifndef __PIPELINE_SHELL_SV__
`define __PIPELINE_SHELL_SV__
//`include "iss_wrap.sv"

import uvma_rvfi_pkg::*;

import "DPI-C" function void spike_init();
import "DPI-C" function void spike_step(inout st_rvfi rvfi_o);

module pipeline_shell 
    import uvma_rvfi_pkg::*;
    (
        input logic clk_i,
        uvma_rvfi_instr_if_t rvfi_i,
        uvma_rvfi_instr_if_t rvfi_o
    );

    st_rvfi rvfi;

    initial begin
        $display("Pipeline Shell: Starting");
        spike_init();
    end

    always_ff @( posedge clk_i ) begin
        if(rvfi_i.rvfi_valid) begin
            spike_step(rvfi);
        end
    end

endmodule //pipeline_shell

`endif //__PIPELINE_SHELL_SV__
