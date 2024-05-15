`ifndef __REFERENCE_MODEL_SV__
`define __REFERENCE_MODEL_SV__


module reference_model
    import uvma_rvfi_pkg::*;
    (
        input logic clk_i,
        uvma_rvfi_instr_if_t rvfi_i,
        st_rvfi rvfi_o
    );

    initial begin
        $display("Reference Model: Starting");
    end

    pipeline_shell pipeline_shell_i(
        .clk_i(clk_i),
        .rvfi_i(rvfi_i),
        .rvfi_o(rvfi_o)
    );

endmodule //reference_model

`endif //__REFERENCE_MODEL_SV__