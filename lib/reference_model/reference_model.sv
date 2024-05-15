`ifndef __REFERENCE_MODEL_SV__
`define __REFERENCE_MODEL_SV__


module reference_model
    import iss_wrap_pkg::*;
    import uvma_rvfi_pkg::*;
    (
        input logic clk_i,
        uvma_rvfi_instr_if_t rvfi_i,
        uvma_interrupt_if_t interrupt_if_i,
        rvfi_if_t rvfi_o
    );

    string binary;

    initial begin
        if ($value$plusargs("elf_file=%s", binary))
            $display("Setting up ISS with binary %s...", binary);
        
        iss_init(binary);

        $display("Reference Model: Starting");
    end

    pipeline_shell pipeline_shell_i(
        .clk_i(clk_i),
        .rvfi_i(rvfi_i),
        .interrupt_if_i(interrupt_if_i),
        .rvfi_o(rvfi_o)
    );

endmodule //reference_model

`endif //__REFERENCE_MODEL_SV__