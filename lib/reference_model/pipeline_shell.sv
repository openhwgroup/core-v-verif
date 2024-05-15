`ifndef __PIPELINE_SHELL_SV__
`define __PIPELINE_SHELL_SV__

module pipeline_shell 
    import uvma_rvfi_pkg::*;
    import iss_wrap_pkg::*;
    (
        input logic clk_i,
        uvma_rvfi_instr_if_t rvfi_i,
        st_rvfi rvfi_o
    );

    st_rvfi rvfi_iss;
    string binary;

    initial begin
        if ($value$plusargs("elf_file=%s", binary))
            $display("Setting up ISS with binary %s...", binary);
        
        iss_init(binary);

        $display("Pipeline Shell: Starting");
    end

    always_ff @( posedge clk_i ) begin
        if(rvfi_i.rvfi_valid) begin
            iss_step(rvfi_iss);
            
            $displayb("insn: %x",rvfi_iss.insn);
            $displayb("pc: %x",rvfi_iss.pc_rdata);
        end
    end


endmodule //pipeline_shell

`endif //__PIPELINE_SHELL_SV__
