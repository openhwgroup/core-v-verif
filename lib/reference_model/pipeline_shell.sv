`ifndef __PIPELINE_SHELL_SV__
`define __PIPELINE_SHELL_SV__

module pipeline_shell 
    import uvma_rvfi_pkg::*;
    import iss_wrap_pkg::*;
    (
        input logic clk_i,
        uvma_rvfi_instr_if_t rvfi_i,
        rvfi_if_t rvfi_o
    );

    st_rvfi rvfi_iss;

    initial begin
        $display("Pipeline Shell: Starting");
    end

    always_ff @( posedge clk_i ) begin
        if(rvfi_i.rvfi_valid) begin
            iss_step(rvfi_iss);
            rvfi_o.valid = 1'b1;     
        end
        else begin
            rvfi_o.valid = 1'b0;     
        end
        
        rvfi_o.order = rvfi_iss.order;
        rvfi_o.insn = rvfi_iss.insn;
        rvfi_o.trap = rvfi_iss.trap;
        rvfi_o.halt = rvfi_iss.halt;
        rvfi_o.dbg = rvfi_iss.dbg;
        rvfi_o.dbg_mode = rvfi_iss.dbg_mode;
        rvfi_o.nmip = rvfi_iss.nmip;
        rvfi_o.intr = rvfi_iss.intr;
        rvfi_o.mode = rvfi_iss.mode;
        rvfi_o.ixl = rvfi_iss.ixl;
        rvfi_o.pc_rdata = rvfi_iss.pc_rdata;
        rvfi_o.pc_wdata = rvfi_iss.pc_wdata;
        rvfi_o.rs1_addr = rvfi_iss.rs1_addr;
        rvfi_o.rs1_rdata = rvfi_iss.rs1_rdata;
        rvfi_o.rs2_addr = rvfi_iss.rs2_addr;
        rvfi_o.rs2_rdata = rvfi_iss.rs2_rdata;
        rvfi_o.rs3_addr = rvfi_iss.rs3_addr;
        rvfi_o.rs3_rdata = rvfi_iss.rs3_rdata;
        rvfi_o.rd1_addr = rvfi_iss.rd1_addr;
        rvfi_o.rd1_wdata = rvfi_iss.rd1_wdata;
        rvfi_o.rd2_addr = rvfi_iss.rd2_addr;
        rvfi_o.rd2_wdata = rvfi_iss.rd2_wdata;
        rvfi_o.mem_addr = rvfi_iss.mem_addr;
        rvfi_o.mem_rdata = rvfi_iss.mem_rdata;
        rvfi_o.mem_rmask = rvfi_iss.mem_rmask;
        rvfi_o.mem_wdata = rvfi_iss.mem_wdata;
        rvfi_o.mem_wmask = rvfi_iss.mem_wmask;
    end

endmodule //pipeline_shell

`endif //__PIPELINE_SHELL_SV__
