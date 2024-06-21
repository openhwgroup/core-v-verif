//
// Copyright 2024 Torje Nygaard Eikenes
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
//


`ifndef __UVMT_CV32E40S_REFERENCE_MODEL_WRAP_SV__
`define __UVMT_CV32E40S_REFERENCE_MODEL_WRAP_SV__


`define DUT_PATH dut_wrap.cv32e40s_wrapper_i
`define RVFI_IF  `DUT_PATH.rvfi_instr_if
`define INTERRUPT_IF dut_wrap.interrupt_if
`define DEBUG_IF debug_if
`define CLKNRST_IF dut_wrap.clknrst_if

`define CORE_I `DUT_PATH.core_i

module uvmt_cv32e40s_reference_model_wrap
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  import uvme_cv32e40s_pkg::*;
  import uvma_rvfi_pkg::*;
  ();

    uvma_clknrst_if_t clknrst_if_rm();
    rvfi_if_t rvfi_rm();
    rvfi_if_t rvfi_core();
    int clock_cnt;

    reference_model reference_model_i(
       .clknrst_if(clknrst_if_rm),
       .rvfi_i(`RVFI_IF),
       .interrupt_if_i(`INTERRUPT_IF),
       .debug_req_i(debug_if.debug_req),
       .rvfi_o(rvfi_rm)
    );

    rvfi_compare_sva rvfi_compare_i(
      .rvfi_core(rvfi_core),
      .rvfi_rm(rvfi_rm)
    );

   string info_tag = "RM_wrap";

   uvme_cv32e40s_cfg_c  uvm_env_cfg;

   int fd; 
   int pl; 
   string line;
   string pipelineLine;
   logic [31:0] irq_drv_ff;

   initial begin
     @(`RVFI_IF.clk);
     void'(uvm_config_db#(uvme_cv32e40s_cfg_c)::get(null, "uvm_test_top.env", "cfg", uvm_env_cfg));
     if (!uvm_env_cfg) begin
      `uvm_fatal(info_tag, "Configuration handle is null")
     end
     else begin
      `uvm_info(info_tag, $sformatf("Found UVM environment configuration handle:\n%s", uvm_env_cfg.sprint()), UVM_DEBUG)
     end

     fd = $fopen("reference_model.log", "w");
     pl = $fopen("pipeline.log", "w");

     $fdisplay(fd, "Reference model logging");

   end

  initial begin
    clknrst_if_rm.clk = 1'b0;
    #1;  // time for clknrst_if to set the clk_period
    wait (`CLKNRST_IF.clk_period != 0.0);
    `uvm_info("RM_WRAP", "Starting RM clock", UVM_LOW)
    clknrst_if_rm.set_period(`CLKNRST_IF.clk_period);
    clknrst_if_rm.start_clk();
  end

  assign clknrst_if_rm.reset_n = `CLKNRST_IF.reset_n;

  // Temporary logging to compare core functionality to RM   
    always_ff @(posedge rvfi_core.clk) begin
      $sformat(line, "");
      irq_drv_ff <= `INTERRUPT_IF.irq_drv;
      if (irq_drv_ff != `INTERRUPT_IF.irq_drv) begin
        $sformat(line, "MIP set to: %x",`INTERRUPT_IF.irq_drv);
        $sformat(pipelineLine, "MIP set to: %x",`INTERRUPT_IF.irq_drv);
        $fdisplay(fd, line);
        $fdisplay(pl, pipelineLine);
      end
      $sformat(pipelineLine, "%15s | IF %x  %x| ID %x %x| EX %x %x | WB %x %x | RVFI %x %x|",$sformatf("%t", $time), 
              `CORE_I.if_stage_i.pc_if_o, `CORE_I.if_stage_i.instr_valid,  
              `CORE_I.if_id_pipe.pc, `CORE_I.id_stage_i.instr_valid, 
              `CORE_I.id_ex_pipe.pc, `CORE_I.ex_stage_i.instr_valid,
              `CORE_I.ex_wb_pipe.pc, `CORE_I.wb_stage_i.instr_valid,
              `RVFI_IF.rvfi_pc_rdata, `RVFI_IF.rvfi_valid);
      $sformat(pipelineLine, "%s| ID %8x  %x| EX %8x %x | WB %8x %x | RVFI %x %x",pipelineLine, 
              reference_model_i.pipeline_shell_i.if_id_pipe.rvfi.pc_rdata,
              reference_model_i.pipeline_shell_i.if_id_pipe.valid,
              reference_model_i.pipeline_shell_i.id_ex_pipe.rvfi.pc_rdata,
              reference_model_i.pipeline_shell_i.id_ex_pipe.valid,
              reference_model_i.pipeline_shell_i.ex_wb_pipe.rvfi.pc_rdata,
              reference_model_i.pipeline_shell_i.ex_wb_pipe.valid,
              rvfi_rm.pc_rdata, rvfi_rm.valid);
      $sformat(pipelineLine, "%s| dbg %x | dbg t %x | dbg m %x | da %x | ada %x | irq %x| ia %x / %x | it %x | ie %x | mie %x / %x | INTR %x %d / %x %d |",pipelineLine,
              debug_if.debug_req,
              reference_model_i.pipeline_shell_i.controller_i.debug_taken,
              reference_model_i.pipeline_shell_i.controller_i.debug_mode,
              `CORE_I.controller_i.controller_fsm_i.sync_debug_allowed,
              `CORE_I.controller_i.controller_fsm_i.async_debug_allowed,
              `INTERRUPT_IF.irq,
              `CORE_I.controller_i.controller_fsm_i.interrupt_allowed,
              reference_model_i.pipeline_shell_i.controller_i.interrupt_allowed,
              reference_model_i.pipeline_shell_i.controller_i.interrupt_taken,
              reference_model_i.pipeline_shell_i.controller_i.interrupt_enabled,
              `CORE_I.mie,
              reference_model_i.pipeline_shell_i.controller_i.mie,
              `RVFI_IF.rvfi_intr, (`RVFI_IF.rvfi_intr >> 3),
              rvfi_rm.intr, (rvfi_rm.intr >> 3)
              );

      if(rvfi_core.valid) begin
        $sformat(line, " %-8s | %d | %x (%x) | %x, (%x) | IF %x | ID %x | EX %x | WB %x |",`RVFI_IF.instr_asm.instr.name(), clock_cnt, rvfi_core.pc_rdata, rvfi_core.insn, rvfi_rm.pc_rdata, rvfi_rm.insn, `CORE_I.if_id_pipe.pc, `CORE_I.id_ex_pipe.pc, `CORE_I.ex_wb_pipe.pc, rvfi_core.pc_rdata);
        $sformat(pipelineLine, "%s RVFI | %-8s | %x", pipelineLine, `RVFI_IF.instr_asm.instr.name(), rvfi_core.pc_rdata);

        if (rvfi_core.intr) begin
          $sformat(line, "%s Core INTR Taken", line);
        end
        if (rvfi_rm.intr) begin
          $sformat(line, "%s RM INTR Taken", line);
        end
        $fdisplay(fd, line);

        clock_cnt = 0;
      end
      else
        clock_cnt++;

      $fdisplay(pl, pipelineLine);
    end

    assign rvfi_core.clk = `RVFI_IF.clk;

    //Delay one cycle to keep in sync with the reference model which currently depends on rvfi_valid from the core
    always_ff @(posedge `RVFI_IF.clk) begin
      rvfi_core.valid     <= `RVFI_IF.rvfi_valid;

      rvfi_core.insn      <= `RVFI_IF.rvfi_insn;
      rvfi_core.trap      <= `RVFI_IF.rvfi_trap;
      rvfi_core.halt      <= `RVFI_IF.rvfi_halt;
      rvfi_core.dbg       <= `RVFI_IF.rvfi_dbg;
      rvfi_core.dbg_mode  <= `RVFI_IF.rvfi_dbg_mode;
      rvfi_core.nmip      <= `RVFI_IF.rvfi_nmip;
      rvfi_core.intr      <= `RVFI_IF.rvfi_intr;
      rvfi_core.mode      <= `RVFI_IF.rvfi_mode;
      rvfi_core.ixl       <= `RVFI_IF.rvfi_ixl;
      rvfi_core.pc_rdata  <= `RVFI_IF.rvfi_pc_rdata;
      rvfi_core.pc_wdata  <= `RVFI_IF.rvfi_pc_wdata;
      rvfi_core.rs1_addr  <= `RVFI_IF.rvfi_rs1_addr;
      rvfi_core.rs1_rdata <= `RVFI_IF.rvfi_rs1_rdata;
      rvfi_core.rs2_addr  <= `RVFI_IF.rvfi_rs2_addr;
      rvfi_core.rs2_rdata <= `RVFI_IF.rvfi_rs2_rdata;
      rvfi_core.rs3_addr  <= `RVFI_IF.rvfi_rs3_addr;
      rvfi_core.rs3_rdata <= `RVFI_IF.rvfi_rs3_rdata;
      rvfi_core.rd1_addr  <= `RVFI_IF.rvfi_rd1_addr;
      rvfi_core.rd1_wdata <= `RVFI_IF.rvfi_rd1_wdata;
      rvfi_core.rd2_addr  <= `RVFI_IF.rvfi_rd2_addr;
      rvfi_core.rd2_wdata <= `RVFI_IF.rvfi_rd2_wdata;

      rvfi_core.mem_addr  <= `RVFI_IF.rvfi_mem_addr;
      rvfi_core.mem_rdata <= `RVFI_IF.rvfi_mem_rdata;
      rvfi_core.mem_rmask <= `RVFI_IF.rvfi_mem_rmask;
      rvfi_core.mem_wdata <= `RVFI_IF.rvfi_mem_wdata;
      rvfi_core.mem_wmask <= `RVFI_IF.rvfi_mem_wmask;
    end


endmodule : uvmt_cv32e40s_reference_model_wrap

`endif // __UVMT_CV32E40S_REFERENCE_MODEL_WRAP_SV__