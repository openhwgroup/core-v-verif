//
// Copyright 2022 OpenHW Group
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

import uvma_rvfi_pkg::*;
import uvm_pkg::*;

`define DUT_PATH dut_wrap.cv32e40s_wrapper_i
`define RVFI_IF  `DUT_PATH.rvfi_instr_if
`define INTERRUPT_IF dut_wrap.interrupt_if
`define CLKNRST_IF dut_wrap.clknrst_if

`define CORE_I `DUT_PATH.core_i

//`define STRINGIFY(x) `"x`"

//`ifdef USE_RM 

module rvfi_compare(
  rvfi_if_t rvfi_core,
  rvfi_if_t rvfi_rm
);


  function void check_32bit(input string compared, input bit [31:0] core, input logic [31:0] rm); 
      static int now = 0;
      if (now != $time) begin
        now = $time;
      end
      if (core !== rm) begin
        `uvm_error("Step-and-Compare", $sformatf("%s core=0x%8h and rm=0x%8h PC=0x%8h", compared, core, rm, rvfi_core.pc_rdata))
      end else begin
        `uvm_info("Step-and-Compare", $sformatf("%s core=0x%8h==core", compared, core), UVM_DEBUG)
      end
   endfunction // check_32bit

function void check_4bit(input string compared, input bit [3:0] core, input logic [3:0] rm); 
      static int now = 0;
      if (now != $time) begin
        now = $time;
      end
      if (core !== rm) begin
        `uvm_error("Step-and-Compare", $sformatf("%s core=0x%8h and rm=0x%8h PC=0x%8h", compared, core, rm, rvfi_core.pc_rdata))
      end else begin
        `uvm_info("Step-and-Compare", $sformatf("%s core=0x%8h==core", compared, core), UVM_DEBUG)
      end
   endfunction // check_4bit

  //use assertion to compare the RVFI signals
  rvfi_valid_a: assert property( @(posedge rvfi_core.clk)
    rvfi_core.valid |-> rvfi_rm.valid)
    else `uvm_error("RVFI_VALID", $sformatf("rvfi_rm.valid=%0h rvfi_core.valid=%0h",$sampled(rvfi_rm.valid), $sampled(rvfi_core.valid)));

  rvfi_pc_a: assert property( @(posedge rvfi_core.clk)
    rvfi_rm.valid |-> (rvfi_rm.pc_rdata == rvfi_core.pc_rdata))
    else `uvm_error("RVFI_PC", $sformatf("rvfi_rm.pc_rdata=%0h rvfi_core.pc_rdata=%0h",$sampled(rvfi_rm.pc_rdata), $sampled(rvfi_core.pc_rdata)));

  rvfi_insn_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid |-> (rvfi_rm.insn == rvfi_core.insn))
    else `uvm_error("RVFI_INSN", $sformatf("rvfi_rm.insn=%0h rvfi_core.insn=%0h",$sampled(rvfi_rm.insn), $sampled(rvfi_core.insn)));

  rvfi_trap_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid |-> (rvfi_rm.trap == rvfi_core.trap))
    else `uvm_error("RVFI_TRAP", $sformatf("rvfi_rm.trap=%0h rvfi_core.trap=%0h",$sampled(rvfi_rm.trap), $sampled(rvfi_core.trap)));

  rvfi_halt_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid |-> (rvfi_rm.halt == rvfi_core.halt))
    else `uvm_error("RVFI_HALT", $sformatf("rvfi_rm.halt=%0h rvfi_core.halt=%0h",$sampled(rvfi_rm.halt), $sampled(rvfi_core.halt)));

  rvfi_dbg_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid |-> (rvfi_rm.dbg == rvfi_core.dbg))
    else `uvm_error("RVFI_DBG", $sformatf("rvfi_rm.dbg=%0h rvfi_core.dbg=%0h",$sampled(rvfi_rm.dbg), $sampled(rvfi_core.dbg)));

  rvfi_dbg_mode_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid |-> (rvfi_rm.dbg_mode == rvfi_core.dbg_mode))
    else `uvm_error("RVFI_DBG_MODE", $sformatf("rvfi_rm.dbg_mode=%0h rvfi_core.dbg_mode=%0h",$sampled(rvfi_rm.dbg_mode), $sampled(rvfi_core.dbg_mode)));

  rvfi_nmip_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid |-> (rvfi_rm.nmip == rvfi_core.nmip))
    else `uvm_error("RVFI_NMIP", $sformatf("rvfi_rm.nmip=%0h rvfi_core.nmip=%0h",$sampled(rvfi_rm.nmip), $sampled(rvfi_core.nmip)));
  
  rvfi_intr_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid |-> (rvfi_rm.intr == rvfi_core.intr))
    else `uvm_error("RVFI_INTR", $sformatf("rvfi_rm.intr=%0h rvfi_core.intr=%0h",$sampled(rvfi_rm.intr), $sampled(rvfi_core.intr)));

  rvfi_mode_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid |-> (rvfi_rm.mode == rvfi_core.mode))
    else `uvm_error("RVFI_MODE", $sformatf("rvfi_rm.mode=%0h rvfi_core.mode=%0h",$sampled(rvfi_rm.mode), $sampled(rvfi_core.mode)));

  /*TODO: 
  ixl
  pc_wdata
  rs1_addr
  rs1_rdata;
  rs2_addr
  rs2_rdata
  rs3_addr
  rs3_rdata
  rd2_addr
  rd2_wdata

  CSRs
  */

  // TODO: implement these with assertions
  always_ff @(posedge rvfi_core.clk) begin
    if (rvfi_rm.valid) begin
      //Disable instructions with multiple memory accesses
      if(~(rvfi_core.mem_rmask[511:4] || rvfi_core.mem_wmask[511:4])) begin
        //Disable checking of rd1 if a trap occurs, since core and Spike mismatch
        if(~(rvfi_core.trap || rvfi_rm.trap)) begin
          check_32bit("rd1_addr", rvfi_core.rd1_addr, rvfi_rm.rd1_addr);

          // rd1_wdata is not guaranteed to be 0 even though rd1_addr is 0
          if(rvfi_core.rd1_addr != 0) begin
            check_32bit("rd1_wdata", rvfi_core.rd1_wdata, rvfi_rm.rd1_wdata);
          end
        end

        //Only check addr and data if there is a memory access
        check_32bit("mem_rmask", rvfi_core.mem_rmask, rvfi_rm.mem_rmask);

        check_32bit("mem_wmask", rvfi_core.mem_wmask, rvfi_rm.mem_wmask);
        if (rvfi_core.mem_rmask) begin

          check_32bit("mem_addr", rvfi_core.mem_addr, rvfi_rm.mem_addr);

          //check_32bit("mem_rdata", rvfi_core.mem_rdata, rvfi_rm.mem_rdata );
        end else if (rvfi_core.mem_wmask) begin

          check_32bit("mem_addr", rvfi_core.mem_addr, rvfi_rm.mem_addr);

          //check_32bit("mem_wdata", rvfi_core.mem_wdata, rvfi_rm.mem_wdata);

        end 

        //Only compare the bytes that are masked
        for (int i = 0; i < 4; i++) begin
          if (rvfi_core.mem_wmask[(4) + i]) begin
            check_4bit($sformatf("mem_wdata[%0d]", i), rvfi_core.mem_wdata[i*8 +:8], rvfi_rm.mem_wdata[i*8 +:8]);
          end

          if (`RVFI_IF.rvfi_mem_rmask[(4) + i]) begin
          check_4bit($sformatf("mem_wdata[%0d]", i), rvfi_core.mem_rdata[i*8 +:8], rvfi_rm.mem_rdata[i*8 +:8]);
        end

      end

      end

    end

  end
  


endmodule



//`include "reference_model.sv"
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
       .rvfi_o(rvfi_rm)
    );

    rvfi_compare rvfi_compare_i(
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
    #0.5 // Slightly offset the rm clock
    clknrst_if_rm.set_period(`CLKNRST_IF.clk_period);
    clknrst_if_rm.start_clk();
  end

  assign clknrst_if_rm.reset_n = `CLKNRST_IF.reset_n;

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
      $sformat(pipelineLine, "%s| ia %x | li %x / %x | db %x | f %x | cp %x | si %x | ib %x | cf %x | sl %x |",pipelineLine,
              `CORE_I.controller_i.controller_fsm_i.interrupt_allowed,
              `CORE_I.controller_i.controller_fsm_i.lsu_interruptible_i,
              reference_model_i.pipeline_shell_i.controller_i.lsu_interruptible,
              `CORE_I.controller_i.controller_fsm_i.debug_interruptible,
              `CORE_I.controller_i.controller_fsm_i.fencei_ongoing,
              `CORE_I.controller_i.controller_fsm_i.clic_ptr_in_pipeline,
              `CORE_I.controller_i.controller_fsm_i.sequence_interruptible,
              `CORE_I.controller_i.controller_fsm_i.interrupt_blanking_q,
              `CORE_I.controller_i.controller_fsm_i.csr_flush_ack_q,
              (`CORE_I.controller_i.controller_fsm_i.ctrl_fsm_cs == SLEEP));

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

    always_comb begin
      rvfi_core.valid     <= `RVFI_IF.rvfi_valid;

      rvfi_core.pc_rdata  <= `RVFI_IF.rvfi_pc_rdata;
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

//`endif // USE_RM

`endif // __UVMT_CV32E40S_REFERENCE_MODEL_WRAP_SV__