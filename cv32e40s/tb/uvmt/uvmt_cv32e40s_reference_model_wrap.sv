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
`define DEBUG_IF debug_if
`define CLKNRST_IF dut_wrap.clknrst_if

`define CORE_I `DUT_PATH.core_i

//`define STRINGIFY(x) `"x`"

//`ifdef USE_RM 

module rvfi_compare(
  rvfi_if_t rvfi_core,
  rvfi_if_t rvfi_rm
);

`define ASSERT_EQUAL(NAME, NAME_STR) \
    NAME``_a: assert property( @(posedge rvfi_core.clk) \
      rvfi_rm.valid |-> (rvfi_rm.NAME == rvfi_core.NAME)) \
      else `uvm_error(NAME_STR, $sformatf("PC: %0h rvfi_rm.%0s=%0h rvfi_core.%0s=%0h", rvfi_rm.pc_rdata, NAME_STR, $sampled(rvfi_rm.NAME), NAME_STR, $sampled(rvfi_core.NAME)))

  rvfi_valid_a: assert property( @(posedge rvfi_core.clk)
    rvfi_core.valid || rvfi_rm.valid |-> (rvfi_rm.valid == rvfi_core.valid))
    else `uvm_error("RVFI_VALID", $sformatf("rvfi_rm.valid=%0h rvfi_core.valid=%0h",$sampled(rvfi_rm.valid), $sampled(rvfi_core.valid)));

  `ASSERT_EQUAL(insn, "RVFI_INSN")
  `ASSERT_EQUAL(trap, "RVFI_TRAP")
  `ASSERT_EQUAL(halt, "RVFI_HALT")
  `ASSERT_EQUAL(dbg, "RVFI_DBG")
  `ASSERT_EQUAL(dbg_mode, "RVFI_DBG_MODE")
  `ASSERT_EQUAL(nmip, "RVFI_NMIP")
  `ASSERT_EQUAL(intr, "RVFI_INTR")
  `ASSERT_EQUAL(mode, "RVFI_MODE")
  `ASSERT_EQUAL(rd1_addr, "RVFI_RD1_ADDR")

  // TODO: Spike outputs wrong values for rs1_addr and rs2_addr
  //`ASSERT_EQUAL(rs1_addr, "RVFI_RS1_ADDR")
  //`ASSERT_EQUAL(rs1_rdata, "RVFI_RS1_RDATA")
  //`ASSERT_EQUAL(rs2_addr, "RVFI_RS2_ADDR")
  //`ASSERT_EQUAL(rs2_rdata, "RVFI_RS2_RDATA")

  // TODO: The following assertions cant use the macro because they require more conditions

  //`ASSERT_EQUAL(rd1_wdata, "RVFI_RD1_WDATA")
  rvfi_rd1_wdata_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid && rvfi_rm.rd1_addr |-> (rvfi_rm.rd1_wdata == rvfi_core.rd1_wdata))
    else `uvm_error("RVFI_RD1_WDATA", $sformatf("rvfi_rm.rd1_wdata=%0h rvfi_core.rd1_wdata=%0h",$sampled(rvfi_rm.rd1_wdata), $sampled(rvfi_core.rd1_wdata)));

  //`ASSERT_EQUAL(mem_rmask, "RVFI_MEM_RMASK")
  rvfi_mem_rmask_a: assert property(@ (posedge rvfi_core.clk) 
    rvfi_rm.valid |-> (rvfi_rm.mem_rmask == rvfi_core.mem_rmask[3:0])) 
    else `uvm_error("RVFI_MEM_RMASK", $sformatf("rvfi_rm.mem_rmask=%0h rvfi_core.mem_rmask=%0h",$sampled(rvfi_rm.mem_rmask), $sampled(rvfi_core.mem_rmask)));

  //`ASSERT_EQUAL(mem_wmask, "RVFI_MEM_WMASK")
  rvfi_mem_wmask_a: assert property(@ (posedge rvfi_core.clk) 
    rvfi_rm.valid |-> (rvfi_rm.mem_wmask == rvfi_core.mem_wmask[3:0]))
    else `uvm_error("RVFI_MEM_WMASK", $sformatf("rvfi_rm.mem_wmask=%0h rvfi_core.mem_wmask=%0h",$sampled(rvfi_rm.mem_wmask), $sampled(rvfi_core.mem_wmask)));

  //`ASSERT_EQUAL(mem_addr, "RVFI_MEM_ADDR")
  rvfi_mem_addr_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and ((rvfi_core.mem_rmask || rvfi_core.mem_wmask))|-> (rvfi_rm.mem_addr[31:0] == rvfi_core.mem_addr[31:0]))
    else `uvm_error("RVFI_MEM_ADDR", $sformatf("PC: %0h rvfi_rm.mem_addr=%0h rvfi_core.mem_addr=%0h", $sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_addr), $sampled(rvfi_core.mem_addr)));

  // rvfi_mem_wdata is 32 bits wide, but we only check the bytes masked by mem_wmask
  rvfi_mem_wdata_0_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_wmask[0])|-> (rvfi_rm.mem_wdata[7:0] == rvfi_core.mem_wdata[7:0]))
    else `uvm_error("RVFI_MEM_WDATA", $sformatf("PC: %0h rvfi_rm.mem_wdata=%0h rvfi_core.mem_wdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_wdata), $sampled(rvfi_core.mem_wdata)));

  rvfi_mem_wdata_1_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_wmask[1])|-> (rvfi_rm.mem_wdata[15:8] == rvfi_core.mem_wdata[15:8]))
    else `uvm_error("RVFI_MEM_WDATA", $sformatf("PC: %0h rvfi_rm.mem_wdata=%0h rvfi_core.mem_wdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_wdata), $sampled(rvfi_core.mem_wdata)));
  
  rvfi_mem_wdata_2_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_wmask[2])|-> (rvfi_rm.mem_wdata[23:16] == rvfi_core.mem_wdata[23:16]))
    else `uvm_error("RVFI_MEM_WDATA", $sformatf("PC: %0h rvfi_rm.mem_wdata=%0h rvfi_core.mem_wdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_wdata), $sampled(rvfi_core.mem_wdata)));

  rvfi_mem_wdata_3_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_wmask[3])|-> (rvfi_rm.mem_wdata[31:24] == rvfi_core.mem_wdata[31:24]))
    else `uvm_error("RVFI_MEM_WDATA", $sformatf("PC: %0h rvfi_rm.mem_wdata=%0h rvfi_core.mem_wdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_wdata), $sampled(rvfi_core.mem_wdata)));


  // rvfi_mem_rdata
  rvfi_mem_rdata_0_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_rmask[0])|-> (rvfi_rm.mem_rdata[7:0] == rvfi_core.mem_rdata[7:0]))
    else `uvm_error("RVFI_MEM_RDATA", $sformatf("byte 0 pc %0h rvfi_rm.mem_rdata=%0h rvfi_core.mem_rdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_rdata[7:0]), $sampled(rvfi_core.mem_rdata[7:0])));

  rvfi_mem_rdata_1_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_rmask[1])|-> (rvfi_rm.mem_rdata[15:8] == rvfi_core.mem_rdata[15:8]))
    else `uvm_error("RVFI_MEM_RDATA", $sformatf("byte 1 pc %0h rvfi_rm.mem_rdata=%0h rvfi_core.mem_rdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_rdata[15:8]), $sampled(rvfi_core.mem_rdata[15:8])));

  rvfi_mem_rdata_2_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_rmask[2])|-> (rvfi_rm.mem_rdata[23:16] == rvfi_core.mem_rdata[23:16]))
    else `uvm_error("RVFI_MEM_RDATA", $sformatf("byte 2 pc %0h rvfi_rm.mem_rdata=%0h rvfi_core.mem_rdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_rdata[23:16]), $sampled(rvfi_core.mem_rdata[23:16])));

  rvfi_mem_rdata_3_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_rmask[3])|-> (rvfi_rm.mem_rdata[31:24] == rvfi_core.mem_rdata[31:24]))
    else `uvm_error("RVFI_MEM_RDATA", $sformatf("byte 3 pc %0h rvfi_rm.mem_rdata=%0h rvfi_core.mem_rdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_rdata[31:24]), $sampled(rvfi_core.mem_rdata[31:24])));


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
       .debug_req_i(debug_if.debug_req),
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

    //Delay one cycle to keep in sync with the reference model
    always_ff @(posedge `RVFI_IF.clk) begin
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