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

`define DUT_PATH dut_wrap.cv32e40s_wrapper_i
`define RVFI_IF  `DUT_PATH.rvfi_instr_if

//`define STRINGIFY(x) `"x`"

//`ifdef USE_RM 

module rvfi_compare(
  rvfi_if_t rvfi_core,
  rvfi_if_t rvfi_rm
);


  //use assertion to compare the RVFI signals
  always_comb begin
    if (rvfi_rm.valid) begin
      assert #0 (rvfi_core.pc_rdata == rvfi_rm.pc_rdata ) 
        $display("RVFI PC match: core: %x, rm: %x", rvfi_core.pc_rdata, rvfi_rm.pc_rdata);
        else $error("RVFI PC mismatch: core: %x, rm: %x", rvfi_core.pc_rdata, rvfi_rm.pc_rdata);

      assert #0 (rvfi_core.insn == rvfi_rm.insn ) 
        else $error("RVFI insn mismatch: core: %x, rm: %x", rvfi_core.insn, rvfi_rm.insn);

      assert #0 (rvfi_core.trap == rvfi_rm.trap ) 
        else $error("RVFI trap mismatch: core: %x, rm: %x", rvfi_core.trap, rvfi_rm.trap);

      assert #0 (rvfi_core.halt == rvfi_rm.halt ) 
        else $error("RVFI halt mismatch: core: %x, rm: %x", rvfi_core.halt, rvfi_rm.halt);

      assert #0 (rvfi_core.dbg == rvfi_rm.dbg ) 
        else $error("RVFI dbg mismatch: core: %x, rm: %x", rvfi_core.dbg, rvfi_rm.dbg);

      assert #0 (rvfi_core.dbg_mode == rvfi_rm.dbg_mode ) 
        else $error("RVFI dbg_mode mismatch: core: %x, rm: %x", rvfi_core.dbg_mode, rvfi_rm.dbg_mode);

      assert #0 (rvfi_core.nmip == rvfi_rm.nmip ) 
        else $error("RVFI nmip mismatch: core: %x, rm: %x", rvfi_core.nmip, rvfi_rm.nmip);

      assert #0 (rvfi_core.intr == rvfi_rm.intr ) 
        else $error("RVFI intr mismatch: core: %x, rm: %x", rvfi_core.intr, rvfi_rm.intr);

      assert #0 (rvfi_core.mode == rvfi_rm.mode ) 
        else $error("RVFI mode mismatch: core: %x, rm: %x", rvfi_core.mode, rvfi_rm.mode);

      assert #0 (rvfi_core.ixl == rvfi_rm.ixl ) 
        else $error("RVFI ixl mismatch: core: %x, rm: %x", rvfi_core.ixl, rvfi_rm.ixl);

      assert #0 (rvfi_core.pc_rdata == rvfi_rm.pc_rdata ) 
        else $error("RVFI pc_rdata mismatch: core: %x, rm: %x", rvfi_core.pc_rdata, rvfi_rm.pc_rdata);

      assert #0 (rvfi_core.pc_wdata == rvfi_rm.pc_wdata ) 
        else $error("RVFI pc_wdata mismatch: core: %x, rm: %x", rvfi_core.pc_wdata, rvfi_rm.pc_wdata);

      assert #0 (rvfi_core.rs1_addr == rvfi_rm.rs1_addr ) 
        else $error("RVFI rs1_addr mismatch: core: %x, rm: %x", rvfi_core.rs1_addr, rvfi_rm.rs1_addr);

      assert #0 (rvfi_core.rs1_rdata == rvfi_rm.rs1_rdata ) 
        else $error("RVFI rs1_rdata mismatch: core: %x, rm: %x", rvfi_core.rs1_rdata, rvfi_rm.rs1_rdata);

      assert #0 (rvfi_core.rs2_addr == rvfi_rm.rs2_addr ) 
        else $error("RVFI rs2_addr mismatch: core: %x, rm: %x", rvfi_core.rs2_addr, rvfi_rm.rs2_addr);

      assert #0 (rvfi_core.rs2_rdata == rvfi_rm.rs2_rdata ) 
        else $error("RVFI rs2_rdata mismatch: core: %x, rm: %x", rvfi_core.rs2_rdata, rvfi_rm.rs2_rdata);

      assert #0 (rvfi_core.rs3_addr == rvfi_rm.rs3_addr ) 
        else $error("RVFI rs3_addr mismatch: core: %x, rm: %x", rvfi_core.rs3_addr, rvfi_rm.rs3_addr);

      assert #0 (rvfi_core.rs3_rdata == rvfi_rm.rs3_rdata ) 
        else $error("RVFI rs3_rdata mismatch: core: %x, rm: %x", rvfi_core.rs3_rdata, rvfi_rm.rs3_rdata);

      assert #0 (rvfi_core.rd1_addr == rvfi_rm.rd1_addr ) 
        else $error("RVFI rd1_addr mismatch: core: %x, rm: %x", rvfi_core.rd1_addr, rvfi_rm.rd1_addr);

      assert #0 (rvfi_core.rd1_wdata == rvfi_rm.rd1_wdata ) 
        else $error("RVFI rd1_wdata mismatch: core: %x, rm: %x", rvfi_core.rd1_wdata, rvfi_rm.rd1_wdata);

      assert #0 (rvfi_core.rd2_addr == rvfi_rm.rd2_addr ) 
        else $error("RVFI rd2_addr mismatch: core: %x, rm: %x", rvfi_core.rd2_addr, rvfi_rm.rd2_addr);

      assert #0 (rvfi_core.rd2_wdata == rvfi_rm.rd2_wdata ) 
        else $error("RVFI rd2_wdata mismatch: core: %x, rm: %x", rvfi_core.rd2_wdata, rvfi_rm.rd2_wdata);

      assert #0 (rvfi_core.mem_addr == rvfi_rm.mem_addr ) 
        else $error("RVFI mem_addr mismatch: core: %x, rm: %x", rvfi_core.mem_addr, rvfi_rm.mem_addr);

      assert #0 (rvfi_core.mem_rdata == rvfi_rm.mem_rdata ) 
        else $error("RVFI mem_rdata mismatch: core: %x, rm: %x", rvfi_core.mem_rdata, rvfi_rm.mem_rdata);

      assert #0 (rvfi_core.mem_rmask == rvfi_rm.mem_rmask ) 
        else $error("RVFI mem_rmask mismatch: core: %x, rm: %x", rvfi_core.mem_rmask, rvfi_rm.mem_rmask);

      assert #0 (rvfi_core.mem_wdata == rvfi_rm.mem_wdata ) 
        else $error("RVFI mem_wdata mismatch: core: %x, rm: %x", rvfi_core.mem_wdata, rvfi_rm.mem_wdata);

      assert #0 (rvfi_core.mem_wmask == rvfi_rm.mem_wmask ) 
        else $error("RVFI mem_wmask mismatch: core: %x, rm: %x", rvfi_core.mem_wmask, rvfi_rm.mem_wmask);

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
  //import rvviApiPkg::*;

    //uvma_rvfi_instr_if_t#(ILEN,XLEN) rvfi_o();  
    //st_rvfi rvfi_o;

    rvfi_if_t rvfi_o();
    rvfi_if_t rvfi_core();

    reference_model reference_model_i(
       .clk_i(`RVFI_IF.clk),
       .rvfi_i(`RVFI_IF),
       .rvfi_o(rvfi_o)
    );

    rvfi_compare rvfi_compare_i(
      .rvfi_core(rvfi_core),
      .rvfi_rm(rvfi_o)
    );

   string info_tag = "RM_wrap";

   uvme_cv32e40s_cfg_c  uvm_env_cfg;

   initial begin
     @(`RVFI_IF.clk);
     void'(uvm_config_db#(uvme_cv32e40s_cfg_c)::get(null, "uvm_test_top.env", "cfg", uvm_env_cfg));
     if (!uvm_env_cfg) begin
      `uvm_fatal(info_tag, "Configuration handle is null")
     end
     else begin
      `uvm_info(info_tag, $sformatf("Found UVM environment configuration handle:\n%s", uvm_env_cfg.sprint()), UVM_DEBUG)
     end
   end


    always_ff @(posedge `RVFI_IF.clk) begin

     if (rvfi_o.valid) begin
      rvfi_core.pc_rdata = `RVFI_IF.rvfi_pc_rdata;
      rvfi_core.insn = `RVFI_IF.rvfi_insn;
      rvfi_core.trap = `RVFI_IF.rvfi_trap;
      rvfi_core.halt = `RVFI_IF.rvfi_halt;
      rvfi_core.dbg = `RVFI_IF.rvfi_dbg;
      rvfi_core.dbg_mode = `RVFI_IF.rvfi_dbg_mode;
      rvfi_core.nmip = `RVFI_IF.rvfi_nmip;
      rvfi_core.intr = `RVFI_IF.rvfi_intr;
      rvfi_core.mode = `RVFI_IF.rvfi_mode;
      rvfi_core.ixl = `RVFI_IF.rvfi_ixl;
      rvfi_core.pc_rdata = `RVFI_IF.rvfi_pc_rdata;
      rvfi_core.pc_wdata = `RVFI_IF.rvfi_pc_wdata;
      rvfi_core.rs1_addr = `RVFI_IF.rvfi_rs1_addr;
      rvfi_core.rs1_rdata = `RVFI_IF.rvfi_rs1_rdata;
      rvfi_core.rs2_addr = `RVFI_IF.rvfi_rs2_addr;
      rvfi_core.rs2_rdata = `RVFI_IF.rvfi_rs2_rdata;
      rvfi_core.rs3_addr = `RVFI_IF.rvfi_rs3_addr;
      rvfi_core.rs3_rdata = `RVFI_IF.rvfi_rs3_rdata;
      rvfi_core.rd1_addr = `RVFI_IF.rvfi_rd1_addr;
      rvfi_core.rd1_wdata = `RVFI_IF.rvfi_rd1_wdata;
      rvfi_core.rd2_addr = `RVFI_IF.rvfi_rd2_addr;
      rvfi_core.rd2_wdata = `RVFI_IF.rvfi_rd2_wdata;
      rvfi_core.mem_addr = `RVFI_IF.rvfi_mem_addr;
      rvfi_core.mem_rdata = `RVFI_IF.rvfi_mem_rdata;
      rvfi_core.mem_rmask = `RVFI_IF.rvfi_mem_rmask;
      rvfi_core.mem_wdata = `RVFI_IF.rvfi_mem_wdata;
      rvfi_core.mem_wmask = `RVFI_IF.rvfi_mem_wmask;
     end
    end

    /*
   assign rvvi.clk            = `RVFI_IF.clk;
   assign rvvi.valid[0][0]    = `RVFI_IF.rvfi_valid;
   assign rvvi.order[0][0]    = `RVFI_IF.rvfi_order;
   assign rvvi.insn[0][0]     = `RVFI_IF.rvfi_insn;
   assign rvvi.trap[0][0]     =  (`RVFI_IF.rvfi_trap.trap && `RVFI_IF.rvfi_trap.exception == 1'b1)                                      || // Exceptions never retire
                                 (`RVFI_IF.rvfi_trap.trap && `RVFI_IF.rvfi_trap.debug == 1'b1 && `RVFI_IF.rvfi_trap.debug_cause == 'h1) || // Ebreak never retires
                                 (`RVFI_IF.rvfi_trap.trap && `RVFI_IF.rvfi_trap.debug == 1'b1 && `RVFI_IF.rvfi_trap.debug_cause == 'h2);   // Trigger match never retires
   assign rvvi.intr[0][0]     = `RVFI_IF.rvfi_intr;
   assign rvvi.mode[0][0]     = `RVFI_IF.rvfi_mode;
   assign rvvi.ixl[0][0]      = `RVFI_IF.rvfi_ixl;
   assign rvvi.pc_rdata[0][0] = `RVFI_IF.rvfi_pc_rdata;
   assign rvvi.pc_wdata[0][0] = `RVFI_IF.rvfi_pc_wdata;


   ////////////////////////////////////////////////////////////////////////////
   // Assign the RVVI GPR registers
   ////////////////////////////////////////////////////////////////////////////
   bit [31:0] XREG[32];
   genvar gi;
   generate
       for(gi=0; gi<32; gi++)
           assign rvvi.x_wdata[0][0][gi] = XREG[gi];
   endgenerate

   always_comb begin
     int i;
     if (|`RVFI_IF.rvfi_gpr_wmask[31:1] && `RVFI_IF.rvfi_valid) begin
       for (i=1; i<32; i++) begin
         if (`RVFI_IF.rvfi_gpr_wmask[i]) begin
           XREG[i] = `RVFI_IF.rvfi_gpr_wdata[i*XLEN+:XLEN];
         end
         else begin
           XREG[i] = 32'h0;
         end
       end
     end
   end

   assign rvvi.x_wb[0][0] = `RVFI_IF.rvfi_gpr_wmask;
*/

endmodule : uvmt_cv32e40s_reference_model_wrap

interface uvmt_reference_model_if_t;
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  import uvme_cv32e40s_pkg::*;
  //import rvviApiPkg::*;

  string info_tag = "reference_model_if";


  task ref_init;
    string test_program_elf;
    logic [31:0] hart_id;

    // Select processor name
    //void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_NAME, "CVE4S"));
    // Worst case propagation of events 4 retirements (actually 3 observed)
    //void'(rvviRefConfigSetInt(IDV_CONFIG_MAX_NET_LATENCY_RETIREMENTS, 4));
    // Redirect stdout to parent systemverilog simulator
    //void'(rvviRefConfigSetInt(IDV_CONFIG_REDIRECT_STDOUT, RVVI_TRUE));

    // Initialize REF and load the test-program into it's memory (do this before initializing the DUT).
    // TODO: is this the best place for this?
    //if (!rvviVersionCheck(RVVI_API_VERSION)) begin
    //  `uvm_fatal(info_tag, $sformatf("Expecting RVVI API version %0d.", RVVI_API_VERSION))
    //end
    //// Test-program must have been compiled before we got here...
    //if ($value$plusargs("elf_file=%s", test_program_elf)) begin
    //  `uvm_info(info_tag, $sformatf("RM loading test_program %0s", test_program_elf), UVM_LOW)
    //  //void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_VENDOR,  "openhwgroup.ovpworld.org"));
    //  //void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_VARIANT, "CV32E40S_DEV"));
    //  if (!rvviRefInit(test_program_elf)) begin
    //    `uvm_fatal(info_tag, "rvviRefInit failed")
    //  end
    //  else begin
    //    `uvm_info(info_tag, "rvviRefInit() succeed", UVM_LOW)
    //  end
    //end
    //else begin
    //  `uvm_fatal(info_tag, "No test_program specified")
    //end



    hart_id = 32'h0000_0000;

    `uvm_info(info_tag, "ref_init() complete", UVM_LOW)
  endtask // ref_init



endinterface : uvmt_reference_model_if_t

//`endif // USE_RM

`endif // __UVMT_CV32E40S_REFERENCE_MODEL_WRAP_SV__