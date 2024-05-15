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
  always_comb begin
    if (rvfi_rm.valid) begin
      


      check_32bit("PC", rvfi_core.pc_rdata, rvfi_rm.pc_rdata);

      check_32bit("insn", rvfi_core.insn, rvfi_rm.insn);

      check_32bit("trap", rvfi_core.trap, rvfi_rm.trap);

      check_32bit("halt", rvfi_core.halt, rvfi_rm.halt);

      check_32bit("dbg", rvfi_core.dbg, rvfi_rm.dbg);

      check_32bit("dbg_mode", rvfi_core.dbg_mode, rvfi_rm.dbg_mode);

      check_32bit("nmip", rvfi_core.nmip, rvfi_rm.nmip);

      check_32bit("intr", rvfi_core.intr, rvfi_rm.intr);

      check_32bit("mode", rvfi_core.mode, rvfi_rm.mode);

      //check_32bit("ixl", rvfi_core.ixl, rvfi_rm.ixl);

      //check_32bit("pc_wdata", rvfi_core.pc_wdata, rvfi_rm.pc_wdata);

      //check_32bit("rs1_addr", rvfi_core.rs1_addr, rvfi_rm.rs1_addr);

      //check_32bit("rs1_rdata", rvfi_core.rs1_rdata, rvfi_rm.rs1_rdata);

      //check_32bit("rs2_addr", rvfi_core.rs2_addr, rvfi_rm.rs2_addr);

      //check_32bit("rs2_rdata", rvfi_core.rs2_rdata, rvfi_rm.rs2_rdata);

      //check_32bit("rs3_addr", rvfi_core.rs3_addr, rvfi_rm.rs3_addr);

      //check_32bit("rs3_rdata", rvfi_core.rs3_rdata, rvfi_rm.rs3_rdata);



      //check_32bit("rd2_addr", rvfi_core.rd2_addr, rvfi_rm.rd2_addr);

      //check_32bit("rd2_wdata", rvfi_core.rd2_wdata, rvfi_rm.rd2_wdata);




      //Disable instructions with multiple memory accesses
      if(~(rvfi_core.mem_rmask[511:4] || rvfi_core.mem_wmask[511:4])) begin

        check_32bit("rd1_addr", rvfi_core.rd1_addr, rvfi_rm.rd1_addr);

        // rd1_wdata is not guaranteed to be 0 even though rd1_addr is 0
        if(rvfi_core.rd1_addr != 0) begin
          check_32bit("rd1_wdata", rvfi_core.rd1_wdata, rvfi_rm.rd1_wdata);
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
  //import rvviApiPkg::*;

    //uvma_rvfi_instr_if_t#(ILEN,XLEN) rvfi_o();  
    //st_rvfi rvfi_o;

    rvfi_if_t rvfi_o();
    rvfi_if_t rvfi_core();
    //int clock_cnt;

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


      //`uvm_info("RM count", $sformatf("PC: %x | CNT: %d", rvfi_core.pc_rdata, clock_cnt), UVM_NONE)

      //clock_cnt = 0;
     end
     else begin
      //clock_cnt = clock_cnt + 1;
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