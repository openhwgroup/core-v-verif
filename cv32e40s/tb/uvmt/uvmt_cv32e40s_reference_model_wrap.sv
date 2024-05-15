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

`define DUT_PATH dut_wrap.cv32e40s_wrapper_i
`define RVFI_IF  `DUT_PATH.rvfi_instr_if

//`define STRINGIFY(x) `"x`"

//`ifdef USE_RM 

//`include "reference_model.sv"

module uvmt_cv32e40s_reference_model_wrap
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  import uvme_cv32e40s_pkg::*;
  import uvma_rvfi_pkg::*;

  import rvviApiPkg::*;
  #(
   )

   (
           rvviTrace rvvi // RVVI SystemVerilog Interface
   );

    uvma_rvfi_instr_if_t#(ILEN,XLEN) rvfi_o();  

    reference_model reference_model_i(
       .clk_i(`RVFI_IF.clk),
       .rvfi_i(`RVFI_IF),
       .rvfi_o(rvfi_o)
    );

   string info_tag = "RM_wrap";

   uvme_cv32e40s_cfg_c  uvm_env_cfg;

   initial begin
     @(rvvi.clk);
     void'(uvm_config_db#(uvme_cv32e40s_cfg_c)::get(null, "uvm_test_top.env", "cfg", uvm_env_cfg));
     if (!uvm_env_cfg) begin
      `uvm_fatal(info_tag, "Configuration handle is null")
     end
     else begin
      `uvm_info(info_tag, $sformatf("Found UVM environment configuration handle:\n%s", uvm_env_cfg.sprint()), UVM_DEBUG)
     end
   end

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


endmodule : uvmt_cv32e40s_reference_model_wrap

interface uvmt_reference_model_if_t;
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  import uvme_cv32e40s_pkg::*;
  import rvviApiPkg::*;

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