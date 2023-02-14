//
// Copyright 2022 OpenHW Group
// Copyright 2022 Imperas
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


`ifndef __UVMT_CV32E40P_IMPERAS_DV_WRAP_SV__
`define __UVMT_CV32E40P_IMPERAS_DV_WRAP_SV__

`define DUT_PATH dut_wrap.cv32e40p_tb_wrapper_i
`define RVFI_IF  `DUT_PATH.rvfi_i

module uvmt_cv32e40p_imperas_dv_wrap

  `include "rvvi/imperasDV.svh" // located in $IMPERAS_HOME/ImpProprietary/include/host
  import uvm_pkg::*;
  import cv32e40p_pkg::*;
  import uvme_cv32e40p_pkg::*;
  import uvmt_cv32e40p_pkg::*;
  import rvviApiPkg::*;
  #(
   )

   (
           rvviTrace  rvvi // RVVI SystemVerilog Interface
   );
   trace2api       #(.CMP_PC      (1),
                   .CMP_INS     (1),
                   .CMP_GPR     (1),
                   .CMP_FPR     (0),
                   .CMP_VR      (0),
                   .CMP_CSR     (0)
                   )
                   trace2api(rvvi);

  trace2log trace2log_i (rvvi);

   string info_tag = "ImperasDV_wrap";

   ////////////////////////////////////////////////////////////////////////////
   // Adopted from:
   // ImperasDV/examples/openhwgroup_cv32e40x/systemverilog/cv32e40x_testbench.sv
   //
   // InstrunctionBusFault(48) is in fact a TRAP which is derived externally
   // This is strange as other program TRAPS are derived by the model, for now
   // We have to ensure we do not step the REF model for this TRAP as it will
   // Step too far. So instead we block it as being VALID, but pass on the
   // signals.
   // maybe we need a different way to communicate this to the model, for
   // instance the ability to register a callback on fetch, in order to assert
   // this signal.
   ////////////////////////////////////////////////////////////////////////////
   assign rvvi.clk            = `RVFI_IF.clk_i;
   assign rvvi.valid[0][0]    = `RVFI_IF.rvfi_valid;
   assign rvvi.order[0][0]    = `RVFI_IF.rvfi_order;
   assign rvvi.insn[0][0]     = `RVFI_IF.rvfi_insn;
   assign rvvi.trap[0][0]     = `RVFI_IF.rvfi_trap.trap;
   assign rvvi.intr[0][0]     = `RVFI_IF.rvfi_intr;
   assign rvvi.mode[0][0]     = `RVFI_IF.rvfi_mode;
   assign rvvi.ixl[0][0]      = `RVFI_IF.rvfi_ixl;
   assign rvvi.pc_rdata[0][0] = `RVFI_IF.rvfi_pc_rdata;
  //  assign rvvi.pc_wdata[0][0] = `RVFI_IF.rvfi_pc_wdata;
   ////////////////////////////////////////////////////////////////////////////
   // Assign the RVVI GPR registers
   ////////////////////////////////////////////////////////////////////////////
   bit [31:0] XREG[32];
   genvar gi;
   generate
       for(gi=0; gi<32; gi++)
           assign rvvi.x_wdata[0][0][gi] = XREG[gi];
   endgenerate

   always @(*) begin
       int i;
       for (i=1; i<32; i++) begin
           XREG[i] = 32'b0;
           // TODO: This current RVFI implementation will only allow a single destination
           //       register to be written. For some instructions this is not sufficient
           //       This code will need enhancing once the RVFI has the ability to describe
           //       multiple target register writes, for a single instruction
           if (`RVFI_IF.rvfi_rd_addr==5'(i))
               XREG[i] = `RVFI_IF.rvfi_rd_wdata;
       end
   end

   assign rvvi.x_wb[0][0] = 1 << `RVFI_IF.rvfi_rd_addr; // TODO: originally rvfi_rd_addr

  /////////////////////////////////////////////////////////////////////////////
  // REF control
  /////////////////////////////////////////////////////////////////////////////
  task ref_init;
    string test_program_elf;
    reg [31:0] hart_id;

    // Select processor name
    void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_NAME, "CV32E40P"));
    // Worst case propagation of events 4 retirements (actually 3 observed)
    void'(rvviRefConfigSetInt(IDV_CONFIG_MAX_NET_LATENCY_RETIREMENTS, 4));
    // Redirect stdout to parent systemverilog simulator
    void'(rvviRefConfigSetInt(IDV_CONFIG_REDIRECT_STDOUT, RVVI_TRUE));

    // Initialize REF and load the test-program into it's memory (do this before initializing the DUT).
    // TODO: is this the best place for this?
    if (!rvviVersionCheck(RVVI_API_VERSION)) begin
      `uvm_fatal(info_tag, $sformatf("Expecting RVVI API version %0d.", RVVI_API_VERSION))
    end
    // Test-program must have been compiled before we got here...
    if ($value$plusargs("elf_file=%s", test_program_elf)) begin
      `uvm_info(info_tag, $sformatf("ImperasDV loading test_program %0s", test_program_elf), UVM_NONE)
      void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_VENDOR,  "openhwgroup.ovpworld.org"));
      void'(rvviRefConfigSetString(IDV_CONFIG_MODEL_VARIANT, "CV32E40P"));
      if (!rvviRefInit(test_program_elf)) begin
        `uvm_fatal(info_tag, "rvviRefInit failed")
      end
      else begin
        `uvm_info(info_tag, "rvviRefInit() succeed", UVM_NONE)
      end
    end
    else begin
      `uvm_fatal(info_tag, "No test_program specified")
    end

    hart_id = 32'h0000_0000;

  endtask // ref_init
endmodule : uvmt_cv32e40s_imperas_dv_wrap
`endif // __UVMT_CV32E40P_IMPERAS_DV_WRAP_SV__