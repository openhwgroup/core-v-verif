//
// Copyright 2020 OpenHW Group
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


`ifndef __UVMT_CV32_STEP_COMPARE_SV__
`define __UVMT_CV32_STEP_COMPARE_SV__

// Step-and-Compare between the CV32E40P and Imperas OVPsim ISS
// Cloned from the Imperas demo at $(IMPERAS_HOME)/RTL_OVPmodel_step_compare/verilog_testbench/testbench.sv

/*
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 * Copyright (C) Tumbush Enterprises, LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
 * either express or implied.
 *
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */

`ifdef COVERAGE
`include "class_coverage.svh" 
`endif

//
// Execute step and compare of dut ISS instance vs riscv RTL instance
//
`ifndef T0_TYPE
  `define T0_TYPE "RV32IMC"
`endif

import uvm_pkg::*;      // needed for the UVM messaging service (`uvm_info(), etc.)

`include "uvm_macros.svh"
`define CV32E40P_CORE   $root.uvmt_cv32_tb.dut_wrap.cv32e40p_wrapper_i.core_i
`define CV32E40P_TRACER $root.uvmt_cv32_tb.dut_wrap.cv32e40p_wrapper_i.tracer_i
`define CV32E40P_MMRAM  $root.uvmt_cv32_tb.dut_wrap.ram_i

`define CV32E40P_ISS $root.uvmt_cv32_tb.iss_wrap.cpu


module uvmt_cv32_step_compare
(
   uvma_clknrst_if            clknrst_if,
   uvmt_cv32_step_compare_if  step_compare_if
);

   bit  Clk;
   bit  miscompare;
   bit  is_stall_sim = 0;

  // Set the is_stall_sim flag if random stalls are enabled
  // This will turn off some unpredictable checks:
  // - CSR wire checks
  // - Non-written GPR registers (per instructions)
  // Note that register writebacks to GPRs will still be checked during each instruction retirement even with stalls
  always @(posedge clknrst_if.reset_n) begin
    is_stall_sim = `CV32E40P_MMRAM.is_stall_sim();
    if (is_stall_sim) begin
      `uvm_info("Step-andCompare", $sformatf("is_stall_sim set to 1, disabling CSR wire checks and stable GPR register checks"), UVM_NONE)
    end
  end

  function void check_32bit(input string compared, input bit [31:0] expected, input logic [31:0] actual);
      static int now = 0;
      if (now != $time) begin
        miscompare = 0;
        now = $time;
      end
      if (expected !== actual) begin
        miscompare = 1;
        `uvm_error("Step-and-Compare", $sformatf("%s expected=0x%8h and actual=0x%8h PC=0x%8h", compared, expected, actual, step_compare_if.ovp_cpu_PCr))
      end else begin
        `uvm_info("Step-and-Compare", $sformatf("%s expected=0x%8h==actual", compared, actual), UVM_DEBUG)
      end
   endfunction // check_32bit

   function automatic void compare();
      int idx;
      logic [ 5:0] insn_regs_write_addr;
      logic [31:0] insn_regs_write_value;
      int          insn_regs_write_size;
      string       compared_str;
      bit ignore;
      logic [31:0] csr_val;

      // Compare PC
      check_32bit(.compared("PC"), .expected(step_compare_if.ovp_cpu_PCr), 
                                   .actual(step_compare_if.insn_pc));
      step_compare_if.num_pc_checks++;

      // Compare GPR's
      // Assuming that `CV32E40P_TRACER.insn_regs_write size is never > 1.  Check this.
      // Note that dut_wrap is found 1 level up
      insn_regs_write_size = `CV32E40P_TRACER.insn_regs_write.size();
      if (insn_regs_write_size > 1) begin
        `uvm_error("Step-and-Compare",  $sformatf("Assume insn_regs_write size is 0 or 1 but is %0d", insn_regs_write_size))
      end
      else if (insn_regs_write_size == 1) begin // Get `CV32E40P_TRACER.insn_regs_write fields if size is 1
         insn_regs_write_addr  = `CV32E40P_TRACER.insn_regs_write[0].addr;
         insn_regs_write_value = `CV32E40P_TRACER.insn_regs_write[0].value;
         `uvm_info("Step-and-Compare", $sformatf("insn_regs_write queue[0] addr=0x%0x, value=0x%0x", insn_regs_write_addr, insn_regs_write_value), UVM_DEBUG)
      end
      
      // Ignore insn_regs_write_addr=0 just like in riscv_tracer.sv
      for (idx=0; idx<32; idx++) begin
         compared_str = $sformatf("GPR[%0d]", idx);
         if ((idx == insn_regs_write_addr) && (idx != 0) && (insn_regs_write_size == 1)) // Use register in insn_regs_write queue if it exists
            check_32bit(.compared(compared_str), .expected(step_compare_if.ovp_cpu_GPR[idx][31:0]), .actual(insn_regs_write_value));
         // FIXME:strichmo:I am removing the static (non-written) register checks, as they fail in presence of I and D bus RAM stalls
         // It would be highly desirable to find an alternative for this type of check to ensure unintended writes to do not
         else if (!is_stall_sim && !`CV32E40P_TRACER.insn_wb_bypass) // Use actual value from RTL to compare registers which should have not changed
            check_32bit(.compared(compared_str), .expected(step_compare_if.ovp_cpu_GPR[idx][31:0]), .actual(step_compare_if.riscy_GPR[idx]));
         step_compare_if.num_gpr_checks++;
      end

      // Compare CSR's
      `ifdef ISS
        foreach(iss_wrap.cpu.CSR[index]) begin
           step_compare_if.num_csr_checks++;
           ignore = 0;
           csr_val = 0;
           
           // CSR timing at instruction retirement is not completely deterministic in this simple model in presence of OBI stalls
           if (is_stall_sim)
            ignore = 1;
           case (index)
             "marchid"       : csr_val = cv32e40p_pkg::MARCHID; // warning!  defined in cv32e40p_pkg
             
             "mcountinhibit" : csr_val = `CV32E40P_CORE.cs_registers_i.mcountinhibit_q;

             "mvendorid"     : csr_val = {cv32e40p_pkg::MVENDORID_BANK, cv32e40p_pkg::MVENDORID_OFFSET};
             "mstatus"       : if (step_compare_if.deferint_prime == 0) ignore = 1;
                               else csr_val = {`CV32E40P_CORE.cs_registers_i.mstatus_q.mprv, // Not documented in Rev 4.5 of user_manual.doc but is in the design
                                          4'b0,
                                          `CV32E40P_CORE.cs_registers_i.mstatus_q.mpp,
                                          3'b0,
                                          `CV32E40P_CORE.cs_registers_i.mstatus_q.mpie,
                                          2'b0,
                                          `CV32E40P_CORE.cs_registers_i.mstatus_q.upie,
                                          `CV32E40P_CORE.cs_registers_i.mstatus_q.mie,
                                          2'b0,
                                          `CV32E40P_CORE.cs_registers_i.mstatus_q.uie};
             "misa"          : csr_val = `CV32E40P_CORE.cs_registers_i.MISA_VALUE;
             "mie"           : csr_val = `CV32E40P_CORE.cs_registers_i.mie_q;
             "mtvec"         : csr_val = {`CV32E40P_CORE.cs_registers_i.mtvec_q, 6'h0, `CV32E40P_CORE.cs_registers_i.mtvec_mode_q};
             "mscratch"      : csr_val = `CV32E40P_CORE.cs_registers_i.mscratch_q;                          
             "mepc"          : if (step_compare_if.deferint_prime == 0) ignore = 1;
                               else csr_val = `CV32E40P_CORE.cs_registers_i.mepc_q;             
             "mcause"        : if (step_compare_if.deferint_prime == 0) ignore = 1;
                               else csr_val = {`CV32E40P_CORE.cs_registers_i.mcause_q[5],
                                               26'b0,
                                               `CV32E40P_CORE.cs_registers_i.mcause_q[4:0]};
            //  "mip"           : if (step_compare_if.deferint_prime == 0 || iss_wrap.b1.deferint == 0) ignore = 1;
            //                    else csr_val = `CV32E40P_CORE.cs_registers_i.mip;
             "mip"           : ignore = 1;      
             "mhartid"       : csr_val = `CV32E40P_CORE.cs_registers_i.hart_id_i; 

             // only valid in DEBUG Mode
             "dcsr"          : begin
                               csr_val = `CV32E40P_CORE.cs_registers_i.dcsr_q;     
                               if (iss_wrap.b1.DM==0) ignore = 1;
             end
             "dpc"           : begin
                               csr_val = `CV32E40P_CORE.cs_registers_i.depc_q;       
                               if (iss_wrap.b1.DM==0) ignore = 1;
             end

             "dscratch0"     : csr_val = `CV32E40P_CORE.cs_registers_i.dscratch0_q;
             "dscratch1"     : csr_val = `CV32E40P_CORE.cs_registers_i.dscratch1_q;
             "pmpcfg0"       : csr_val = `CV32E40P_CORE.cs_registers_i.pmp_reg_q.pmpcfg_packed[0];
             "pmpcfg1"       : csr_val = `CV32E40P_CORE.cs_registers_i.pmp_reg_q.pmpcfg_packed[1];
             "pmpcfg2"       : csr_val = `CV32E40P_CORE.cs_registers_i.pmp_reg_q.pmpcfg_packed[2];
             "pmpcfg3"       : csr_val = `CV32E40P_CORE.cs_registers_i.pmp_reg_q.pmpcfg_packed[3];
             "tselect"       : csr_val = 32'h0000_0000;
             "tdata1"        : csr_val = `CV32E40P_CORE.cs_registers_i.tmatch_control_rdata;
             "tdata2"        : csr_val = `CV32E40P_CORE.cs_registers_i.tmatch_value_rdata;
             "tdata3"        : csr_val = 32'h0000_0000;
             "tinfo"         : csr_val = `CV32E40P_CORE.cs_registers_i.tinfo_types;
             "time"          : ignore  = 1;
             default: begin
                `uvm_error("STEP_COMPARE", $sformatf("index=%s does not match a CSR name", index))
                ignore = 1;
             end
           endcase // case (index)

           if (!ignore)
             check_32bit(.compared(index), .expected(iss_wrap.cpu.CSR[index]), .actual(csr_val));

        end // foreach (ovp.cpu.CSR[index])
        
      `endif      
    endfunction // compare
    
    // RTL->RM CSR : mcycle, minstret, mcycleh, minstreth
    function automatic void pushRTL2RM(string message);
        logic [ 5:0] gpr_addr;
        logic [31:0] gpr_value;
      
        if (`CV32E40P_TRACER.insn_regs_write.size()) begin
          gpr_addr  = `CV32E40P_TRACER.insn_regs_write[0].addr;
          gpr_value = `CV32E40P_TRACER.insn_regs_write[0].value;
          `CV32E40P_ISS.GPR_rtl[gpr_addr] = gpr_value;
        end
    endfunction // pushRTL2RM
    
    /*
        The schedule works like this
        1. Run the RTL for 1 instruction retirement
        2. if the RTL.RetiredPC == OVP.NextPC
           then run OVP for 1 instruction retirement
        3. Compare RTL <-> OVP
    */
    bit step_rtl = 0;
    bit step_ovp = 0;
    event ev_ovp, ev_rtl;
    event ev_compare;
    static integer instruction_count = 0;
   
    typedef enum {RESET,  // Needed to get an event on state so always block is initially entered
                  STEP_RTL,
                  STEP_OVP,
                  COMPARE} state_e; 

   state_e state;
   initial begin
      pushRTL2RM("Initial");
      step_compare_if.ovp_b1_Step <= 0;
      step_compare_if.ovp_b1_Stepping <= 1;
      step_ovp <= 0;
      step_rtl <= 1;
      state <= STEP_RTL;
   end
   
   always @(*) begin
      case (state)
        STEP_RTL: begin
           wait (step_compare_if.riscv_retire.triggered)
           clknrst_if.stop_clk();
           step_rtl <= 0;
           step_ovp <= 1;
           pushRTL2RM("ret_rtl");
           state <= STEP_OVP;
        end
        STEP_OVP: begin
           wait (step_compare_if.ovp_cpu_retire.triggered)
           step_ovp <= 0;
           ->ev_ovp; // not used
           ->`CV32E40P_TRACER.ovp_retire;
           state <= COMPARE;
        end
        COMPARE: begin 
           ->step_compare_if.ovp_cpu_busWait;
           compare();
           step_rtl <= 1;
           ->ev_compare;
           clknrst_if.start_clk();
           instruction_count += 1;           
           state <= STEP_RTL;
        end
      endcase // case (state)      
   end
   
    always @(step_ovp) begin
        step_compare_if.ovp_b1_Step = step_ovp;
    end

   always @(instruction_count) begin
      if (!(instruction_count % 10000)) begin
         `uvm_info("Step-and-Compare", $sformatf("Compared %0d instructions", instruction_count), UVM_NONE)
      end
      if (instruction_count >= 10_000_000) begin
         `uvm_fatal("Step-and-Compare", $sformatf("Compared %0d instructions - that's too long!", instruction_count))
      end
   end
   

`ifdef COVERAGE
   coverage cov1;
   initial begin
       cov1 = new();
   end

    function void split(input string in_s, output string s1, s2);
        automatic int i;
        for (i=0; i<in_s.len(); i++) begin
            if (in_s.getc(i) == ":")
                break;
         end
         if (i==0 ) begin
            `uvm_fatal("STEP COMPARE", $sformatf(": not found in split '%0s'", in_s))
         end
         s1 = in_s.substr(0,i-1);
         s2 = in_s.substr(i+1,in_s.len()-1);
    endfunction


    function automatic void sample();
        string decode = iss_wrap.cpu.Decode;
        string ins_str, op[4], key, val;
        int i;
        ins_t ins;
        int num = $sscanf (decode, "%s %s %s %s %s", ins_str, op[0], op[1], op[2], op[3]);
        ins.ins_str = ins_str;
        for (i=0; i<num-1; i++) begin
            split(op[i], key, val);
            ins.ops[i].key=key;
            ins.ops[i].val=val;
        end
        cov1.sample (ins);
    endfunction
`endif

endmodule: uvmt_cv32_step_compare

`endif //__UVMT_CV32_STEP_COMPARE_SV__
