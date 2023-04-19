// Copyright 2023 Silicon Labs, Inc.
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


////////////////////////////////////////////////////////////////////////////////
// Author:  Henrik Fegran - henrik.fegran@silabs.com                          //
//                                                                            //
// Virtual sequence to ensure that random tests encountering                  //
// nmi terminates correctly after a set timeout                               //
//                                                                            //
// Usage: Set nmi_timeout_instr plusarg to non-zero value                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
`ifndef __UVME_CV32E40S_NMI_TIMEOUT_VSEQ_SV__
`define __UVME_CV32E40S_NMI_TIMEOUT_VSEQ_SV__


/**
 * Virtual sequence responsible for terminating test n cycles after an nmi
 */
class uvme_cv32e40s_nmi_timeout_vseq_c extends uvme_cv32e40s_base_vseq_c;

   uvme_cv32e40s_cntxt_c cv32e40s_cntxt;


   `uvm_object_utils(uvme_cv32e40s_nmi_timeout_vseq_c)

   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40s_nmi_timeout_vseq");

   /**
    * Waits for a configured number of instructions after an nmi.
    */
   extern virtual task body();

endclass : uvme_cv32e40s_nmi_timeout_vseq_c


function uvme_cv32e40s_nmi_timeout_vseq_c::new(string name="uvme_cv32e40s_nmi_timeout_vseq");

   super.new(name);

endfunction : new


task uvme_cv32e40s_nmi_timeout_vseq_c::body();

   if (cntxt == null) begin
     `uvm_fatal("E40SVPSTATUS", "Must initialize cntxt in virtual sequence")
   end

   if (cfg.nmi_timeout_instr > 0) begin
     fork
       forever begin
         @(posedge cntxt.rvfi_cntxt.instr_vif[0].clk) begin
           if (cntxt.rvfi_cntxt.instr_vif[0].rvfi_valid) begin
             if (cntxt.rvfi_cntxt.instr_vif[0].nmi_instr_cnt >= cfg.nmi_timeout_instr) begin
               `uvm_info("NMI_TIMEOUT_WATCHDOG", $sformatf("NMI timeout: %0d", cntxt.rvfi_cntxt.instr_vif[0].nmi_instr_cnt), UVM_LOW);
               cntxt.vp_status_vif.exit_valid = 1;
               cntxt.vp_status_vif.exit_value = 32'h0;
             end
           end
         end
       end
     join
   end

endtask : body


`endif // __UVME_CV32E40S_NMI_TIMEOUT_VSEQ_SV__
