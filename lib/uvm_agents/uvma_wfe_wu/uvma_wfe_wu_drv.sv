//
// Copyright 2023 Silicon Labs Inc.
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


`ifndef __UVMA_WFE_WU_DRV_SV__
`define __UVMA_WFE_WU_DRV_SV__


/**
 * Component driving a wfe wakeup virtual interface (uvma_wfe_wu_if_t).
 */
class uvma_wfe_wu_drv_c extends uvm_driver#(
   .REQ(uvma_wfe_wu_seq_item_c),
   .RSP(uvma_wfe_wu_seq_item_c)
);

   // Objects
   uvma_wfe_wu_cfg_c    cfg;
   uvma_wfe_wu_cntxt_c  cntxt;

   // TLM
   uvm_analysis_port#(uvma_wfe_wu_seq_item_c)  ap;


   `uvm_component_utils_begin(uvma_wfe_wu_drv_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_wfe_wu_drv", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Obtains the reqs from the sequence item port and calls drv_req()
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Drives the virtual interface's (cntxt.vif) signals using req's contents.
    */
   extern task drv_req(uvma_wfe_wu_seq_item_c req);


endclass : uvma_wfe_wu_drv_c


function uvma_wfe_wu_drv_c::new(string name="uvma_wfe_wu_drv", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_wfe_wu_drv_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_wfe_wu_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   uvm_config_db#(uvma_wfe_wu_cfg_c)::set(this, "*", "cfg", cfg);

   void'(uvm_config_db#(uvma_wfe_wu_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   uvm_config_db#(uvma_wfe_wu_cntxt_c)::set(this, "*", "cntxt", cntxt);

   ap = new("ap", this);

endfunction : build_phase


task uvma_wfe_wu_drv_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   forever begin
      seq_item_port.get_next_item(req);
      `uvml_hrtbt()
      drv_req(req);
      ap.write(req);
      seq_item_port.item_done();
   end

endtask : run_phase


task uvma_wfe_wu_drv_c::drv_req(uvma_wfe_wu_seq_item_c req);
  `uvm_info("WFE_WU", $sformatf("Driving:\n%s", req.sprint()), UVM_HIGH);
  @(cntxt.vif.drv_cb);
  case (req.action)
    UVMA_WFE_WU_SEQ_ITEM_ACTION_ASSERT: begin
      cntxt.vif.drv_cb.wfe_wu <= 1'b1;
    end
    UVMA_WFE_WU_SEQ_ITEM_ACTION_DEASSERT: begin
      cntxt.vif.drv_cb.wfe_wu <= 1'b0;
    end
  endcase

endtask : drv_req

`endif // __UVMA_WFE_WU_DRV_SV__
