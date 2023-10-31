//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2022 Silicon Labs, Inc.
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

`ifndef __UVMA_CLIC_DRV_SV__
`define __UVMA_CLIC_DRV_SV__

/**
 * Component driving a Clock & Reset virtual interface (uvma_clic_if_t).
 */
class uvma_clic_drv_c#(CLIC_ID_WIDTH) extends uvm_driver#(
   .REQ(uvma_clic_seq_item_c),
   .RSP(uvma_clic_seq_item_c)
);

   // Objects
   uvma_clic_cfg_c                    cfg;
   uvma_clic_cntxt_c#(CLIC_ID_WIDTH)  cntxt;

   semaphore               assert_until_ack_sem[4096];

   // TLM
   uvm_analysis_port#(uvma_clic_seq_item_c)  ap;

   `uvm_component_utils_begin(uvma_clic_drv_c#(CLIC_ID_WIDTH))
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_clic_drv", uvm_component parent=null);

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
    * Thread that clears acknowledged interrupts that were randomly asserted
    */
   extern task irq_ack_clear();

   /**
    * Drives the virtual interface's (cntxt.vif) signals using req's contents.
    */
   extern task drv_req(uvma_clic_seq_item_c req);

   /**
    * Forked thread to handle interrupts
    */
   extern task assert_irq_until_ack(uvma_clic_seq_item_c req);

   /**
    * Assert an interrupt signal
    */
   extern task assert_irq(uvma_clic_seq_item_c req);

   /**
    * Deassert an interrupt signal
    */
   extern task deassert_irq(uvma_clic_seq_item_c req);

endclass : uvma_clic_drv_c

function uvma_clic_drv_c::new(string name="uvma_clic_drv", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_clic_drv_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_clic_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   uvm_config_db#(uvma_clic_cfg_c)::set(this, "*", "cfg", cfg);

   void'(uvm_config_db#(uvma_clic_cntxt_c#(CLIC_ID_WIDTH))::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   uvm_config_db#(uvma_clic_cntxt_c#(CLIC_ID_WIDTH))::set(this, "*", "cntxt", cntxt);

   ap = new("ap", this);

   foreach (assert_until_ack_sem[i]) begin
      assert_until_ack_sem[i] = new(1);
   end
endfunction : build_phase


task uvma_clic_drv_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   // Enable the driver in the interface
   cntxt.vif.is_active = cfg.enabled;
   cntxt.vif.is_mmode_irq_only = cfg.is_mmode_irq_only;

   // Fork thread to deassert randomly asserted clics when acknowledged
   if (cfg.clear_irq_on_ack) begin
     fork
        irq_ack_clear();
     join_none
   end

   forever begin
      seq_item_port.get_next_item(req);
      `uvml_hrtbt()
      drv_req(req);
      ap.write(req);
      seq_item_port.item_done();
   end

endtask : run_phase

task uvma_clic_drv_c::drv_req(uvma_clic_seq_item_c req);
   `uvm_info("CLICDRV", $sformatf("Driving:\n%s", req.sprint()), UVM_HIGH);
   case (req.action)
      UVMA_CLIC_SEQ_ITEM_ACTION_ASSERT_UNTIL_ACK: begin
         assert_irq_until_ack(req);
      end
      UVMA_CLIC_SEQ_ITEM_ACTION_ASSERT: begin
         assert_irq(req);
      end
      UVMA_CLIC_SEQ_ITEM_ACTION_DEASSERT: begin
         deassert_irq(req);
      end
   endcase

endtask : drv_req

task uvma_clic_drv_c::assert_irq_until_ack(uvma_clic_seq_item_c req);
   // If a thread is already running on this irq, then exit
   if (!assert_until_ack_sem[req.index].try_get(1))
      return;

   repeat (req.skew) @(cntxt.vif.drv_cb);

   for (int loop = 0; loop < req.repeat_count; loop++) begin
      repeat (req.skew) @(cntxt.vif.drv_cb);
      cntxt.vif.drv_cb.clic_irq_drv       <= 1'b1;
      cntxt.vif.drv_cb.clic_irq_id_drv    <= req.index;
      cntxt.vif.drv_cb.clic_irq_shv_drv   <= req.sel_hardware_vectoring;
      cntxt.vif.drv_cb.clic_irq_priv_drv  <= req.privilege_mode;
      cntxt.vif.drv_cb.clic_irq_level_drv <= req.level;

      while (1) begin
         @(cntxt.vif.mon_cb);
         if (cntxt.vif.mon_cb.irq_ack) begin
            break;
         end
      end
   end

   `uvm_info("CLICDRV", $sformatf("assert_irq_until_ack: Deasserting irq: %0d", req.index), UVM_DEBUG);
   cntxt.vif.drv_cb.clic_irq_drv       <= 1'b0;
   cntxt.vif.drv_cb.clic_irq_id_drv    <= req.index;
   cntxt.vif.drv_cb.clic_irq_shv_drv   <= req.sel_hardware_vectoring;
   cntxt.vif.drv_cb.clic_irq_priv_drv  <= req.privilege_mode;
   cntxt.vif.drv_cb.clic_irq_level_drv <= req.level;
   assert_until_ack_sem[req.index].put(1);
endtask : assert_irq_until_ack

task uvma_clic_drv_c::assert_irq(uvma_clic_seq_item_c req);
   if (assert_until_ack_sem[req.index].try_get(1)) begin
      repeat (req.skew) @(cntxt.vif.drv_cb);
      cntxt.vif.drv_cb.clic_irq_drv       <= 1'b1;
      cntxt.vif.drv_cb.clic_irq_id_drv    <= req.index;
      cntxt.vif.drv_cb.clic_irq_shv_drv   <= req.sel_hardware_vectoring;
      cntxt.vif.drv_cb.clic_irq_priv_drv  <= req.privilege_mode;
      cntxt.vif.drv_cb.clic_irq_level_drv <= req.level;
      assert_until_ack_sem[req.index].put(1);
      return;
   end
endtask : assert_irq

task uvma_clic_drv_c::deassert_irq(uvma_clic_seq_item_c req);
   if (assert_until_ack_sem[req.index].try_get(1)) begin
      repeat (req.skew) @(cntxt.vif.drv_cb);
      cntxt.vif.drv_cb.clic_irq_drv       <= 1'b0;
      cntxt.vif.drv_cb.clic_irq_id_drv    <= req.index;
      cntxt.vif.drv_cb.clic_irq_shv_drv   <= req.sel_hardware_vectoring;
      cntxt.vif.drv_cb.clic_irq_priv_drv  <= req.privilege_mode;
      cntxt.vif.drv_cb.clic_irq_level_drv <= req.level;
      assert_until_ack_sem[req.index].put(1);
      return;
   end
endtask : deassert_irq

task uvma_clic_drv_c::irq_ack_clear();
   while(1) begin
      @(cntxt.vif.mon_cb);
      if (cntxt.vif.mon_cb.irq_ack && cfg.enabled) begin
         // Try to get the semaphore for the irq_id,
         // If we can't get it, then this irq is managed by assert_irq_until_ack and we will ignore this ack
         // Otherwise deassert the interrupt
         int unsigned irq_id;

         irq_id  = cntxt.vif.mon_cb.clic_irq_id_drv;

         `uvm_info("IRQDRV", $sformatf("irq_ack_clear: ack for IRQ: %0d", irq_id), UVM_DEBUG);
         if (assert_until_ack_sem[irq_id].try_get(1)) begin
            `uvm_info("IRQDRV", $sformatf("irq_ack_clear: Clearing IRQ: %0d", irq_id), UVM_DEBUG);
            cntxt.vif.drv_cb.clic_irq_drv       <= 1'b0;
            cntxt.vif.drv_cb.clic_irq_id_drv    <= 11'b0;
            cntxt.vif.drv_cb.clic_irq_shv_drv   <= 1'b0;
            cntxt.vif.drv_cb.clic_irq_priv_drv  <= 2'b00;
            cntxt.vif.drv_cb.clic_irq_level_drv <= 8'b0;
            assert_until_ack_sem[irq_id].put(1);
         end
      end
   end
endtask

`endif // __UVMA_CLIC_DRV_SV__
