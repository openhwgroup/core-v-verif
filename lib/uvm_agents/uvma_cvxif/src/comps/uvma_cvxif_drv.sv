// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_DRV_SV__
`define __UVMA_CVXIF_DRV_SV__


class uvma_cvxif_drv_c extends uvm_driver #(uvma_cvxif_resp_item_c);

   uvma_cvxif_resp_item_c resp_item;

   // Objects
   uvma_cvxif_cfg_c    cfg;
   uvma_cvxif_cntxt_c  cntxt;

   int unsigned TIMEOUT = 0;

   `uvm_component_utils_begin(uvma_cvxif_drv_c)
      `uvm_field_object(cfg   , UVM_DEFAULT)
      `uvm_field_object(cntxt , UVM_DEFAULT)
   `uvm_component_utils_end

   string info_tag = "CVXIF_DRV";

   uvma_cvxif_resp_item_c resp_item_queue[$];
   uvma_cvxif_resp_item_c res_item;

   extern function new(string name="uvma_cvxif_drv", uvm_component parent=null);

   extern virtual function void build_phase(uvm_phase phase);

   extern virtual task reset_phase(uvm_phase phase);

   extern virtual task run_phase(uvm_phase phase);

   //Generate randomly the issue_ready signal
   extern virtual task gen_slv_random_ready();

   //Drive response
   extern virtual task drv_slv_resp(input uvma_cvxif_resp_item_c item);

   //Reject issue request
   extern virtual task reject_slv_resp();

   //Drive issue response
   extern virtual task drv_issue_resp(input uvma_cvxif_resp_item_c item);

   //Drive compressed response
   extern virtual task drv_compressed_resp(input uvma_cvxif_resp_item_c item);

   //De-assert issue response
   extern virtual task deassert_issue_resp();

   //De-assert compressed response
   extern virtual task deassert_compressed_resp();

   //Drive result response
   extern virtual task drv_slv_result_resp(input uvma_cvxif_resp_item_c item);

   //De-assert result signals
   extern virtual task deassert_slv_result();

   //Called by run_phase() while agent is in pre-reset state.
   extern task drv_cvxif_pre_reset();

   //Called by run_phase() while agent is in reset state.
   extern task drv_cvxif_in_reset();

   //Called by run_phase() while agent is in post-reset state.
   extern task drv_cvxif_post_reset();

   //Drive result in order
   extern task drv_result_in_order();

   //Drive result out of order
   extern task drv_result_out_of_order();

endclass : uvma_cvxif_drv_c

function uvma_cvxif_drv_c::new(string name="uvma_cvxif_drv", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

function void uvma_cvxif_drv_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_cvxif_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   uvm_config_db#(uvma_cvxif_cfg_c)::set(this, "*", "cfg", cfg);

   void'(uvm_config_db#(uvma_cvxif_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   uvm_config_db#(uvma_cvxif_cntxt_c)::set(this, "*", "cntxt", cntxt);

endfunction : build_phase

task uvma_cvxif_drv_c::reset_phase(uvm_phase phase);

   // init value of slave
   cntxt.vif.commit_valid             <= 0;
   cntxt.vif.commit_req.commit_kill   <= 0;
   cntxt.vif.commit_req.id            <= 0;

   cntxt.vif.issue_valid              <= 0;
   cntxt.vif.issue_req.hartid         <= 0;
   cntxt.vif.issue_req.id             <= 0;
   cntxt.vif.issue_req.instr          <= 0;
								      
   cntxt.vif.register_valid           <= 0;
   cntxt.vif.register.hartid          <= 0;
   cntxt.vif.register.id              <= 0;
   cntxt.vif.register.rs_valid        <= 0;

   cntxt.vif.compressed_valid         <= 0;
   cntxt.vif.compressed_req.hartid    <= 0;
   cntxt.vif.compressed_req.instr     <= 0;

endtask


task uvma_cvxif_drv_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   //Initial the interface before the CPU start
   deassert_issue_resp();
   deassert_compressed_resp();
   deassert_slv_result();

   forever begin
      case (cntxt.reset_state)
         UVMA_CVXIF_RESET_STATE_PRE_RESET : drv_cvxif_pre_reset ();
         UVMA_CVXIF_RESET_STATE_IN_RESET  : drv_cvxif_in_reset  ();
         UVMA_CVXIF_RESET_STATE_POST_RESET: drv_cvxif_post_reset();

         default: `uvm_fatal(get_type_name(), $sformatf("Invalid reset_state: %0d", cntxt.reset_state))
      endcase
   end

endtask : run_phase

task uvma_cvxif_drv_c::gen_slv_random_ready();

   fork
      forever begin
         if (cfg.issue_ready_mode == UVMA_CVXIF_ISSUE_READY_RANDOMIZED) begin
            cntxt.vif.issue_ready <= 1'b1;
            repeat(cfg.hold_issue_ready)     @(posedge cntxt.vif.clk);
            cntxt.vif.issue_ready <= 1'b0;
            repeat(cfg.hold_issue_not_ready) @(posedge cntxt.vif.clk);
         end
         else if (cfg.issue_ready_mode == UVMA_CVXIF_ISSUE_READY_FIX) begin
            @(posedge cntxt.vif.clk);
            cntxt.vif.issue_ready <= 1'b1;
         end
      end
      forever begin
         if (cfg.compressed_ready_mode == UVMA_CVXIF_COMPRESSED_READY_RANDOMIZED) begin
            cntxt.vif.compressed_ready <= 1'b1;
            repeat(cfg.hold_compressed_ready)     @(posedge cntxt.vif.clk);
            cntxt.vif.compressed_ready <= 1'b0;
            repeat(cfg.hold_compressed_not_ready) @(posedge cntxt.vif.clk);
         end
         else if (cfg.compressed_ready_mode == UVMA_CVXIF_COMPRESSED_READY_FIX) begin
            @(posedge cntxt.vif.clk);
            cntxt.vif.compressed_ready <= 1'b1;
         end
      end
   join_any

endtask

task uvma_cvxif_drv_c::drv_cvxif_post_reset();

   if (cfg.enabled_cvxif) begin
      fork
         begin
            gen_slv_random_ready();
         end
         forever begin
            // 1. Get the response item from sequencer
            resp_item = uvma_cvxif_resp_item_c::type_id::create("resp_item");
            seq_item_port.get_next_item(resp_item);
            `uvm_info(info_tag, $sformatf("Response : %p", resp_item), UVM_NONE);
            // delay response until all necessary register are provided
            if (resp_item.delay_resp) cntxt.vif.issue_ready <= 0;
            else drv_slv_resp(resp_item);

            //Tell sequencer we're ready for the next sequence item
            seq_item_port.item_done();
         end
         forever begin
            if (cfg.ordering_mode == UVMA_CVXIF_ORDERING_MODE_IN_ORDER) begin
               drv_result_in_order();
            end
            if (cfg.ordering_mode == UVMA_CVXIF_ORDERING_MODE_RANDOM) begin
               drv_result_out_of_order();
            end
         end
      join_any
   end
   //Disabling cvxif agent means the agent gonna reject all the request from the CPU
   else begin
    `uvm_info(info_tag, $sformatf("CVXIF Agent is disabled : All CPU Requests are rejected !!"), UVM_NONE);
    forever begin
       @(posedge cntxt.vif.clk);
       reject_slv_resp();
    end
   end

endtask

task uvma_cvxif_drv_c::drv_cvxif_pre_reset();

   deassert_issue_resp();
   deassert_compressed_resp();
   deassert_slv_result();
   @(posedge cntxt.vif.clk);

endtask : drv_cvxif_pre_reset


task uvma_cvxif_drv_c::drv_cvxif_in_reset();

   deassert_issue_resp();
   deassert_compressed_resp();
   deassert_slv_result();
   @(posedge cntxt.vif.clk);

endtask : drv_cvxif_in_reset

task uvma_cvxif_drv_c::drv_slv_resp(input uvma_cvxif_resp_item_c item);

   //issue_resp in same cycle as issue_req
   fork begin
      if (item.issue_valid) begin
         wait (cntxt.vif.issue_ready);
         drv_issue_resp(item);
         `uvm_info(info_tag, $sformatf("drive issue done !"), UVM_NONE);
         @(posedge cntxt.vif.clk);
         if (item.result_valid) begin
           resp_item_queue.push_back(item);
         end
         deassert_issue_resp();
      end
   end

   begin
     if (item.compressed_valid) begin
        wait (cntxt.vif.compressed_ready);
        drv_compressed_resp(item);
        `uvm_info(info_tag, $sformatf("drive compressed done !"), UVM_NONE);
         @(posedge cntxt.vif.clk);
        deassert_compressed_resp();
     end
   end
   join_none

endtask

task uvma_cvxif_drv_c::drv_issue_resp(input uvma_cvxif_resp_item_c item);

   cntxt.vif.issue_resp.accept        <= item.issue_resp.accept;
   cntxt.vif.issue_resp.writeback     <= item.issue_resp.writeback;
   cntxt.vif.issue_resp.register_read <= item.issue_resp.register_read;

endtask

task uvma_cvxif_drv_c::drv_compressed_resp(input uvma_cvxif_resp_item_c item);

   cntxt.vif.compressed_resp.accept   <= item.compressed_resp.accept;
   cntxt.vif.compressed_resp.instr    <= item.compressed_resp.instr;

endtask

task uvma_cvxif_drv_c::deassert_issue_resp();

   cntxt.vif.issue_resp.accept        <= 0;
   cntxt.vif.issue_resp.writeback     <= 0;
   cntxt.vif.issue_resp.register_read <= 0;

endtask

task uvma_cvxif_drv_c::deassert_compressed_resp();

   cntxt.vif.compressed_resp.accept   <= 0;
   cntxt.vif.compressed_resp.instr    <= 0;

endtask

task uvma_cvxif_drv_c::reject_slv_resp();

   cntxt.vif.issue_ready              <= 1;
   cntxt.vif.issue_resp.accept        <= 0;
   cntxt.vif.issue_resp.writeback     <= 0;
   cntxt.vif.issue_resp.register_read <= 0;
   cntxt.vif.compressed_ready         <= 1;
   cntxt.vif.compressed_resp.accept   <= 0;
   cntxt.vif.compressed_resp.instr    <= 0;

endtask

task uvma_cvxif_drv_c::drv_slv_result_resp(input uvma_cvxif_resp_item_c item);

   if (item.result_valid) begin
     cntxt.vif.result_valid   <= item.result_valid;
     cntxt.vif.result.hartid  <= item.result.hartid;
     cntxt.vif.result.id      <= item.result.id;
     cntxt.vif.result.rd      <= item.result.rd;
     cntxt.vif.result.data    <= item.result.data;
     cntxt.vif.result.we      <= item.result.we;
   end

   `uvm_info(info_tag, $sformatf("Driving result_resp, id = %d", item.result.id), UVM_NONE);

endtask

task uvma_cvxif_drv_c::drv_result_in_order();

   wait (resp_item_queue.size() != 0);
   repeat (cfg.instr_delayed) @(posedge cntxt.vif.clk);
   res_item = resp_item_queue.pop_front();
   if (res_item.result_valid) begin
     while (!cntxt.vif.result_ready) @(posedge cntxt.vif.clk);
     drv_slv_result_resp(res_item);
     @(posedge cntxt.vif.clk);
     deassert_slv_result();
   end

endtask

task uvma_cvxif_drv_c::drv_result_out_of_order();

   if (resp_item_queue.size() == MAX_ELEMENT_TO_DRIVE || TIMEOUT == 0) begin
      resp_item_queue.shuffle();
      foreach(resp_item_queue[i]) begin
        while (!cntxt.vif.result_ready) @(posedge cntxt.vif.clk);
        repeat (cfg.instr_delayed) @(posedge cntxt.vif.clk);
        drv_slv_result_resp(resp_item_queue[i]);
        @(posedge cntxt.vif.clk);
        deassert_slv_result();
      end
      resp_item_queue.delete();
      TIMEOUT = TIME_TO_WAIT_UNTIL_DRIVE;
   end
   else begin
      TIMEOUT--;
      @(posedge cntxt.vif.clk);
   end

endtask

task uvma_cvxif_drv_c::deassert_slv_result();

   cntxt.vif.result_valid   <= 0;
   cntxt.vif.result.hartid  <= 0;
   cntxt.vif.result.id      <= 0;
   cntxt.vif.result.rd      <= 0;
   cntxt.vif.result.data    <= 0;
   cntxt.vif.result.we      <= 0;

endtask


`endif // __UVMA_CVXIF_DRV_SV__
