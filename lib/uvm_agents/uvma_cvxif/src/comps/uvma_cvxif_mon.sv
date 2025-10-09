

// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)

`ifndef __UVMA_CVXIF_MON_SV__
`define __UVMA_CVXIF_MON_SV__


class uvma_cvxif_mon_c extends uvm_monitor;

   //objects
   uvma_cvxif_cfg_c    cfg;
   uvma_cvxif_cntxt_c  cntxt;

   // add to factory
   `uvm_component_utils_begin(uvma_cvxif_mon_c)
      `uvm_field_object(cfg,   UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   string info_tag = "CVXIF_MONITOR";

   int req_valid;

   uvm_analysis_port#(uvma_cvxif_req_item_c)  req_ap;
   uvm_analysis_port#(uvma_cvxif_resp_item_c) resp_ap;

   uvma_cvxif_req_item_c req_tr;
   uvma_cvxif_resp_item_c resp_tr;

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_cvxif_mon", uvm_component parent=null);

   /**
    * 1. Ensures vif handle is not null.
    * 2. Builds ap.
   */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Monitoring transaction
   */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Send transaction request to sequencer
   */
   extern task send_req_to_sqr(uvma_cvxif_req_item_c req);

   /**
    * Collect and send request items to sequencer
   */
   extern task collect_and_send_req(uvma_cvxif_req_item_c req_tr);

   /**
    * Collect and send response items to coverage model
   */
   extern task collect_and_send_resp(uvma_cvxif_resp_item_c resp_tr);

   /**
    * Observe reset state
   */
   extern task observe_reset();

   /**
    * Monitor pre-reset phase
    */
   extern virtual task mon_cvxif_pre_reset();

   /**
    * Monitor in-reset phase
    */
   extern virtual task mon_cvxif_in_reset();

   /**
    * Monitor post-reset phase
    */
   extern virtual task mon_cvxif_post_reset();

endclass : uvma_cvxif_mon_c

function uvma_cvxif_mon_c::new(string name="uvma_cvxif_mon", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

function void uvma_cvxif_mon_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_cvxif_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvma_cvxif_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   req_ap = new("req_ap", this);
   resp_ap = new("resp_ap", this);

endfunction : build_phase

task uvma_cvxif_mon_c::run_phase(uvm_phase phase);
   super.run_phase(phase);

   fork
      observe_reset();

      forever begin
         case (cntxt.reset_state)
            UVMA_CVXIF_RESET_STATE_PRE_RESET:  mon_cvxif_pre_reset();
            UVMA_CVXIF_RESET_STATE_IN_RESET:   mon_cvxif_in_reset();
            UVMA_CVXIF_RESET_STATE_POST_RESET: mon_cvxif_post_reset();
         endcase
      end
   join

endtask: run_phase

task uvma_cvxif_mon_c::mon_cvxif_post_reset();

   fork
      begin
         collect_and_send_resp(resp_tr);
      end
      begin
         collect_and_send_req(req_tr);
      end
   join_any

endtask

task uvma_cvxif_mon_c::mon_cvxif_in_reset();

   @(cntxt.vif.clk);

endtask

task uvma_cvxif_mon_c::mon_cvxif_pre_reset();

   @(cntxt.vif.clk);

endtask

task uvma_cvxif_mon_c::send_req_to_sqr(uvma_cvxif_req_item_c req);

   req_ap.write(req);

endtask : send_req_to_sqr

task uvma_cvxif_mon_c::collect_and_send_req(uvma_cvxif_req_item_c req_tr);

   forever begin
      // wait for a transaction
      if ((cntxt.vif.issue_valid && cntxt.vif.issue_ready) || (cntxt.vif.compressed_valid && cntxt.vif.compressed_ready)) begin
         req_tr = uvma_cvxif_req_item_c::type_id::create("req_tr");
         `uvm_info(info_tag, $sformatf("New transaction received"), UVM_HIGH);

         //Detect an issue_req transaction
         if (cntxt.vif.compressed_valid) begin
            req_tr.compressed_valid   = cntxt.vif.compressed_valid;
            req_tr.compressed_req.instr    = cntxt.vif.compressed_req.instr;
            req_tr.compressed_req.hartid   = cntxt.vif.compressed_req.hartid;
            `uvm_info(info_tag, $sformatf("New compressed valid transaction received"), UVM_HIGH);
            req_valid = 1;
         end

         //Detect an issue_req transaction
         if (cntxt.vif.issue_valid) begin
            req_tr.issue_valid         = cntxt.vif.issue_valid;
            req_tr.issue_req.instr     = cntxt.vif.issue_req.instr;
            req_tr.issue_req.hartid    = cntxt.vif.issue_req.hartid;
            req_tr.issue_req.id        = cntxt.vif.issue_req.id;
            `uvm_info(info_tag, $sformatf("New issue valid transaction received"), UVM_HIGH);
            req_valid = 1;
         end

         //Detect an issue_req transaction
         if (cntxt.vif.register_valid) begin
            req_tr.register_valid     = cntxt.vif.register_valid;
            req_tr.register.hartid    = cntxt.vif.register.hartid;
            req_tr.register.id        = cntxt.vif.register.id;
            for (int i = 0; i < X_NUM_RS; i++) begin
              if (cntxt.vif.register.rs_valid[i]) begin
                 req_tr.register.rs_valid[i]  = cntxt.vif.register.rs_valid[i];
                 req_tr.register.rs[i]        = cntxt.vif.register.rs[i];
              end
            end
            `uvm_info(info_tag, $sformatf("New register valid transaction received"), UVM_HIGH);
            req_valid = 1;
         end

         //Detect commit transaction
         if (cntxt.vif.commit_valid) begin
            req_tr.commit_valid           = cntxt.vif.commit_valid;
            req_tr.commit_req.hartid      = cntxt.vif.commit_req.hartid;
            req_tr.commit_req.id          = cntxt.vif.commit_req.id;
            req_tr.commit_req.commit_kill = cntxt.vif.commit_req.commit_kill;
            `uvm_info(info_tag, $sformatf("New commit valid transaction received"), UVM_HIGH);
            req_valid = 1;
         end

         if (req_valid) begin
            `uvm_info(info_tag, $sformatf("Sending req to sqr %p", req_tr), UVM_HIGH);
            send_req_to_sqr(req_tr);
            req_valid = 0;
         end
      end
      @(cntxt.vif.slv_cvxif_cb);
   end

endtask

task uvma_cvxif_mon_c::collect_and_send_resp(uvma_cvxif_resp_item_c resp_tr);

   forever begin
      fork
         begin
            wait (cntxt.vif.compressed_ready && cntxt.vif.compressed_valid);
               resp_tr = uvma_cvxif_resp_item_c::type_id::create("resp_tr");
               resp_tr.compressed_resp.accept  = cntxt.vif.compressed_resp.accept;
               resp_tr.compressed_resp.instr   = cntxt.vif.compressed_resp.instr;
               `uvm_info(info_tag, $sformatf("send compreseed resp"), UVM_HIGH);
         end
         begin
            wait (cntxt.vif.issue_ready && cntxt.vif.issue_valid);
               resp_tr = uvma_cvxif_resp_item_c::type_id::create("resp_tr");
               resp_tr.issue_resp.accept         = cntxt.vif.issue_resp.accept;
               resp_tr.issue_resp.writeback      = cntxt.vif.issue_resp.writeback;
               resp_tr.issue_resp.register_read  = cntxt.vif.issue_resp.register_read;
               `uvm_info(info_tag, $sformatf("send issue resp"), UVM_HIGH);
         end
         begin
            wait (cntxt.vif.result_valid && cntxt.vif.result_ready);
               resp_tr = uvma_cvxif_resp_item_c::type_id::create("resp_tr");
               resp_tr.result_valid     = cntxt.vif.result_valid;
               resp_tr.result.hartid    = cntxt.vif.result.hartid;
               resp_tr.result.id        = cntxt.vif.result.id;
               resp_tr.result.data      = cntxt.vif.result.data;
               resp_tr.result.rd        = cntxt.vif.result.rd;
               resp_tr.result.we        = cntxt.vif.result.we;
               `uvm_info(info_tag, $sformatf("send result resp"), UVM_HIGH);
         end
      join_any
      resp_ap.write(resp_tr);
      @(cntxt.vif.slv_cvxif_cb);
   end

endtask

task uvma_cvxif_mon_c::observe_reset();

   forever begin
      wait (cntxt.vif.reset_n === 0);
      cntxt.reset_state = UVMA_CVXIF_RESET_STATE_IN_RESET;
      `uvm_info(get_type_name(), $sformatf("RESET_STATE_IN_RESET"), UVM_NONE)
      wait (cntxt.vif.reset_n === 1);
      cntxt.reset_state = UVMA_CVXIF_RESET_STATE_POST_RESET;
      `uvm_info(get_type_name(), $sformatf("RESET_STATE_POST_RESET"), UVM_NONE)
   end

endtask : observe_reset

`endif // __UVMA_CVXIF_MON_SV__
