// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_COV_MODEL_SV__
`define __UVMA_CVXIF_COV_MODEL_SV__

   /*
   * Covergroups
   * Decalred at package-level to enable mutliple instances per monitor class (e.g. read/write)
   */
   //covergroup instances

covergroup cg_request(
    string name
    ) with function sample(uvma_cvxif_req_item_c req_item);

    option.per_instance = 1;
    option.name = name;

   cp_compressed_valid : coverpoint req_item.compressed_valid {
    bins COMPRESSED_VALID = {1};
   }

   cp_issue_valid : coverpoint req_item.issue_valid {
    bins ISSUE_VALID = {1};
   }

   cp_issue_id : coverpoint req_item.issue_req.id {
    bins ID [] = {[0:$]};
   }

   cp_rs_valid : coverpoint req_item.register.rs_valid {
    ignore_bins IGN_BINS = {3'b111} with (X_NUM_RS == 2);
    bins RS_VALID_2  = {2'b11};
    bins RS_VALID_3  = {3'b111};
   }

   cp_commit_id : coverpoint req_item.commit_req.id {
    bins ID_COMMIT [] = {[0:$]};
   }

   cp_commit_kill : coverpoint req_item.commit_req.commit_kill {
    bins COMMIT_KILL [] = {[0:$]};
   }

   cp_commit_valid : coverpoint req_item.commit_valid {
    bins COMMIT_VALID = {1};
   }

   cross_issue_req : cross cp_issue_valid, cp_issue_id, cp_rs_valid {
     ignore_bins IGN_BINS = binsof(cp_issue_valid) intersect{0};
   }

   cross_commit_req : cross cp_commit_valid, cp_commit_kill, cp_commit_id {
     ignore_bins IGN_BINS = binsof(cp_commit_valid) intersect{0};
   }

endgroup: cg_request

covergroup cg_response(
    string name
    ) with function sample(uvma_cvxif_resp_item_c resp_item);

    option.per_instance = 1;
    option.name = name;

   cp_issue_accept : coverpoint resp_item.issue_resp.accept {
    bins ISSUE_ACCEPT [] = {[0:$]};
   }

   cp_writeback : coverpoint resp_item.issue_resp.writeback {
    bins WRITEBACK [] = {[0:$]};
   }

   cp_register_read : coverpoint resp_item.issue_resp.register_read {
    bins REGISTER_READ [] = {[0:$]};
   }

   cp_compressed_accept : coverpoint resp_item.issue_resp.accept {
    bins COMPRESSED_ACCEPT [] = {[0:$]};
   }

   cross_resp : cross cp_issue_accept, cp_writeback, cp_register_read {
    ignore_bins IGN_ACCEPT0 = binsof(cp_issue_accept) intersect{0};
    ignore_bins IGN_WRITEBACK1 = binsof(cp_writeback) intersect{1} && binsof(cp_register_read) intersect{0};
    ignore_bins IGN_WRITEBACK0 = binsof(cp_writeback) intersect{0} && !binsof(cp_register_read) intersect{0};
   }

endgroup: cg_response

covergroup cg_result(
    string name
    ) with function sample(uvma_cvxif_resp_item_c resp_item);

    option.per_instance = 1;
    option.name = name;

   cp_result_valid : coverpoint resp_item.result.id {
    bins RESULT_VALID = {1};
   }

   cp_result_id : coverpoint resp_item.result.id {
    bins ID [] = {[0:$]};
   }

   cp_rd : coverpoint resp_item.result.rd {
    bins RD [] = {[0:31]};
   }

   `CVXIF_CP_BITWISE_PER_CP_IFF(cp_data_toggle, resp_item.result.data, 1)

   cp_we : coverpoint resp_item.result.we {
    bins WE [] = {[0:$]};
   }

   cross_result : cross cp_result_valid, cp_result_id, cp_we, cp_rd {
    ignore_bins IGN_RESULT_VALID0 = binsof(cp_result_valid) intersect{0};
    ignore_bins IGN_WE0           = binsof(cp_result_valid) intersect{1} && binsof(cp_we) intersect{0};
   }
endgroup: cg_result

class uvma_cvxif_cov_model_c extends uvm_component;

   // Objects
   uvma_cvxif_cfg_c         cfg      ;
   uvma_cvxif_cntxt_c       cntxt    ;

   // TLM
   uvm_tlm_analysis_fifo#(uvma_cvxif_req_item_c )  req_item_fifo;
   uvm_tlm_analysis_fifo#(uvma_cvxif_resp_item_c)  resp_item_fifo;

   `uvm_component_utils_begin(uvma_cvxif_cov_model_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   cg_request request_cg;
   cg_response response_cg;
   cg_result result_cg;
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_cvxif_cov_model", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds fifos.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Forks all sampling loops
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * TODO Describe uvma_cvxif_cov_model_c::sample_req_item()
    */
   extern function void sample_req_item(uvma_cvxif_req_item_c req_item);

   /**
    * TODO Describe uvma_cvxif_cov_model_c::sample_resp_item()
    */
   extern function void sample_resp_item(uvma_cvxif_resp_item_c resp_item);

endclass : uvma_cvxif_cov_model_c

function uvma_cvxif_cov_model_c::new(string name="uvma_cvxif_cov_model", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_cvxif_cov_model_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_cvxif_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvma_cvxif_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   request_cg  = new("request_cg");
   response_cg = new("response_cg");
   result_cg   = new("result_cg");

   req_item_fifo   = new("req_item_fifo" , this);
   resp_item_fifo  = new("resp_item_fifo", this);

endfunction : build_phase


task uvma_cvxif_cov_model_c::run_phase(uvm_phase phase);


   uvma_cvxif_req_item_c    req_item ;
   uvma_cvxif_resp_item_c   resp_item;

   super.run_phase(phase);
   if (cfg.enabled_cvxif && cfg.cov_model_enabled) begin
      fork
         // 'mstr' sequence items
         forever begin
            req_item_fifo.get(req_item);
            sample_req_item(req_item);
         end

         // 'slv' sequence items
          forever begin
            resp_item_fifo.get(resp_item);
            sample_resp_item(resp_item);
         end
      join_none
   end

endtask : run_phase

function void uvma_cvxif_cov_model_c::sample_req_item(uvma_cvxif_req_item_c req_item);

  request_cg.sample(req_item);

endfunction : sample_req_item

function void uvma_cvxif_cov_model_c::sample_resp_item(uvma_cvxif_resp_item_c resp_item);

   response_cg.sample(resp_item);
   result_cg.sample(resp_item);

endfunction : sample_resp_item

`endif // __UVMA_CVXIF_COV_MODEL_SV__
