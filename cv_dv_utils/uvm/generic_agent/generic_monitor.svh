// ----------------------------------------------------------------------------
// Copyright 2023 CEA*
// *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//[END OF HEADER]
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//  Description : Monitor for generic request
// ----------------------------------------------------------------------------

class generic_monitor #(type req_t, type rsp_t)extends uvm_monitor;

  `uvm_component_param_utils(generic_monitor#(req_t, rsp_t))

  // -------------------------------------------------------------------------
  // Fields for the vrp monitor
  // -------------------------------------------------------------------------
  protected uvm_active_passive_enum is_active = UVM_PASSIVE;

  virtual generic_if#(req_t, rsp_t)   vif;

  int                                 num_req_pkts;
  int                                 num_resp_pkts;
  
  // -------------------------------------------------------------------------
  // Internal members for monitoring requests
  // -------------------------------------------------------------------------
  uvm_analysis_port #(req_t) ap_req;

  // -------------------------------------------------------------------------
  // Internal members for monitoring responses
  // -------------------------------------------------------------------------
  uvm_analysis_port #(rsp_t) ap_rsp;

  // -------------------------------------------------------------------------
  // Events to handle reset
  // -------------------------------------------------------------------------
  event                             reset_asserted;
  event                             reset_deasserted;
  // -------------------------------------------------------------------------
  // Constructor
  // -------------------------------------------------------------------------
  function new(string name, uvm_component parent);
      super.new(name, parent);


  endfunction: new

  // -------------------------------------------------------------------------
  // Build phase
  // -------------------------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    ap_req    = new("ap_req", this);
    ap_rsp    = new("ap_rsp", this);

    num_req_pkts            = 0;
    num_resp_pkts           = 0;

    `uvm_info(get_full_name( ), "Build stage complete.", UVM_HIGH)
  endfunction: build_phase

  // -------------------------------------------------------------------------
  // Pre-reset phase
  // -------------------------------------------------------------------------
  virtual task pre_reset_phase(uvm_phase phase);
    super.pre_reset_phase(phase);
    -> reset_asserted;
  endtask: pre_reset_phase

  virtual task reset_phase(uvm_phase phase);
    super.reset_phase(phase);
    num_req_pkts            = 0;
    num_resp_pkts           = 0;
  endtask: reset_phase
  // -------------------------------------------------------------------------
  // Post-reset phase
  // -------------------------------------------------------------------------
  virtual task post_reset_phase(uvm_phase phase);
    super.post_reset_phase(phase);
    -> reset_deasserted;
  endtask: post_reset_phase

  // -------------------------------------------------------------------------
  // Run phase
  // -------------------------------------------------------------------------
  virtual task run_phase(uvm_phase phase);
    `uvm_info("generic MONITOR", "Entering run Phase", UVM_HIGH);
    super.run_phase(phase);

    forever begin
      @(reset_deasserted);
      fork
        collect_reqs( phase );
        collect_resps( phase );
      join_none
      // In case of a reset on the fly, kill all processes
      @(reset_asserted);
      disable fork;
    end
    `uvm_info("generic MONITOR", "Leaving run Phase", UVM_HIGH);
  endtask: run_phase

  // -------------------------------------------------------------------------
  // Collect requests 
  // -------------------------------------------------------------------------
  virtual task collect_reqs(uvm_phase phase);
    req_t    req;

    forever begin
      @(posedge vif.clk_i);
      
      if (vif.req_valid && vif.req_ready) begin
        req = vif.req; 
        ap_req.write(req);
        num_req_pkts++;
      end
    end
  endtask: collect_reqs
 
  // -------------------------------------------------------------------------
  // Collect responses
  // -------------------------------------------------------------------------
  task collect_resps(uvm_phase phase);
    rsp_t    rsp;

    forever begin
      @(posedge vif.clk_i);
      if (vif.rsp_valid & vif.rsp_ready) begin
        rsp = vif.rsp;
        ap_rsp.write(rsp);
      end      
    end
  endtask

  // ----------------------------------------------------------------------
  // Set agent to active mode
  // ----------------------------------------------------------------------
  function void set_is_active();
    is_active = UVM_ACTIVE;
  endfunction: set_is_active

  // -------------------------------------------------------------------------
  // Report phase
  // -------------------------------------------------------------------------
  virtual function void report_phase(uvm_phase phase);
      `uvm_info(get_type_name( ), $sformatf("REPORT: COLLECTED REQUEST TRANSACTIONS = %0d, COLLECTED RESPONSE TRANSACTIONS = %d",
                                            num_req_pkts, num_resp_pkts), UVM_HIGH)
  endfunction: report_phase

    // API to set the interface 
    function void set_generic_vif (virtual generic_if#(req_t, rsp_t) I);
        vif = I;
    endfunction

endclass: generic_monitor
