// ----------------------------------------------------------------------------
//Copyright 2023 CEA*
//*Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
//
//Licensed under the Apache License, Version 2.0 (the "License");
//you may not use this file except in compliance with the License.
//You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
//Unless required by applicable law or agreed to in writing, software
//distributed under the License is distributed on an "AS IS" BASIS,
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//See the License for the specific language governing permissions and
//limitations under the License.
//[END OF HEADER]
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//  Description : Agent for the generic request. 
//                It is parametrized by the type of request and response.
//                And it drives and monitor the request of type req_t(to be
//                defined by user) and responses of type rsp_t (to be defined by user) 
// ----------------------------------------------------------------------------

class generic_agent #(type req_t, type rsp_t) extends uvm_agent;

  // -------------------------------------------------------------------------
  // UVM Utils
  // -------------------------------------------------------------------------
  `uvm_component_param_utils(generic_agent #(req_t, rsp_t))

  // -------------------------------------------------------------------------
  // Fields for the vrp agents
  // -------------------------------------------------------------------------
  protected uvm_active_passive_enum is_active = UVM_ACTIVE;

  generic_sequencer  #(req_t, rsp_t)m_sequencer;
  generic_driver     #(req_t, rsp_t)m_driver;

  virtual generic_if #(req_t, rsp_t)generic_vif; 
  generic_monitor    #(req_t, rsp_t)m_monitor;
  
  // -------------------------------------------------------------------------
  // Constructor
  // -------------------------------------------------------------------------
  function new(string name, uvm_component parent);
      super.new(name, parent);
  endfunction
  
  // ----------------------------------------------------------------------
  // Build Phase
  // ----------------------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    m_monitor = generic_monitor#(req_t, rsp_t)::type_id::create("monitor", this);
    if(is_active == UVM_ACTIVE) begin
      m_sequencer = generic_sequencer#(req_t, rsp_t)::type_id::create("sequencer", this);
      m_driver    = generic_driver#(req_t, rsp_t)::type_id::create("driver", this);
    end

    if (!uvm_config_db #( virtual generic_if#(req_t, rsp_t))::get(this, "", get_name(), generic_vif )) begin
        `uvm_fatal("BUILD_PHASE", $sformatf("Unable to get generic_vif_config for %s from configuration database", get_name() ) );
    end // if

    `uvm_info(get_full_name( ), "Build stage complete.", UVM_LOW)
  endfunction: build_phase
  
  // ----------------------------------------------------------------------
  // connect phase
  // ----------------------------------------------------------------------
  function void connect_phase(uvm_phase phase);
      if(is_active == UVM_ACTIVE) begin
        m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        m_driver.set_generic_vif(generic_vif);
      end
      m_monitor.set_generic_vif(generic_vif);
      `uvm_info(get_full_name( ), "Connect stage complete.", UVM_LOW)
  endfunction: connect_phase

  // ----------------------------------------------------------------------
  // Set agent to active mode
  // ----------------------------------------------------------------------
  function void set_is_active();
    is_active = UVM_ACTIVE;
  endfunction: set_is_active
 
  virtual task reset_phase( uvm_phase phase );
      if ( is_active == UVM_ACTIVE ) begin
        m_sequencer.stop_sequences();
        `uvm_info( "STOPPED SEQUENCES", "STOPPED SEQUENCES", UVM_LOW );
      end // if
  endtask: reset_phase

endclass: generic_agent
