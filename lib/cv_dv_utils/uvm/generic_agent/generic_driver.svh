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
//  Description : Test base class that creates the generic Driver
// ----------------------------------------------------------------------------

class generic_driver #(type req_t, type rsp_t) extends uvm_driver #(generic_txn #(req_t, rsp_t));

    `uvm_component_param_utils( generic_driver#(req_t, rsp_t))

    // ------------------------------------------------------------------------
    // Local variable
    // ------------------------------------------------------------------------
    protected string name ;
//    generic_txn rsp_list[integer][$]; 

    // ------------------------------------------------------------------------
    // Modules
    // -----------------------------------------------------------------------
    virtual generic_if#(req_t, rsp_t) generic_vif;
    
    event                             reset_asserted;
    event                             reset_deasserted;
    // ----------------------------------------------------------------------- 
    // Constructor
    // ----------------------------------------------------------------------- 
    function new( string name , uvm_component parent = null ); 
      super.new( name , parent);
      this.name = name;
    endfunction

    // ----------------------------------------------------------------------- 
    // Build phase
    // ----------------------------------------------------------------------- 
    virtual function void build_phase (uvm_phase phase);

        super.build_phase(phase);

    endfunction

    // ------------------------------------------------------------------------
    // Reset phase 
    // ------------------------------------------------------------------------ 
    virtual task reset_phase(uvm_phase phase);
       super.reset_phase(phase);

       generic_vif.req_valid       <= 0; 

       ->reset_asserted;
       `uvm_info(this.name, "Reset stage complete.", UVM_LOW)
    endtask

    virtual task post_reset_phase(uvm_phase phase);
       super.post_reset_phase(phase);


       ->reset_deasserted;
       `uvm_info(this.name, "post_reset stage complete.", UVM_LOW)
    endtask

    // ----------------------------------------------------------------------- 
    // run phase
    // ----------------------------------------------------------------------- 
    virtual task run_phase ( uvm_phase phase );

        super.run_phase(phase);
 
        forever begin
          @(reset_deasserted);
           // ----------------------------------------------------------------------------
           // get_and_drive_req : new sequence item is created and new transaction 
           // ----------------------------------------------------------------------------
           fork 
             get_and_drive_req(); 
             spy_and_drive_rsp(); 
           join_none
          // In case of a reset on the fly, kill all processes
          @(reset_asserted);
          disable fork;
        end

    endtask

    // ----------------------------------
    // get and drive 
    // ----------------------------------
    virtual task get_and_drive_req( );
       // Drive generic iterface
       forever begin
           seq_item_port.get_next_item(req);
           `uvm_info("REQ ACK DRIVER", "New Request Recieved", UVM_HIGH);

//           @ (posedge generic_vif.clk_i);

           if(req.m_txn_idle_cycles > 0)
             generic_vif.wait_n_clocks(req.m_txn_idle_cycles);

           generic_vif.req_valid   <=  1'b1;
           generic_vif.req         <=  req.m_req;

           // Wait for the request to be consumed
           do begin
             @(posedge generic_vif.clk_i);
           end while (!generic_vif.req_ready); 
 
           generic_vif.req_valid       <=  1'b0;

           // ------------------------------------------------------
           // This is to be used by respose handler
           // ------------------------------------------------------
          // if(req.m_req_need_rsp) begin 
          //   rsp_list[req.m_req_tid].push_back(req);
          // end
           seq_item_port.item_done();
       end
    endtask

    // ----------------------------------
    // get and drive 
    // ----------------------------------
    virtual task spy_and_drive_rsp( );
       generic_txn #(req_t, rsp_t)rsp;
       // Drive generic iterface
       forever begin
           @ (posedge generic_vif.clk_i);
           
           if(generic_vif.rsp_valid & generic_vif.rsp_ready) begin
             rsp       = generic_txn#(req_t, rsp_t)::type_id::create("new rsp");
             rsp.m_rsp <= generic_vif.rsp;

             seq_item_port.put(rsp);
             `uvm_info("RES ACK DRIVER", "New Response Sent", UVM_HIGH);
           end
       end
    endtask
    // ------------------------------------------------------
    // API to set the interface 
    // ------------------------------------------------------
    function void set_generic_vif (virtual generic_if#(req_t, rsp_t) I);
        generic_vif = I;
    endfunction
endclass
