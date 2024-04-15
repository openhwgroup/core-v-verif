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
//  Description : This holds a UVM agent for generating back-pressure.
//                
// 
// ----------------------------------------------------------------------------


class bp_agent extends uvm_agent;

 `uvm_component_utils( bp_agent )

    // -------------------------------------------------------------------------
    // 2 Structural Components
    //
    // This agent does not yet have a monitor. If there is a need to
    //  to monitor the back-pressure, then we'll add a monitor
    // -------------------------------------------------------------------------
    bp_sequencer    m_sequencer;
    bp_driver       m_driver;

    // -------------------------------------------------------------------------
    // Constructor
    // -------------------------------------------------------------------------
    function new( string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    // -------------------------------------------------------------------------
    // Build Phase
    // -------------------------------------------------------------------------
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if (is_active == UVM_ACTIVE ) begin
            `uvm_info( "BUILD", "Is Active", UVM_HIGH );
            m_sequencer = bp_sequencer::type_id::create( "bp_sequencer"   ,this);
            m_driver = bp_driver::type_id::create( "driver", this);
        end else begin
            `uvm_info( "BUILD", "Is Passive", UVM_HIGH );
        end // if
    endfunction: build_phase

    // -------------------------------------------------------------------------
    // Connect Phase
    //
    // Connect driver to sequencer
    // -------------------------------------------------------------------------
    function void connect_phase(uvm_phase phase);
        if ( is_active == UVM_ACTIVE ) begin
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
            `uvm_info( "CONNECT", "Connect stage complete both directions.", UVM_MEDIUM );
        end // if
    endfunction: connect_phase

    // -------------------------------------------------------------------------
    // Pre-Reset Phase
    //
    // Stop the sequencer
    // -------------------------------------------------------------------------
    task pre_reset_phase( uvm_phase phase );
        m_sequencer.stop_sequences( );
    endtask : pre_reset_phase

    // -------------------------------------------------------------------------
    // Pre-Shutdown Phase
    //
    // Stop the sequencer
    // -------------------------------------------------------------------------
    task pre_shutdown_phase( uvm_phase phase );
        m_sequencer.stop_sequences( );
    endtask : pre_shutdown_phase

    // -------------------------------------------------------------------------
    // Post-Shutdown Phase
    //
    // Stop the sequencer
    // -------------------------------------------------------------------------
    task post_shutdown_phase( uvm_phase phase );
        m_sequencer.stop_sequences( );
    endtask : post_shutdown_phase

endclass: bp_agent

