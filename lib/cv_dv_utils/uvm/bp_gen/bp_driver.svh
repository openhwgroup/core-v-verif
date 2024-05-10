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
//  Description : Parameterized driver for a backpressure signal.
// 
// ----------------------------------------------------------------------------


class bp_driver extends uvm_driver #( bp_txn, bp_txn ) ;

    `uvm_component_utils( bp_driver  )

    // Virtual Interface
    virtual bp_vif  #( .is_active( 1 ) ) m_v_bp_vif;

    // Events to handle reset
    event m_start_driver;
    event m_reset_driver;

    // ----------------------------------------------------------------------
    // Field member seed
    // ----------------------------------------------------------------------
    rand integer unsigned seed;

    // ----------------------------------------------------------------------
    // Constructor
    // ----------------------------------------------------------------------
    function new( string name, uvm_component parent);
        super.new(name,parent);
    endfunction : new

    // ----------------------------------------------------------------------
    // Build Phase
    // ----------------------------------------------------------------------
    function void build_phase( uvm_phase phase );
        super.build_phase( phase);

        if(!uvm_config_db #( virtual bp_vif #( .is_active( 1 ) )  )::get(this, "", get_parent().get_name(), m_v_bp_vif )) begin
            `uvm_fatal("BUILD_PHASE", $sformatf("Unable to get bp_vif for %s from configuration database", get_parent().get_name() ) );
        end

    endfunction : build_phase

    // ----------------------------------------------------------------------
    // connect phase
    // ----------------------------------------------------------------------
    function void connect_phase( uvm_phase phase );
        super.connect_phase( phase );

        `uvm_info( "CONNECT PHASE", $sformatf("BP driver %s now connected", get_parent().get_name() ) , UVM_MEDIUM );

     endfunction : connect_phase

    // ----------------------------------------------------------------------
    // Start of Simulation Phase
    // ----------------------------------------------------------------------
    function void start_of_simulation_phase( uvm_phase phase );

       super.start_of_simulation_phase( phase );

       if ( !randomize( seed ) ) begin
          `uvm_fatal("Randomize", "Failure in bp_driver");
       end // if

       m_v_bp_vif.set_seed( seed );
       `uvm_info( "START OF SIMULATION",
                  $sformatf( "Setting BP seed to %0x for %0s",
                              seed, get_name() ), UVM_HIGH );
    endfunction : start_of_simulation_phase

    // In the pre-reset phase - reset the driver, if already running
    // ----------------------------------------------------------------------
    virtual task pre_reset_phase( uvm_phase phase );
       ->m_reset_driver;
    endtask : pre_reset_phase;

    // ----------------------------------------------------------------------
    // Only actually start the driver after reset
    // ----------------------------------------------------------------------
    virtual task post_reset_phase( uvm_phase phase );
       ->m_start_driver;
    endtask : post_reset_phase

    // ----------------------------------------------------------------------
    // run phase
    // ----------------------------------------------------------------------
    task run_phase( uvm_phase phase );

        forever begin
            @( m_start_driver );

            fork
               get_and_drive( );
            join_none;

            @( m_reset_driver );
            `uvm_info( "BP IF DRV KILLING THREADS", "KILLING THREADS", UVM_MEDIUM );
            disable fork;
        end // forever

    endtask : run_phase

    virtual task get_and_drive( );
       driver_burst_bp_txn_t  curr_txns;
       bp_txn req_item;

       forever begin

          while ( !m_v_bp_vif.fifo_full() ) begin
             for( int i=0 ; i<bp_txns_per_xfer ; i++ ) begin
                seq_item_port.get_next_item(req_item);
                curr_txns.txns[i].valid   = 1'b1;
                curr_txns.txns[i].bp_type = req_item.m_bp_type;
                curr_txns.txns[i].N       = req_item.m_N;
                curr_txns.txns[i].M       = req_item.m_M;
                `uvm_info( "BP RUN", $sformatf("Generating i=%0d V=%0b TYPE=%0b N=%0d M=%0d",
                                     i,
                                     curr_txns.txns[i].valid,
                                     curr_txns.txns[i].bp_type,
                                     curr_txns.txns[i].N,
                                     curr_txns.txns[i].M ), UVM_DEBUG );
                seq_item_port.item_done( );
             end // for

             m_v_bp_vif.send( curr_txns );
          end // while
          `uvm_info( "BP RUN", "WAITING TO BE DONE", UVM_DEBUG );
          @( m_v_bp_vif.done_sending );
       end // forever
    endtask : get_and_drive

endclass : bp_driver

