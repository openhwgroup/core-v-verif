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
//  Description : driver for clock signal.
//                nominal_clock_period, duty_cycle and starting_signal_level are
//                configurable items, needs to be configured at
//                pre_configure_phase in the test
// 
// ----------------------------------------------------------------------------

class dummy_txn extends uvm_sequence_item;

endclass : dummy_txn

class clock_driver_c extends uvm_driver #( dummy_txn, dummy_txn ) ;

    `uvm_component_utils( clock_driver_c )

    //---------------------------
    // Virtual Interface
    //---------------------------
    virtual xrtl_clock_vif m_v_clock_vif;

    //---------------------------------------------
    // Clock config handle to get 
    // frequency, starting signal level, duty cycle 
    //--------------------------------------------
    clock_config_c    m_clk_cfg; 

    // Give global clock count 
    int global_cycle_count;
    //---------------------------------------------
    // The period ...1/F 
    //--------------------------------------------
    real m_nominal_clock_period;

    function new( string name, uvm_component parent);
        super.new(name,parent);
    endfunction : new

    //---------------------------------------------
    // Build Phase  
    //--------------------------------------------
    function void build_phase( uvm_phase phase );
        super.build_phase( phase);

        if(!uvm_config_db #( virtual xrtl_clock_vif )::get(this, "", get_name(), m_v_clock_vif )) begin
            `uvm_fatal("CLOCK_DRIVER_C", $sformatf("Unable to get clock_if for %s from configuration database", get_name() ) );
        end

    endfunction : build_phase


    //---------------------------------------------
    // Start of simulation phase 
    //--------------------------------------------
    function void start_of_simulation_phase( uvm_phase phase );

    	super.start_of_simulation_phase(phase);
        m_nominal_clock_period               = 1.0/(m_clk_cfg.m_clock_frequency);
        m_v_clock_vif.starting_signal_level = m_clk_cfg.m_starting_signal_level;
        m_v_clock_vif.clk_high	           = (m_nominal_clock_period)*(m_clk_cfg.m_duty_cycle/100.0)*1000000; // ps
        m_v_clock_vif.clk_low		       = (m_nominal_clock_period)*(1.0- (m_clk_cfg.m_duty_cycle/100.0))*1000000; //ps

        // Make sure we don't give a period of zero -> this locks up the simulator!
        if ( ( m_v_clock_vif.clk_high == 0 ) || ( m_v_clock_vif.clk_low == 0 ) ) begin
           `uvm_fatal( "CLOCK_DRIVER_C", $sformatf("Clock periods are zero : %0d %0d",
            m_v_clock_vif.clk_high, m_v_clock_vif.clk_low == 0 )  );
        end // if

        `uvm_info( "CLOCK_DRIVER_C", $sformatf("START clock period = %0f(f) ps, clock duty = %0d(d), low_clock = %0f(f) ps, high_clock = %0f(f) ps", m_nominal_clock_period*1000000, m_clk_cfg.m_duty_cycle, m_v_clock_vif.clk_low*1000000, m_v_clock_vif.clk_high*1000000), UVM_NONE );
    endfunction : start_of_simulation_phase


    virtual task pre_reset_phase( uvm_phase phase );
        fork begin
            start_clock();
        end join
    endtask : pre_reset_phase
    //---------------------------------------------
    // Post shutdown phase  
    //--------------------------------------------
    virtual task post_shutdown_phase( uvm_phase phase );
        phase.raise_objection( this, "Started Post Shutdown");
        `uvm_info( "CLOCK_DRIVER_C", "STARTING POST SHUTDOWN", UVM_NONE );
        #1; // Allow time for any assertions to trigger
        phase.drop_objection( this, "Post Shutdown Completed");
    endtask : post_shutdown_phase

    //---------------------------------------------
    // Extract phase  
    //--------------------------------------------
//    virtual function void extract_phase( uvm_phase phase );
//        `uvm_info( "CLOCK_DRIVER_C", "STOPPING THE CLOCK", UVM_NONE );
//        fork begin
//            stop_clock();
//        end join
//    endfunction : extract_phase

   //================================================================================
   // Global Clock Counter 
   //================================================================================
   task global_cycle_counter();
      forever begin
        m_v_clock_vif.wait_n_clocks(1);
        global_cycle_count++;
      end //forever 
   endtask : global_cycle_counter

   //================================================================================
   // Get Global Clock Counter 
   //================================================================================
   function int get_global_cycle_counter();
     get_global_cycle_counter = global_cycle_count;
   endfunction : get_global_cycle_counter

   //---------------------------------------------
   // Task to start the clock from the uvm class  
   //--------------------------------------------
   virtual task start_clock();
        m_v_clock_vif.start_clock();
   endtask: start_clock

   //---------------------------------------------
   // Task to stop the clock from the uvm class
   //--------------------------------------------
   virtual task stop_clock();
        m_v_clock_vif.stop_clock();
   endtask: stop_clock

endclass : clock_driver_c

