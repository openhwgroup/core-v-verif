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
//  Description :  Provides a global watchdog timer that terminates the
//                 simulation after a maximum delay. The maximum delay
//                 can be set by a plusarg (+TIMEOUT=xxx) specified in ns.
//
//                 On timeout, a list of the objectors is provided.
//
//                 Provides a watchdog timer for a UVM environment.
//                 This code was taken from the book Advanced UVM by
//                 Brian Hunter.
//                
// 
// ----------------------------------------------------------------------------

class watchdog_c extends uvm_component;

    int unsigned m_watchdog_time            = 10000;
    int unsigned m_debug_objectors_interval = 0;      // interval to report objectors
    bit          m_enable_wd                = 1;

    // ----------------------------------------------------------------------
    // Configuration Fields
    // ----------------------------------------------------------------------
    `uvm_component_utils_begin( watchdog_c )
        `uvm_field_int( m_watchdog_time, UVM_DEC ) 
    `uvm_component_utils_end

    bit m_timeout_occurred = 0;

    // ----------------------------------------------------------------------
    // Constructor
    function new( string name="watchdog", uvm_component parent=null);
        super.new( name,parent );
    endfunction : new

    // ----------------------------------------------------------------------
    // Build phase
    // ----------------------------------------------------------------------
    virtual function void build_phase( uvm_phase phase );

        int unsigned plus_arg_wdog_time;
        int unsigned plus_arg_debug_time;

        super.start_of_simulation_phase( phase );
        if ( $value$plusargs("TIMEOUT=%d", plus_arg_wdog_time ) ) begin
            m_watchdog_time = plus_arg_wdog_time;
        end // if
        if ( $value$plusargs("OBJECTORS=%d", plus_arg_debug_time ) ) begin
            m_debug_objectors_interval = plus_arg_debug_time;
        end // if
    endfunction : build_phase
            
    // ----------------------------------------------------------------------
    // Start of Simulation
    //
    // If a specific test wants to modify the watchdog value from the 
    //   command line this can be done during the start of simulation phase.
    // Or the user can disable the watchdog>
    // ----------------------------------------------------------------------

    // ----------------------------------------------------------------------
    // Run phase
    // ----------------------------------------------------------------------
    virtual task run_phase( uvm_phase phase );
        uvm_phase current_phase;

        if ( m_enable_wd ) begin
           `uvm_info( "WD START", 
                      $sformatf( "Global Watchog Timer set to %0d ns", m_watchdog_time ), UVM_NONE );
           if ( m_debug_objectors_interval > 0 ) begin
              `uvm_info( "WD DEBUG", 
                         $sformatf( "Object debug Timer set to %0d ns", m_debug_objectors_interval ), UVM_HIGH );
           end // if
           if ( m_watchdog_time == 0 ) return;
   
           // fork a thread for debug, if requested
           if ( m_debug_objectors_interval > 0 ) begin
               fork 
                   forever begin
                       #(m_debug_objectors_interval * 1ns);
                       objector_report();
                   end
               join_none;
           end // if
   
           #(m_watchdog_time * 1ns);    // wait for the delay
   
           `uvm_error( "WATCHDOG", $sformatf( "Simulation timed out after %0d ns", m_watchdog_time ) );
   
           objector_report();
           m_timeout_occurred = 1;
           current_phase = m_current_phase;
           if ( current_phase == null ) begin
               `uvm_fatal( "TIMEOUT OCCURED", "Could not identify which phase is responsible" );
           end else begin
               uvm_domain::jump_all( uvm_check_phase::get() );
           end // if
        end // if
    endtask : run_phase


    // ----------------------------------------------------------------------
    // final_phase
    // ----------------------------------------------------------------------
    virtual function void final_phase( uvm_phase phase );
        if ( m_timeout_occurred ) begin
            `uvm_fatal( "FINAL PHASE", "Exiting due to timeout" );
        end // if
    endfunction : final_phase

    // ----------------------------------------------------------------------
    // objector_report
    // List the class / object which have an objection raised
    // ----------------------------------------------------------------------
    virtual function void objector_report();
        string str;
        uvm_object objectors[$];
        uvm_phase current_phase = m_current_phase;

        if ( current_phase == null )
            `uvm_fatal( "WATCHDOG OBJECT", "Unable to determine current phase" );

        current_phase.get_objection().get_objectors( objectors ) ;

        str = $sformatf("\n\nCurrently executing phase : %s\n", current_phase.get_name() );
        str = { str, "List of Objectors\n" };
        str = { str, "Hierarchical Name                          Class Type\n" };
        foreach( objectors[obj] ) begin
            str = { str, $sformatf("%-47s%s\n", objectors[obj].get_full_name(),
                                               objectors[obj].get_type_name() ) };
        end // for

        `uvm_info( "WD REPORT", str, UVM_HIGH );
    endfunction : objector_report

    // ----------------------------------------------------------------------
    // function override_wd_value
    //
    // This function should be called in the start of simulation phase 
    // ----------------------------------------------------------------------
    function void override_wd_value( int new_wd_value );
       m_watchdog_time = new_wd_value;
        `uvm_info( "WATCHDOG",  $sformatf("WD value now set to %0d", new_wd_value), UVM_LOW );
    endfunction : override_wd_value

    // ----------------------------------------------------------------------
    // function disable
    //
    // This function should be called in the start of simulation phase 
    // ----------------------------------------------------------------------
    function void disable_wd( );
        m_enable_wd = 0;
        `uvm_info( "WATCHDOG",  "DISABLED", UVM_MEDIUM );
    endfunction : disable_wd

endclass : watchdog_c



