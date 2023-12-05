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
// ----------------------------------------------------------------------------
//  Description : Monitor for clock signal(s)
//
//
//
// ----------------------------------------------------------------------------

class clock_monitor_c extends uvm_monitor;

    `uvm_component_utils( clock_monitor_c )

    // ------------------------------------------------------------------------
    // Virtual interfaces - obtained from config_db
    // ------------------------------------------------------------------------

    virtual xrtl_clock_mon_vif m_v_clock_mon_vif;

    // ------------------------------------------------------------------------
    // Variable declaration
    // ------------------------------------------------------------------------

    bit m_clk_mon_en;


    // ------------------------------------------------------------------------
    // Local Parameter
    // ------------------------------------------------------------------------

    localparam int NUMBER_OF_CLK_STABLE = 50;

    // ------------------------------------------------------------------------
    // Constructor
    // ------------------------------------------------------------------------

    function new( string name, uvm_component parent );
      super.new(name, parent);
    endfunction: new

    // ------------------------------------------------------------------------
    // Build phase
    //
    // Get the virtual interface from the configuration DB.
    // ------------------------------------------------------------------------

    function void build_phase( uvm_phase phase );

      super.build_phase( phase );

        // Obtain the Virtual interface from the configuration DB
        if ( !uvm_config_db #( virtual xrtl_clock_mon_vif)::get(this, "",  get_name(), m_v_clock_mon_vif ))
          `uvm_error("BUILD_PHASE", {"UNABLE to get Virtual Interface for [get_full_name]= ", get_full_name(), " from the configuration database" } )

    endfunction: build_phase


    // ------------------------------------------------------------------------
    // Function: enable_auto_clk_monitor
    // ------------------------------------------------------------------------
    function void enable_auto_clk_monitor(int min_freq_Hz, int max_freq_Hz);

      // Period in picosecond + 0.5 Round not truncate
      m_v_clock_mon_vif.clk_min_period_ps = ((1.0/max_freq_Hz) * 1e12) + 0.5;
      m_v_clock_mon_vif.clk_max_period_ps = ((1.0/min_freq_Hz) * 1e12) + 0.5;

      if (min_freq_Hz > max_freq_Hz)
        `uvm_warning( "CLOCK MONITOR", "WARNING: MIN frequency > MAX frequency" );

      m_v_clock_mon_vif.clock_mon_enable();

      `uvm_info( "CLOCK MONITOR", $sformatf("Enabling clock monitor: %s with MIN frequency = %0d (Hz) and MAX frequency = %0d (Hz) - MIN period=%0d (ps) and MAX period=%0d (ps)", get_name(),
         min_freq_Hz, max_freq_Hz, m_v_clock_mon_vif.clk_min_period_ps, m_v_clock_mon_vif.clk_max_period_ps ), UVM_MEDIUM )

    endfunction : enable_auto_clk_monitor


    // ------------------------------------------------------------------------
    // Function: disable_clk_monitor
    // ------------------------------------------------------------------------
    function void disable_clk_monitor();

       m_v_clock_mon_vif.clock_mon_disable();
      `uvm_info( "CLOCK MONITOR", $sformatf("Disabling clock monitor: %s", get_name() ), UVM_MEDIUM )

    endfunction : disable_clk_monitor

    // ------------------------------------------------------------------------
    // Function: clk_is_stable
    // ------------------------------------------------------------------------

    function int clk_is_stable();

      if ( m_v_clock_mon_vif.num_consecutive_clk_stable >= NUMBER_OF_CLK_STABLE )
        begin
          `uvm_info( "CLOCK MONITOR", $sformatf("Clock is Stable"), UVM_MEDIUM )
          return 1;
        end
      else
        return 0;

    endfunction : clk_is_stable


    // ------------------------------------------------------------------------
    // Function: is_clk_flat
    // ------------------------------------------------------------------------

    function logic is_clk_flat( longint flat_duration_in_ps );
       longint time_last_edge;
       longint curr_time;
       longint time_limit;

       curr_time = m_v_clock_mon_vif.get_current_time_ps() ;
       time_last_edge  = m_v_clock_mon_vif.get_time_last_edge_ps() ;
       time_limit = time_last_edge + flat_duration_in_ps;

       `uvm_info( "CLOCK MONITOR", $sformatf("is_clk_flat : %0d %0d %0d %0d",
                          curr_time, time_last_edge, time_limit,
                          ( time_limit < curr_time  ) ), UVM_DEBUG );

       return ( time_limit <  curr_time ) ;
    endfunction : is_clk_flat

    // ------------------------------------------------------------------------
    // Function: get_clk_freq_Hz
    // ------------------------------------------------------------------------
    function longint get_clk_freq_Hz();

      real m_mon_clk_Hz;

      if (m_v_clock_mon_vif.current_period == 0)
        `uvm_fatal("CLOCK MONITOR", "Clock period = 0 ... Did you wait long enough to get a proper measurement?" )

      m_mon_clk_Hz = (1.0/(m_v_clock_mon_vif.current_period * 1e-12));
      `uvm_info("CLOCK MONITOR", $sformatf("[get_clk_freq_Hz] period=%0d (ns) - frequency=%5.0f (Hz) @ time=%0t", m_v_clock_mon_vif.current_period, m_mon_clk_Hz, $time ), UVM_DEBUG )
      return m_mon_clk_Hz;

    endfunction : get_clk_freq_Hz



endclass : clock_monitor_c


