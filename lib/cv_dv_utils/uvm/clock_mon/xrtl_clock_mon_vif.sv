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
//  Description : XRTL portion of clock monitor.
//
//
// ----------------------------------------------------------------------------

import uvm_pkg::*;

`include "uvm_macros.svh"

interface xrtl_clock_mon_vif ( input bit clk,             // This clock is always running
                               input bit reset_n,
                               input bit clk_to_check  );  // This clock is being checked

    //--------------------------------------------------------------------
    // Declarations
    //--------------------------------------------------------------------

    localparam time tolerance = 10ps ;    // allow 10ps of jitter

    bit clk_mon_enable;
    bit clk_mon_sva_enable = 1;

    // IEEE 1800.2017 LRM - 20.3.1 $time
    // The $time system function returns an integer that is a 64-bit unsigned value, rounded to the nearest unit

    time clk_min_period_ps;
    time clk_max_period_ps;

    time current_period;
    time last_period;

    time time_last_edge;
    time time_last_edge_pos_neg;

    time difference_in_period;          // Variable for comparing clock period

    realtime time_glitch_last_edge;
    realtime glitch_period;

    int num_consecutive_clk_stable;
    int period_error = 0;

    //--------------------------------------------------------------------
    // Always block to measure clock period
    //--------------------------------------------------------------------

    always @( posedge clk_to_check)
      begin : blk_meas_per

        if (clk_mon_enable)
          begin

            current_period = $time - time_last_edge;

            difference_in_period = (last_period - current_period);

            if ( $signed(difference_in_period) < 0 )
              begin
                difference_in_period = -$signed(difference_in_period);
              end

            ///////////////////////////////////////////////////////////////////////////////////
            // It is critical that *every* clock pulse be checked (not just every N).
            ///////////////////////////////////////////////////////////////////////////////////

            if ( difference_in_period < tolerance )
              begin
                num_consecutive_clk_stable++;
                // `uvm_info("CLOCK MONITOR", $sformatf("current_period=%0d (ps) IS equal to last_period =%0d (ps) @ time=%0t ps", current_period, last_period, $time ), UVM_DEBUG )
              end
            else
              begin
                num_consecutive_clk_stable = 1;
                // `uvm_info("CLOCK MONITOR", $sformatf("current_period=%0d (ps) is NOT equal to last_period =%0d (ps) @ time=%0t ps", current_period, last_period, $time ), UVM_DEBUG )
              end

            last_period = current_period;

            ///////////////////////////////////////////////////////////////////////////////////
            // Checking for the period being in or out of range MUST be in the interface
            ///////////////////////////////////////////////////////////////////////////////////

            if ( current_period > clk_max_period_ps )
              begin
                period_error++;
                // `uvm_info("CLOCK MONITOR", $sformatf("period_error=%0d - current_period > clk_max_period_ps", period_error ), UVM_DEBUG )
              end
            else if ( current_period < clk_min_period_ps )
              begin
                period_error++;
                // `uvm_info("CLOCK MONITOR", $sformatf("period_error=%0d - current_period < clk_min_period_ps", period_error ), UVM_DEBUG )
              end
            else
              begin
                period_error = 0;
                // `uvm_info("CLOCK MONITOR", $sformatf("period_error=%0d - current_period = clk_min_period_ps", period_error ), UVM_DEBUG )
              end

            ///////////////////////////////////////////////////////////////////////////////////
            // Report Error only once
            ///////////////////////////////////////////////////////////////////////////////////

            if (period_error == 1)
              `uvm_error("CLOCK MONITOR", $sformatf("Monitored clock period=%0d (ps) is outside the desired range of MIN period: %0d (ps) MAX period: %0d (ps) @ %m", current_period, clk_min_period_ps, clk_max_period_ps ) )


          end
        else
          begin
            num_consecutive_clk_stable = 1;
            current_period = 0;
          end

        time_last_edge = $time;

      end : blk_meas_per

    //--------------------------------------------------------------------
    // Always block to get LAST pos/neg edge
    //--------------------------------------------------------------------

    always @(clk_to_check)
      begin : blk_last_edge
        time_last_edge_pos_neg = $time;
      end   : blk_last_edge

    //--------------------------------------------------------------------
    // Functions
    //--------------------------------------------------------------------

    function time get_time_last_edge_ps();
      return time_last_edge_pos_neg;
    endfunction : get_time_last_edge_ps

    function time get_current_time_ps();
      return $time;
    endfunction : get_current_time_ps

    function void clock_mon_enable();
      clk_mon_enable = 1'b1;
    endfunction : clock_mon_enable

    function void clock_mon_disable();
      clk_mon_enable = 1'b0;
    endfunction : clock_mon_disable

    function void clock_mon_sva_enable();
      clk_mon_sva_enable = 1'b1;
    endfunction: clock_mon_sva_enable

    function void clock_mon_sva_disable();
      clk_mon_sva_enable = 1'b0;
    endfunction: clock_mon_sva_disable

    //-------------------------------------------------------------------------
    // ASSERTIONS
    //-------------------------------------------------------------------------

    // ---------------------------------------------------------------------------
    // Verify the clock is never X
    // ---------------------------------------------------------------------------

`ifndef EMULATION

    property no_x_on_ck_pll_out;
      @( posedge clk )
      disable iff ( ~reset_n  || ~clk_mon_sva_enable)
        ( !$isunknown( clk_to_check ) );
    endproperty

    no_x_on_ck_pll_out_sva : assert property (no_x_on_ck_pll_out) else
      `uvm_error("ERROR CLOCK MON SVA", "ck_pll_out MUST NEVER be X/Z")

`endif

  // ---------------------------------------------------------------------------
  // No Glitch on Output
  // ---------------------------------------------------------------------------

  // This assertion will check that there is never a glitch on the clock.
  // For the purpose of this assertion, a glitch will be defined as any 
  // '0->1->0' or '1->0->1' transition with period less than 300ps 
  // (corresponding to a max frequency of 1.666 GHz).


  always @(clk_to_check)
    begin : blk_glitch

      glitch_period         = $realtime - time_glitch_last_edge;
      time_glitch_last_edge = $realtime;
      if(clk_mon_sva_enable) begin
      	pll_out_no_glitch_assert : assert (( glitch_period > 300ps ) || ($realtime == 0)) else
        	$error("[ERROR CLOCK MON SVA] %m there is glitch of %0t (ps) which is less than 300 pico seconds", glitch_period );  //  Need to have clk0/clk1 ... uvm_error
      end 

    end : blk_glitch

endinterface : xrtl_clock_mon_vif
