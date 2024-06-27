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
//  Description : This is a behavioural model that is primarily intended
//                to represent the behaviour of multi-cycle paths in RTL
//                simulation. This module acts as a "wire" which can have
//                a delay that is randomized within a fixed range.
//
//                This module can be instantiated in the RTL of a
//                design, and the synthesized version (the code insid
//                of synopys tranlateon directives), will simply produce
//                a wire between the input and output ports. Thus the
//                resulting synthesized design is not modified.
//
//                In simulation, the model will insert a random delay between
//                the input bus or the output bus. This delay can either be
//                referenced to an absolute time values (specified in ps),
//                or it can be referenced to a number of clock cycles.  The
//                choice of this mode is based on a parameter CLOCK_BASED.
//
//                The range of the inserted delay is defined by two parameters
//                MIN_DELAY and MAX_DELAY. When in clock-based mode, these
//                parameters repesent a delay, expressed in units of 1/10th
//                of the clock period. A value of 10 corresponds to a delay
//                of one clock period, 20 corresponds two two clock periods,
//                5 corresponds to half a clock. When in absolute delay mode,
//                these parameters represent a minimum and maximum delay
//                expressed in pico-seconds.
//
//                Even in simulation, by default, no delay will be inserted.
//                To enable this feature the following +options may be used
//
//                +BEH_DELAY   == Must be present to cause the delays to be
//                                  enabled.
//                
//                +BEH_DELAY_DEBUG == If this is true, then messages will
//                                    printed by each instance, indicating
//                                    its mode of operation and the delays
//                                    it has selected (in FIXED_DELAY_MODE).
//
//                In all cases, a banner will be printed at time zero, stating
//                whether the BEH_DELAY is enabled - or not.
//                
// 
// ----------------------------------------------------------------------------

// synthesis translate_off

// Start System Verilog Global Name Space

// simulation global flag indicating

// These flags allow us to print banners only once for all instances
static logic global_beh_delay_start_banner_printed = 0; 

// End System Verilog Global Name Space

// synthesis translate_on

module beh_rand_delay   #( 
     parameter integer  BUS_WIDTH    = 32,
     parameter integer  CLOCK_BASED  = 1,   // 0=absolute delays, 1=clock based
     parameter integer  MIN_DELAY    = 10,  // if absolute delay, minimum delay in ps
                                            // if clock based,    minimum delay in units
                                            //        of 1/10th of the clock period. 10=1 clock period
     parameter integer  MAX_DELAY    = 20,  // if absolute delay, maximum delay in ps
                                            // if clock based,    maximum delay in units
                                            //        of 1/10th of the clock period. 10=1 clock period
     parameter integer  FIXED_DELAY  = 1    // 0=delay is continously randomized throughout the simulation
                                            // 1=delay is randomized at the beginning and never changes during
                                            //        that simulation run
                         )
(
    // Input and output bus
    input  wire logic  [BUS_WIDTH-1:0]   bus_in,
    output wire logic  [BUS_WIDTH-1:0]   bus_out,
    input                                clk   ); // only used when CLOCK_BASED=1. Used to observe clock period

// synthesis translate_off

   timeunit 1ps;

// ----------------------------------------------------------------------------
// Variables for delay modeling
// ----------------------------------------------------------------------------
   logic                 delay_is_enabled;       // Is this instance adding delays?
   logic                 debug_enabled;          // Are debug messages enabled?
   reg  [BUS_WIDTH-1:0]  delayed_bus;            // The delayed output bus

   time                  last_clock_edge_ps;     // Time of last clock edge
   bit                   last_clock_edge_valid;

   time                  clock_period_ps;        // Current clock period
   time                  new_clock_period_ps;    // Current clock period
   bit                   clock_period_valid;
   bit                   clock_period_changed;

   time                  current_delay_ps;          // Delay currently being applied
   time                  last_input_trans_time_ps;  // Note last time an input transition occured
   bit                   current_delay_valid;

// ----------------------------------------------------------------------------
// Manage Enabling and Startup Banner
// ----------------------------------------------------------------------------
   initial begin
      if ( $test$plusargs("BEH_DELAY" ) ) begin
         delay_is_enabled = 1;
         if ( MAX_DELAY < MIN_DELAY ) begin
               $fatal( $sformatf("Invalid values for delay parmeters in %m  : MIN(%0d)>MAX(%0d)",
                      MIN_DELAY, MAX_DELAY ) );
         end // if
      end else begin
         delay_is_enabled = 0;
      end // if

      if ( $test$plusargs("BEH_DELAY_DEBUG" ) ) begin
         debug_enabled = 1;
      end else begin
         debug_enabled = 0;
      end // if

      // Print a banner with info - but only one instance
      if (!global_beh_delay_start_banner_printed) begin
         $display("*****************************************************");
         if ( delay_is_enabled ) begin
            $display("       RANDOM BEH DELAY MODELING IS ENABLED");
         end else begin
           $display("       RANDOM BEH DELAY MODELING IS DISABLED");
        end // if
        if ( debug_enabled && delay_is_enabled ) begin
           $display("                  DEBUG IS ENABLED");
        end // if
        $display("*****************************************************");
        global_beh_delay_start_banner_printed = 1; // only print for one instance
     end // if
  end // initial

// ----------------------------------------------------------------------------
// Extract the clock period information
// ----------------------------------------------------------------------------
   initial begin
      last_clock_edge_valid = 0;
      clock_period_valid = 0;
      clock_period_changed = 0;
   end // if

   always @( posedge clk ) begin : CLK_PERIOD_PROCESS
      if ( clk === 1'b1 ) begin                 // dont' trigger on X/Z
         if ( last_clock_edge_valid ) begin
            new_clock_period_ps = $time - last_clock_edge_ps;
            if ( clock_period_valid && ( new_clock_period_ps != clock_period_ps ) ) begin
               clock_period_changed = 1'b1;
            end // if
            if ( debug_enabled && ( new_clock_period_ps != clock_period_ps ) ) begin
               $display("[%0t][%m] BEH_DELAY_DEBUG : New clock period is %0d (ps)", $time, new_clock_period_ps);
            end // if
            clock_period_ps = new_clock_period_ps;
            clock_period_valid = 1'b1;
         end // if
         last_clock_edge_ps = $time;
         last_clock_edge_valid = 1'b1;
      end // if
   end // always

// ----------------------------------------------------------------------------
// Update the delay
// ----------------------------------------------------------------------------
   initial begin
      current_delay_valid = 1'b0;
   end

   always @( bus_in ) begin : INPUT_BUS_PROCESS
      if ( CLOCK_BASED == 1 ) begin // -------------- CLOCK BASED ------------------
         if ((!current_delay_valid)&&clock_period_valid) begin                 // first time clock is stable
            current_delay_ps = pick_delay( );
            current_delay_valid = 1'b1;
         end // if
         if ( current_delay_valid &&                                           // Update delay, either when
              ( clock_period_changed || ($urandom_range(100,0)>90) ) &&        // clock period changes or periodically
              FIXED_DELAY == 0 ) begin // -clock period changed
            if ( ( $time - last_input_trans_time_ps ) > current_delay_ps ) begin // don't lower delay if edges in flight
                current_delay_ps = pick_delay( );
                current_delay_valid = 1'b1;
            end // if
         end // if
      end else begin           // ------------ ABSOLUTE DELAY BASED -----------
         if (!current_delay_valid) begin
            current_delay_ps = pick_delay( );
            current_delay_valid = 1'b1;
         end else begin
            if (FIXED_DELAY == 0) begin
               if ( ( $time - last_input_trans_time_ps ) > current_delay_ps ) begin
                  current_delay_ps = pick_delay( );
                  current_delay_valid = 1'b1;
               end // if
            end // if
         end // if
      end // if                // ---------------------------------------------
      last_input_trans_time_ps = $time;
   end : INPUT_BUS_PROCESS // always

// ----------------------------------------------------------------------------
// Actually delay the bus
// ----------------------------------------------------------------------------
   always @( bus_in ) begin : TRANSPORT_DELAY
      delayed_bus <= #current_delay_ps bus_in;
   end : TRANSPORT_DELAY

// ----------------------------------------------------------------------------
// Function to compute the random delays
// ----------------------------------------------------------------------------
   function time pick_delay(); 
      begin
         time new_delay;

         if ( CLOCK_BASED == 1 ) begin // -------------- CLOCK BASED ---------------
            if ( !clock_period_valid ) begin
               $error("Internal model error !!"); // this function is only callsed when clock_period_valid
               return 0;
            end  // if
            new_delay = $urandom_range( (clock_period_ps*MAX_DELAY)/10, (clock_period_ps*MIN_DELAY)/10 );
         end else begin        // ------------ ABSOLUTE DELAY BASED ----------- 
             new_delay = $urandom_range( MAX_DELAY, MIN_DELAY );
         end // if

         return new_delay;
      end
   endfunction 

// ----------------------------------------------------------------------------
// Assign the output bus
// ----------------------------------------------------------------------------
// synthesis translate_on
   assign bus_out = 
// synthesis translate_off
            delay_is_enabled ? delayed_bus :
// synthesis translate_on
                                              bus_in;


endmodule : beh_rand_delay

