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
//  Description : This is a behavioural model that can be used to filter
//                Xs or Zs out of a bus. Great care should be used when using
//                this model, as it can easily mask real bugs. 
//
//                Two instantiation parameters (filter_x, filter_z) can be
//                used to control whether only x, only z or both values
//                are filter. 
//
//                By default, x's or z's are replaced with random values.
//                However, this can be modified by
//                the instantiation parameter (filer_to) to select
//                a zero or one as the new value.
//
//                The x-masking filter can be globally disabled using
//                a +option at start of simulation.
//
//                +NO_X_FILTER   == Disable all X or Z filtering.
//
//                +X_FILTER_DEBUG == If this is true, then messages will
//                                    printed each time an x or value is
//                                    replaced.
//
//                In all cases, a banner will be printed at time zero, stating
//                whether the BEH_DELAY is enabled - or not.
// 
// ----------------------------------------------------------------------------

// synthesis translate_off

// Start System Verilog Global Name Space

// simulation global flag indicating

// This flag allow us to print banners only once for all instances
static logic global_beh_delay_start_banner_printed = 0; 

// End System Verilog Global Name Space

// synthesis translate_on

module x_filter   #( 
     parameter integer  BUS_WIDTH    = 32,
                        FILTER_X     = 1,   // if 1, x values are filtered
                        FILTER_Z     = 1,   // if 1, z values are filtered
                        FILTER_TO    = 2    // new value : 0=zero, 1=one, 2=random

                         )
(
    // Input and output bus
    input  wire logic  [BUS_WIDTH-1:0]   bus_in,
    output wire logic  [BUS_WIDTH-1:0]   bus_out );

// synthesis translate_off

   timeunit 1ps;

// ----------------------------------------------------------------------------
// Variables for delay modeling
// ----------------------------------------------------------------------------
   logic                 filter_is_enabled;      // Is this instance adding delays?
   logic                 debug_enabled;          // Are debug messages enabled?
   reg  [BUS_WIDTH-1:0]  filtered_bus;           // Bus after filtering
   event                 initial_update;         // event to force update at time 0

// ----------------------------------------------------------------------------
// Manage Enabling and Startup Banner
// ----------------------------------------------------------------------------
   initial begin
      if ( $test$plusargs("NO_X_FILTER" ) ) begin
         filter_is_enabled = 0;
      end else begin
         filter_is_enabled = 1;
      end // if

      if ( $test$plusargs("X_FILTER_DEBUG" ) ) begin
         debug_enabled = 1;
      end else begin
         debug_enabled = 0;
      end // if

      // Print a banner with info - but only one instance
      if (!global_beh_delay_start_banner_printed) begin
         $display("*****************************************************");
         if ( filter_is_enabled ) begin
            $display("       X_FILTERING IS ENABLED");
         end else begin
           $display("        X_FILTERING IS DISABLED");
        end // if
        if ( debug_enabled && filter_is_enabled ) begin
           $display("             DEBUG IS ENABLED");
        end // if
        $display("*****************************************************");
        global_beh_delay_start_banner_printed = 1; // only print for one instance
     end // if

     // We want to evaluate the main-process at time zero, in case the bus
     // in question is always X and never changes
     #0;
     ->initial_update;
  end // initial

  // --------------------------------------------------------------------------
  // Main process to filter the bus. This process wakes up every time
  // bus_in has an event. If filtering is enabled, we walk through the
  // bits in the bus looking for X or Z and then filtering them to 0, 1
  // or random values.
  // --------------------------------------------------------------------------
  always @( bus_in or initial_update ) begin : INPUT_BUS_PROCESS
     integer i;                       // loop counter
     automatic string bit_list = "";  // string for debug message
     bit changed_flag;                // flag to print message only if filtered

     if ( filter_is_enabled ) begin

        changed_flag = 0;
        for( i=0 ; i < BUS_WIDTH ; i++ ) begin
           filtered_bus[i] = bus_in[i];
           if ( ( ( bus_in[i] === 1'bx ) && ( FILTER_X ) ) || 
                ( ( bus_in[i] === 1'bz ) && ( FILTER_Z ) ) ) begin

              changed_flag = 1;
              filtered_bus[i] = ( FILTER_TO == 0 ) ? 1'b0 :
                                ( FILTER_TO == 1 ) ? 1'b1 : $random ;
              if (debug_enabled) begin
                 bit_list = $sformatf("%s bit(%0d) %0b->%0b", bit_list, i, bus_in[i], filtered_bus[i] );
              end // if
           end // if
        end // for i
        if ( debug_enabled && changed_flag ) begin
           $display("[X_FILTER][%m][%0t] Filtered following bits : ", $time, bit_list );
        end // if
     end // if filter_is_enabled
  end : INPUT_BUS_PROCESS // always

// ----------------------------------------------------------------------------
// Assign the output bus
//
// In synthesis, we simply assign bus_out = bus_in.
// ----------------------------------------------------------------------------
// synthesis translate_on
   assign bus_out = 
// synthesis translate_off
            filter_is_enabled ? filtered_bus :
// synthesis translate_on
                                 bus_in;


endmodule : x_filter

