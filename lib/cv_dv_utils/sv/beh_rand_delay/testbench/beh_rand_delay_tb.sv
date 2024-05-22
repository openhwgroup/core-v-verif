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
//  Description : Stand-alone test-bench for random beh delay
// 
// ----------------------------------------------------------------------------

module beh_rand_delay_unit_tb;

   timeunit 1ps;

// ----------------------------------------------------------------------------
// Declare 2 clocks
// ----------------------------------------------------------------------------
   reg                    clk1;
   reg                    clk2;

// ----------------------------------------------------------------------------
// Declare 3 Buses
// ----------------------------------------------------------------------------
   reg  [31:0]            bus_in1;
   wire [31:0]            bus_out1;
   reg                    bus_in2;
   wire                   bus_out2;
   reg  [5:0]             bus_in3;
   wire [5:0]             bus_out3;

// ----------------------------------------------------------------------------
// Count the Edges on input and output buses
// ----------------------------------------------------------------------------
   integer                bus1_in_count, bus1_out_count;
   integer                bus2_in_count, bus2_out_count;
   integer                bus3_in_count, bus3_out_count;

// ----------------------------------------------------------------------------
// Flag to stop stimulus
// ----------------------------------------------------------------------------
   reg                    test_running = 1'b1;

// ----------------------------------------------------------------------------
// Instantiate 3 instances of the DUT
// ----------------------------------------------------------------------------
   beh_rand_delay #( .BUS_WIDTH(32),
                     .CLOCK_BASED(1),
                     .MIN_DELAY(10),
                     .MAX_DELAY(20),
                     .FIXED_DELAY(1) ) DUT1 ( .bus_in ( bus_in1 ), .bus_out( bus_out1 ), .clk( clk1 ) );

   beh_rand_delay #( .BUS_WIDTH(1),
                     .CLOCK_BASED(1),
                     .MIN_DELAY(0),
                     .MAX_DELAY(20),
                     .FIXED_DELAY(0) ) DUT2 ( .bus_in ( bus_in2 ), .bus_out( bus_out2 ), .clk( clk2 ) );

   beh_rand_delay #( .BUS_WIDTH(6),
                     .CLOCK_BASED(0),
                     .MIN_DELAY(5),
                     .MAX_DELAY(15),
                     .FIXED_DELAY(0) ) DUT3 ( .bus_in ( bus_in3 ), .bus_out( bus_out3 ), .clk(      ) );

// ----------------------------------------------------------------------------
// Create two clocks with different frequencies
// ----------------------------------------------------------------------------)
   initial begin : CLK1_GEN
      clk1 = 1'b0;
      forever begin #100; clk1 = ~clk1; end
   end // in

   initial begin : CLK2_GEN
      clk2 = 1'b0;
      forever begin #717; clk2 = ~clk2; end
   end // in

// ----------------------------------------------------------------------------
// Generate transitions on bus_in
// ----------------------------------------------------------------------------
   always @(posedge clk1 ) begin
      if ( test_running && $urandom_range( 100, 0 ) > 75 ) begin       // bus 1 few transitions < clock rate
         bus_in1 = $random;
      end // if
   end // always

   always @(clk2 ) begin
      if ( test_running && $urandom_range( 100, 0 ) > 25 ) begin     // many transitions above clock rate
         bus_in2 = $random;
      end // if
   end // always

   initial begin
      forever begin : GEN_BUS3
         integer delay_ps;
         if ( test_running ) bus_in3 = $random;
         delay_ps = $urandom_range( 200, 10 );
         #delay_ps;
      end // forever
   end // initial

// ----------------------------------------------------------------------------
// Count Edges
// ----------------------------------------------------------------------------
   initial begin
      bus1_in_count = 0;
      bus2_in_count = 0;
      bus3_in_count = 0;

      bus1_out_count = 0;
      bus2_out_count = 0;
      bus3_out_count = 0;
   end // initial

   always @(bus_in1)  bus1_in_count++;
   always @(bus_out1) bus1_out_count++;

   always @(bus_in2)  bus2_in_count++;
   always @(bus_out2) bus2_out_count++;

   always @(bus_in3)  bus3_in_count++;
   always @(bus_out3) bus3_out_count++;

// ----------------------------------------------------------------------------
// All good things come to an end
// ----------------------------------------------------------------------------
   initial begin 
     repeat (500) @( posedge clk1 );
     test_running = 1'b0;
     repeat (100) @( posedge clk1 );     // allow some drain time before we compare the counts
     $display("BUS1_IN=%0d(d) BUS1_OUT=%0d", bus1_in_count, bus1_out_count );
     $display("BUS2_IN=%0d(d) BUS2_OUT=%0d", bus2_in_count, bus2_out_count );
     $display("BUS3_IN=%0d(d) BUS3_OUT=%0d", bus3_in_count, bus3_out_count );
     $finish;
   end // initial


endmodule : beh_rand_delay_unit_tb

