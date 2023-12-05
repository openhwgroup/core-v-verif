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
//  Description : Stand-alone test-bench for random beh delay
// 
// ----------------------------------------------------------------------------

module x_filter_unit_tb;

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
// Flag to stop stimulus
// ----------------------------------------------------------------------------
   reg                    test_running = 1'b1;

// ----------------------------------------------------------------------------
// Instantiate 3 instances of the DUT
// ----------------------------------------------------------------------------

   // DUT 1 : Default parameters
   x_filter #( .BUS_WIDTH(32) ) DUT1 ( .bus_in ( bus_in1 ), .bus_out( bus_out1 ) );

   // DUT 2 : Only filter x not z and force to 1
   x_filter #( .BUS_WIDTH(1),
               .FILTER_Z(0),
               .FILTER_TO(1'b1) ) DUT2 ( .bus_in ( bus_in2 ), .bus_out( bus_out2 ) );

   // DUT 3 : Only filter z not x force to 0
   x_filter #( .BUS_WIDTH(6),
               .FILTER_X(0),
               .FILTER_TO(1'b0) ) DUT3 ( .bus_in ( bus_in3 ), .bus_out( bus_out3 ) );

// ----------------------------------------------------------------------------
// Create two clocks with different frequencies
// ----------------------------------------------------------------------------)
   initial begin : CLK1_GEN
      clk1 = 1'b1;
      forever begin #100; clk1 = ~clk1; end
   end // in

   initial begin : CLK2_GEN
      clk2 = 1'b1;
      forever begin #717; clk2 = ~clk2; end
   end // in

// ----------------------------------------------------------------------------
// Generate transitions on the three buses. These include X's and Z's
// ----------------------------------------------------------------------------
   always @(posedge clk1 ) begin
      bus_in1 = rand_vect_with_x_z( );
      bus_in3 = rand_vect_with_x_z( );
   end // always

   always @(clk2 ) begin
      bus_in2 = rand_vect_with_x_z( );
   end // always


// ----------------------------------------------------------------------------
// All good things come to an end
// ----------------------------------------------------------------------------
   initial begin 
     $display("Testbench started");
     repeat (500) @( posedge clk1 );
     $display("Testbench done");
     $finish;
   end // initial

// ----------------------------------------------------------------------------
// function - random_vector with x and z
// ----------------------------------------------------------------------------
function [31:0] rand_vect_with_x_z( );
   int i;

   for( i=0 ; i<32 ; i++ ) begin
      case ( ($random % 4 ) )
         2'b00 : rand_vect_with_x_z[i] = 1'b0;
         2'b01 : rand_vect_with_x_z[i] = 1'b1;
         2'b10 : rand_vect_with_x_z[i] = 1'bx;
         2'b11 : rand_vect_with_x_z[i] = 1'bz;
      endcase
   end // for i
endfunction : rand_vect_with_x_z

endmodule : x_filter_unit_tb

