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
//  Description : XRTL portion of clock agent.
//
//
// ----------------------------------------------------------------------------

interface xrtl_clock_vif ( output bit clock);

timeunit 1ns;
timeprecision 1ps;

//pragma attribute interface_tif partition_interface_xif

   // --------------------------------
   // Clock generation parameters 
   // Extracted from the clock config
   // -------------------------------
   bit enable = 1'b0;
   bit starting_signal_level = 1'b0;
   int clk_high = 10;  // for safety put a non-zero value
   int clk_low = 10;

   always begin
      wait(enable);
      if ( ( clk_high == 0 ) || ( clk_low == 0 ) )  begin
          $display("[FATAL] %m Clock Period is zero : %0d %0d",
                   clk_high, clk_low );
          $finish;
      end // if
      while(enable) begin
         clock = starting_signal_level;
         #(clk_high*1ps);
         clock = ~starting_signal_level;
         #(clk_low*1ps);
      end
   end

   function void start_clock();// pragma tbx xtf
      enable = 1'b1;
   endfunction: start_clock

   function void stop_clock(); // pragma tbx xtf
      enable = 1'b0;
   endfunction: stop_clock


    // ------------------------------------------------------------------------
    // Delay Task
    // ------------------------------------------------------------------------
    task automatic wait_n_clocks( int N );          // pragma tbx xtf
    begin
        @( posedge clock );
        repeat (N-1) @( posedge clock );
    end
    endtask : wait_n_clocks

endinterface : xrtl_clock_vif

