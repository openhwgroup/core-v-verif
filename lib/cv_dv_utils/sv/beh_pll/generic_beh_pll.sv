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
//  Description : This module implements a generic, behavioural PLL.
//                This module takes in a reference clock and it outputs
//                a derived clock whose frequency is obtained by multiplying
//                the input frequency by N(the multiplier) and then dividing
//                it by M(the divisor).
//
//                Thre is an enable input. When it is low, the output 
//                clock is flat, and when the enable is de-asserted,
//                the clock is clean.
//
//                There is also a "fake" locked signal. The locked signal
//                is asserted at a random delay between min_time_to_lock_ps
//                and max_time_to_lock_ps.
// 
// ----------------------------------------------------------------------------


`timescale 1ps / 1ps

module generic_beh_pll(   input ref_clk,
                     output reg clk_out,
                          input enable,
                     input real multiply,
                     input real divide,
                     output reg locked );

   parameter default_min_time_to_lock_ps = 1_000_000;
   parameter default_max_time_to_lock_ps = 2_000_000;

   time last_edge_time;            // time when last posedge was seen
   time curr_period_ps;            // Current measured ref_clk period (in ps)
   time last_period_ps;            // Previous measured ref_clk period (in ps)
   real curr_freq_mhz;             // Ref-clk frequency (in MHz)
   real target_freq_mhz;           // Desired frequency (in MHz)
   time target_half_period_ps;     // Period of output clock

   time time_ref_clk_stable_ps;    // How long has ref_clk_been stable?
   time time_to_assert_lock;       // Randomly chose time to assert lock

   time time_to_lock_min_ps;  initial time_to_lock_min_ps = default_min_time_to_lock_ps;
   time time_to_lock_max_ps;  initial time_to_lock_max_ps = default_max_time_to_lock_ps;

   // Following flag used to hold-off for 
   //   -first edge to identify frequency
   bit  got_first_edge;  initial got_first_edge = 0;

   always @( posedge ref_clk ) begin
      if ( got_first_edge ) begin

         // Remember the period of last clock tick
         last_period_ps = curr_period_ps;

         // Measure period of current clock tick
         curr_period_ps = $time - last_edge_time;

         // Check REF CLK is stable
         if ( ( curr_period_ps == last_period_ps ) && ( enable ) ) begin
             time_ref_clk_stable_ps += curr_period_ps;
         end else begin
             // ref-clk moved - out of lock
             time_ref_clk_stable_ps = 0;
             locked = 1'b0;   // not fully realistic, real PLL may not lose lock
         end // if

         // Check if lock should be asserted
         if ( ( time_ref_clk_stable_ps > time_to_lock_min_ps )  &&
              ( time_to_assert_lock == 0 ) ) begin
            time_to_assert_lock = time_ref_clk_stable_ps + 
                                 $urandom_range( ( time_to_lock_max_ps - time_to_lock_min_ps ), 0 ) ;
         end

         if ( ( time_ref_clk_stable_ps > time_to_assert_lock ) && ( time_to_assert_lock != 0 ) )  begin
            locked = enable;
         end // if

         // Compute Frequency of output clock
         curr_freq_mhz   = 1000000.0 / curr_period_ps;
         target_freq_mhz = curr_freq_mhz * multiply / divide;
         target_half_period_ps = ( 1000000 / target_freq_mhz ) / 2;
         if ( target_half_period_ps == 0 ) begin
            $display("FATAL ERROR : TARGET PERIOD is 0");
            $finish;
         end // if
      end else begin
          locked = 1'b0;
          time_to_assert_lock = 0;
      end // if
      got_first_edge = 1;
      last_edge_time = $time;
   end // always

   initial begin
      forever begin
         wait ( ( enable === 1'b1 ) && ( target_half_period_ps > 0 ) ) ;
         clk_out = 1'b1;
         #target_half_period_ps;
         clk_out = 1'b0;
         #target_half_period_ps;
      end
   end // 

endmodule : generic_beh_pll

