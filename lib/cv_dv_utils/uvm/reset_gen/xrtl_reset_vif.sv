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
//  Description : XRTL portion of reset agent.
//
//
// ----------------------------------------------------------------------------

interface xrtl_reset_vif ( input bit clk,
                          output bit reset,
                          output bit reset_n,
                          output bit post_shutdown_phase );

//pragma attribute interface_tif partition_interface_xif
timeunit 1ns;
timeprecision 100ps;

//pragma attribute interface_tif partition_interface_xif
import reset_vif_xrtl_pkg::*;

    //--------------------------------------------------------------------
    // Parameters
    //--------------------------------------------------------------------
    parameter init_value = 1'b1;
    parameter init_assert = 50;
    parameter post_reset_delay = 25;

    //--------------------------------------------------------------------
    // HVL Object for Interface
    //--------------------------------------------------------------------
    xrtl_reset_vif_c hvl_obj;

    //--------------------------------------------------------------------
    // Declarations
    //--------------------------------------------------------------------
    bit [31:0] ra_cnt_FF;
    bit        reset_D1_FF;

    function void assert_reset( input int assert_count = init_assert );
        ra_cnt_FF = assert_count;
    endfunction : assert_reset

    function void set_post_shutdown_phase_started( );
        post_shutdown_phase <= 1;
    endfunction : set_post_shutdown_phase_started

    //--------------------------------------------------------------------
    // reset generation
    //--------------------------------------------------------------------
    // Initialization supported by Veloce
    initial begin
        reset <= init_value;
        ra_cnt_FF = init_assert;
        post_shutdown_phase <= 1'b0;
    end

    assign reset_n = ~reset;

    //--------------------------------------------------------------------
    // Counter to Drive Reset
    //--------------------------------------------------------------------
    always @(posedge clk) begin
        ra_cnt_FF = ( |ra_cnt_FF ) ? ( ra_cnt_FF - 1 ) : 0;
        reset <= |ra_cnt_FF;  // wait for ra_cnt to be zero
    end

    //--------------------------------------------------------------------
    // Generate Events on Reset Assertion and De Assertion
    //--------------------------------------------------------------------
   always @( posedge clk) begin
       reset_D1_FF <= reset;
       if (  reset && !reset_D1_FF ) ->hvl_obj.reset_asserted;
       if ( ra_cnt_FF == 'd1 )  begin  // assert event on clock when reset
                                       // drops
          repeat (1+post_reset_delay) @( posedge clk );
          ->hvl_obj.reset_deasserted;
       end // if
   end // always

endinterface : xrtl_reset_vif

