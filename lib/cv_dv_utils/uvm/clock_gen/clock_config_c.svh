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
//  Description : config object to configure the clock 
//                starting_signal_level, clock_frequency, duty_cycle
//                
// 
// ----------------------------------------------------------------------------

class clock_config_c extends uvm_object;


    //////////////////////////////////////////////////////
    //Configuration Parameters
    //To be driven by the driver 
    /////////////////////////////////////////////////////
    rand  bit m_starting_signal_level;
    rand  int m_clock_frequency = 10;   // safe default value in case no randomization is done
    rand  int m_duty_cycle = 50;        // safe default value in case no randomization is done

    constraint c_starting_signal_level { m_starting_signal_level dist { 1'b1 := 5,  1'b0 := 5};};
    constraint c_clock_frequency       { m_clock_frequency  > 0;                     };
    constraint c_duty_cycle            { m_duty_cycle == 50;                         };

     // ------------------------------------------------------------------------
     // Utilities for the variables
     // ------------------------------------------------------------------------
    `uvm_object_utils_begin( clock_config_c )
        `uvm_field_int( m_starting_signal_level,   UVM_DEFAULT )
        `uvm_field_int( m_clock_frequency,         UVM_DEFAULT )
        `uvm_field_int( m_duty_cycle,              UVM_DEFAULT )
    `uvm_object_utils_end

    function new( string name ="" );
        super.new( name );
    endfunction

endclass : clock_config_c
