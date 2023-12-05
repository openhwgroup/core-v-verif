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
//  Description : Config object to configure the clock monitor
// ----------------------------------------------------------------------------

class clock_monitor_config_c extends uvm_object;

    //////////////////////////////////////////////////////
    //Configuration Parameters 
    /////////////////////////////////////////////////////

    rand  int m_clock_monitor_enable;
    rand  int m_clock_monitor_sva_enable;

     // ------------------------------------------------------------------------
     // Utilities for the variables
     // ------------------------------------------------------------------------

    `uvm_object_utils_begin( clock_monitor_config_c )
      `uvm_field_int( m_clock_monitor_enable,     UVM_DEFAULT )
      `uvm_field_int( m_clock_monitor_sva_enable, UVM_DEFAULT )
    `uvm_object_utils_end

    function new( string name ="" );
      super.new( name );
    endfunction

endclass : clock_monitor_config_c
