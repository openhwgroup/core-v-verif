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
//  Description : Class to hold performance data about a specific
//                transaction. Internally, this object has information
//                about the source and dest of the transactions as
//                well as the time stamps.
// 
// ----------------------------------------------------------------------------

class trans_record_c extends uvm_object;

    int unsigned m_num_bits;
    string       m_source_id;
    string       m_dest_id;
    time         m_source_time_ns;
    time         m_dest_time_ns;

    `uvm_object_utils_begin( trans_record_c )
       `uvm_field_int( m_num_bits,      UVM_DEFAULT | UVM_UNSIGNED )
       `uvm_field_int( m_source_time_ns ,  UVM_DEFAULT | UVM_UNSIGNED )
       `uvm_field_int( m_dest_time_ns,     UVM_DEFAULT | UVM_UNSIGNED )
       `uvm_field_string( m_source_id,  UVM_DEFAULT | UVM_UNSIGNED )
       `uvm_field_string( m_dest_id,    UVM_DEFAULT | UVM_UNSIGNED )
    `uvm_object_utils_end

    // ------------------------------------------------------------------------
    // Constructor
    // ------------------------------------------------------------------------
    function new( string name="trans_record" );
       super.new(name);

       m_num_bits    = 0;
       m_source_time_ns = 0;
       m_dest_time_ns   = 0;
       m_source_id   = "";
       m_dest_id   = "";

    endfunction : new

    // ------------------------------------------------------------------------
    // Report Details
    // ------------------------------------------------------------------------
    function string get_details_string( ) ;

       real   delta_time_ns; 
       real   bw_gbps; 

       return $sformatf( "source_time=%0d soure_id=%0s dest_time=%0d dest_id=%0s",
                   m_source_time_ns, m_source_id, m_dest_time_ns, m_dest_id );

    endfunction : get_details_string

    // ------------------------------------------------------------------------
    // Report Latency Returning a String
    // ------------------------------------------------------------------------
    function string get_latency_string( ) ;

       real   delta_time_ns; 

       if ( ( m_dest_time_ns - m_source_time_ns ) < 0 ) begin
          return("NaN - Negative latency??");
       end else begin
           delta_time_ns = ( real'(m_dest_time_ns) ) - ( real'(m_source_time_ns) ) ;
           return( $sformatf( "%f ns", delta_time_ns ) );
       end // if
    endfunction : get_latency_string

    // ------------------------------------------------------------------------
    // Report Latency Returning a Float
    // ------------------------------------------------------------------------
    function real get_latency_ns_float( ) ;

       real   delta_time_ns; 

       if ( ( m_dest_time_ns - m_source_time_ns ) < 0 ) begin
          `uvm_warning( "PERF MON", "Negative latency" );
          return 0.0;
       end else begin
           delta_time_ns = ( real'(m_dest_time_ns) ) - ( real'(m_source_time_ns) ) ;
           return delta_time_ns;
       end // if
    endfunction : get_latency_ns_float

endclass  : trans_record_c
