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
//  Description : Class to hold performance data about a source of data.
//                Internally, has fields to record the total number of
//                bits of data, the first and last time data was transmited.
// 
// ----------------------------------------------------------------------------

class perf_record_c extends uvm_object;

    int unsigned m_num_bits;
    int unsigned m_num_trans;
    time         m_first_time_ns;
    time         m_last_time_ns;

    `uvm_object_utils_begin( perf_record_c )
       `uvm_field_int( m_num_bits,     UVM_DEFAULT | UVM_UNSIGNED )
       `uvm_field_int( m_first_time_ns ,  UVM_DEFAULT | UVM_UNSIGNED )
       `uvm_field_int( m_last_time_ns,    UVM_DEFAULT | UVM_UNSIGNED )
    `uvm_object_utils_end

    // ------------------------------------------------------------------------
    // Constructor
    // ------------------------------------------------------------------------
    function new( string name="perf_record" );
       super.new(name);

       m_num_bits   = 0;
       m_num_trans  = 0;
       m_first_time_ns = 0;
       m_last_time_ns  = 0;
    endfunction : new

    // ------------------------------------------------------------------------
    // Increment Data Count
    // ------------------------------------------------------------------------
    function void inc_data( int unsigned num_bits_in,
                                    time time_in  );
        m_num_bits += num_bits_in;
        m_num_trans++;
        if ( m_first_time_ns == 0 ) m_first_time_ns = time_in;
        m_last_time_ns = time_in;
    endfunction : inc_data

    // ------------------------------------------------------------------------
    // Report Details
    // ------------------------------------------------------------------------
    function string get_details_string( ) ;

       real   delta_time_ns; 
       real   bw_gbps; 

       return $sformatf( "first_time=%0d last_time=%0d no. trans=%0d",
                   m_first_time_ns, m_last_time_ns, m_num_trans );

    endfunction : get_details_string

    // ------------------------------------------------------------------------
    // Report Bandwidth Returning a String
    // ------------------------------------------------------------------------
    function string get_bw_string( ) ;

       real   delta_time_ns; 
       real   bw_gbps; 

       if ( ( m_last_time_ns - m_first_time_ns ) <= 0 ) begin
          return("NaN - No time elapsed");
       end else begin
           delta_time_ns = ( real'(m_last_time_ns) ) - ( real'(m_first_time_ns) ) ;
           bw_gbps = ( real'(m_num_bits) ) / ( delta_time_ns );
           return( $sformatf( "%f Gbps", bw_gbps ) );
       end // if

    endfunction : get_bw_string

    function real get_bw_real_gbps( ) ;

       real   delta_time_ns; 
       real   bw_gbps; 

       if ( ( m_last_time_ns - m_first_time_ns ) <= 0 ) begin
          return 0.0;
       end else begin
           delta_time_ns = ( real'(m_last_time_ns) ) - ( real'(m_first_time_ns) ) ;
           bw_gbps = ( real'(m_num_bits) ) / ( delta_time_ns );
           return bw_gbps;
       end // if

    endfunction : get_bw_real_gbps

    // ------------------------------------------------------------------------
    // Report Transaction Rate Returning a String
    // ------------------------------------------------------------------------
    function string get_trans_rate_string( ) ;

       real   delta_time_ns; 
       real   trans_rate_gops;

       if ( ( m_last_time_ns - m_first_time_ns ) <= 0 ) begin
          return("NaN - No time elapsed");
       end else begin
           delta_time_ns = ( real'(m_last_time_ns) ) - ( real'(m_first_time_ns) ) ;
           trans_rate_gops = ( real'(m_num_trans) ) / ( delta_time_ns );
           return( $sformatf( "%f Gops", trans_rate_gops ) );
       end // if

    endfunction : get_trans_rate_string

endclass  : perf_record_c
