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
//  Description : This is a class which can be used to monitor the bandwidth
//                and optionally latency.
//
//                The perf_monitor assumes there can be N sources
//                and M destinations. In the simplest case N=1 and M=0.
//
//                The user registers events which can be source events
//                indicating data left a source, optionally including
//                a transaction ID.
//
//                The user can then, optionnally registers target events
//                indicating transactions have arrived. Transactions are
//                associated by their ID.
//
//                During the reporting phase, the perf_monitor generates
//                a report with 
//                  * bandwidth emitted by each source
//                  * bandwidth received by each destination
//                  * lateny (min/max/avg) from each source,dest pair
//
// 
// ----------------------------------------------------------------------------


class perf_monitor_c extends uvm_component;

`uvm_component_utils( perf_monitor_c )

    perf_record_c   m_source_db[string] ;        // organized by source
    perf_record_c   m_dest_db[string] ;          // organized by dest

    perf_record_c   m_flow_db[string][string] ;  // organized by source and dest

    trans_record_c  m_trans_db[string];          // Active transactions
                                                 // organized by transaction id

    trans_record_c  m_trans_history_db[$];       // Queue holding history

    real            m_min_latency_db[string][string];
    real            m_max_latency_db[string][string];
    real            m_tot_latency_db[string][string];

    // Flag indicating we got any traffic
    //   -used to squelch reporting if nothing seen
    bit             m_got_some_traffic_flag;

    int             m_active_trans_hwm;          // High water mark for
                                                 // number of active
                                                 // transactions

    // ------------------------------------------------------------------------
    // String for messages
    // ------------------------------------------------------------------------
    string                   m_msg_prefix        = "PERF MON";
    string                   m_msg_report_prefix = "PERF MON REPORT";

    // ------------------------------------------------------------------------
    // Constructor
    // ------------------------------------------------------------------------
    function new( string name, uvm_component parent );
       super.new( name, parent );
       m_got_some_traffic_flag = 0;
       m_active_trans_hwm = 0;
    endfunction : new

    // ------------------------------------------------------------------------
    // function reset_open_transactions
    //
    // This function clears the data structures which hold the currently 
    //   open transactions. If the data structures were not already empty,
    //   display a UVM message.
    // ------------------------------------------------------------------------
    function void reset_open_transactions( );
       if ( ( m_source_db.size() > 0        ) ||
            ( m_dest_db.size() > 0          ) ||
            ( m_flow_db.size() > 0          ) ||
            ( m_trans_db.size() > 0         ) ||
            ( m_trans_history_db.size() > 0 ) ||
            ( m_min_latency_db.size() > 0   ) ||
            ( m_max_latency_db.size() >0    ) ||
            ( m_tot_latency_db.size() > 0   ) ) begin
         `uvm_info( m_msg_prefix, "Reset done", UVM_LOW ) ;
       end // if
       m_source_db.delete();
       m_dest_db.delete();
       m_flow_db.delete();
       m_trans_db.delete();
       m_trans_history_db.delete();
       m_min_latency_db.delete();
       m_max_latency_db.delete();
       m_tot_latency_db.delete();
    endfunction : reset_open_transactions

    // -----------------------------------------------------------------------
    // Reset Phase
    // -----------------------------------------------------------------------
    task reset_phase( uvm_phase phase );
       super.reset_phase( phase );
       reset_open_transactions( );
    endtask : reset_phase

    // ------------------------------------------------------------------------
    // Register Source Data
    // ------------------------------------------------------------------------
    function void register_source_event( int unsigned num_bits, 
                                         string       source_id = "Source 0",
                                         time         source_time_ns = 0,
                                         string       trans_id  = "" );

       perf_record_c  m_new_perf_record;
       trans_record_c m_new_trans_record;

       // We've seen something
       m_got_some_traffic_flag = 1;

       // If user didn't explicitely pass time, use $time
       if ( source_time_ns == 0 ) begin
          source_time_ns = $time;
       end // if

       // Debug messages
       `uvm_info( m_msg_prefix,
                 $sformatf("%0d bits from SOURCE %s at time %0t.%0s", 
                   num_bits, source_id, source_time_ns, 
                   ( trans_id == "" ) ? "" : $sformatf("TRANS=%s", trans_id ) ),
                   UVM_MEDIUM );


       // Create a record for this source, if it's the first time we see it
       if ( !(m_source_db.exists( source_id ) ) ) begin
          m_new_perf_record = perf_record_c::type_id::create( $sformatf("PERF_SOURCE_%s", source_id ) ) ;
          m_new_perf_record.m_first_time_ns = source_time_ns ;
          m_source_db[source_id] = m_new_perf_record;
       end // if

       // Update the record with current data
       m_source_db[source_id].inc_data( num_bits, source_time_ns );

       // Create a transaction record, if the user provided a transaction ID
       if ( trans_id != "" )  begin
          if ( !(m_trans_db.exists( trans_id ) ) ) begin
             m_new_trans_record = trans_record_c::type_id::create( trans_id ) ;
             m_new_trans_record.m_source_time_ns = source_time_ns ;
             m_new_trans_record.m_source_id   = source_id ;
             m_new_trans_record.m_num_bits    = num_bits;
             m_trans_db[trans_id] = m_new_trans_record;

             `uvm_info( m_msg_prefix, $sformatf("ADDED TRANS=%s TO TRANS DB (SOURCE=%0s)", trans_id, source_id), UVM_HIGH );

             // Update 
             if ( m_trans_db.size() > m_active_trans_hwm ) begin
                m_active_trans_hwm = m_trans_db.size();
             end // if

          end else begin
             `uvm_error( "PERF MON", $sformatf("DUPLICATE TRANSACTION WITH ID (%0s) FROM SOURCE %d",
                         trans_id, source_id ) );
          end // if
       end // if

    endfunction : register_source_event

    // ------------------------------------------------------------------------
    // Register Destination Data
    // ------------------------------------------------------------------------
    function void register_dest_event( int unsigned num_bits  = 0,
                                       string       dest_id   = "Dest",
                                         time       dest_time_ns = 0,
                                       string       trans_id  = "" );

       perf_record_c  m_new_perf_record;
       trans_record_c m_copy_trans_record;
       string         source_id;

       // We've seen something
       m_got_some_traffic_flag = 1;

       // If user didn't explicitely pass time, use $time
       if ( dest_time_ns == 0 ) begin
          dest_time_ns = $time;
       end // if

       // Debug messages
       `uvm_info( m_msg_prefix,
                 $sformatf("%0d bits from DEST %s at time %0t.%0s", 
                   num_bits, dest_id, dest_time_ns, 
                   ( trans_id == "" ) ? "" : $sformatf("TRANS=%s", trans_id ) ),
                   UVM_MEDIUM );


       // Create a record for this dest, if it's the first time we see it
       if ( !(m_dest_db.exists( dest_id ) ) ) begin
          m_new_perf_record = perf_record_c::type_id::create( $sformatf("PERF_DEST_%s", dest_id ) ) ;
          m_new_perf_record.m_first_time_ns = dest_time_ns ;
          m_dest_db[dest_id] = m_new_perf_record;
       end // if

       // Update the record with current data
       m_dest_db[dest_id].inc_data( num_bits, dest_time_ns );

       // Lookup the transaction record, if the user provided a transaction ID
       if ( trans_id != "" )  begin
          if ( (m_trans_db.exists( trans_id ) ) ) begin
             // now we found the source, remove from the trans_db (active)
             //    and store the record in the trans_history_db (for later generating histogram)
             m_trans_db[trans_id].m_dest_time_ns = dest_time_ns ;
             m_trans_db[trans_id].m_dest_id   = dest_id;
             $cast( m_copy_trans_record,  m_trans_db[trans_id].clone() );
             m_trans_history_db.push_back( m_copy_trans_record );

             source_id = m_copy_trans_record.m_source_id;
             `uvm_info( m_msg_prefix, $sformatf("REMOVED TRANS=%s FROM TRANS DB. LATENCY=%0s", 
                 trans_id, m_trans_db[trans_id].get_latency_string() ), UVM_HIGH );
             m_trans_db.delete( trans_id );

             // Update Flow DB ( organized as source, dest tuples)
             if ( source_id != "" ) begin
                if ( ( ! m_flow_db.exists( source_id ) ) ||                // 1st check source index defined
                     ( ! m_flow_db[source_id].exists( dest_id ) ) ) begin  // then check dest index
                   m_new_perf_record = perf_record_c::type_id::create( $sformatf("PERF_DEST_%s", dest_id ) ) ;
                   m_new_perf_record.m_first_time_ns = dest_time_ns ;
                   m_flow_db[source_id][dest_id] = m_new_perf_record;
                   `uvm_info(m_msg_prefix, $sformatf("UPDATING FLOW FROM %s TO %s",
                      source_id, dest_id) , UVM_HIGH );
                end // if
                m_flow_db[source_id][dest_id].inc_data( num_bits, dest_time_ns );
             end // if

          end else begin
             `uvm_error( "PERF MON", $sformatf("TRANSACTION ID (%0s) NOT FOUND IN DB (FROM DEST=%s)",
                         trans_id, dest_id ) );
          end // if
       end // if

    endfunction : register_dest_event

    // ------------------------------------------------------------------------
    // Reporting
    // ------------------------------------------------------------------------
    virtual function void report_phase( uvm_phase phase ) ;
       string curr_source;
       string curr_dest;
       real   curr_latency;

       string base_file_name;
       string curr_test_name;
       string perf_csv;
       string perf_test;
       string file_name;
       int    fh;
       int    i;

       if ( m_got_some_traffic_flag ) begin
          `uvm_info( m_msg_report_prefix, "PERF REPORT START", UVM_NONE );
   
          // ---------------------------------------------------
          // Report the Active Trans HWM
          // ---------------------------------------------------
          `uvm_info( m_msg_report_prefix, $sformatf("ACTIVE TRANS HWM=%0d", m_active_trans_hwm ), UVM_NONE );

          // ---------------------------------------------------
          // Report bandwidth + Transaction rate for each source
          // ---------------------------------------------------
          if ( m_source_db.first( curr_source ) ) begin
             do begin
                `uvm_info( m_msg_report_prefix,
                    $sformatf("SOURCE %s BANDWIDTH = %s : TRANSACTION RATE = %s [DETAILS : %s]",
                      curr_source, 
                      m_source_db[ curr_source ].get_bw_string(),
                      m_source_db[ curr_source ].get_trans_rate_string(),
                      m_source_db[ curr_source ].get_details_string() ), 
                    UVM_NONE );
             end while ( m_source_db.next( curr_source ) );
          end // if
                         
          // -------------------------------------------------
          // Report bandwidth + Transaction rate for each dest
          // -------------------------------------------------
          if ( m_dest_db.first( curr_dest ) ) begin
             do begin
                `uvm_info( m_msg_report_prefix,
                    $sformatf("DEST %s BANDWIDTH = %s : TRANSACTION RATE = %s [DETAILS : %s]",
                      curr_dest, 
                      m_dest_db[ curr_dest ].get_bw_string(),
                      m_dest_db[ curr_dest ].get_trans_rate_string(),
                      m_dest_db[ curr_dest ].get_details_string() ), 
                    UVM_NONE );
             end while ( m_dest_db.next( curr_dest ) );
          end // if
                         
          // -----------------------------------------------------------------
          // Compute Latencies (min/max/avg) for each pair
          // -----------------------------------------------------------------
          for( i=0 ; i < m_trans_history_db.size() ; i++ ) begin
             curr_source = m_trans_history_db[i].m_source_id ;
             curr_dest   = m_trans_history_db[i].m_dest_id   ;
             curr_latency =  m_trans_history_db[i].m_dest_time_ns - m_trans_history_db[i].m_source_time_ns ;
   
             // Check if we have seen this pair previously
             if ( ( !m_min_latency_db.exists( curr_source ) ) ||
                  ( !m_min_latency_db[curr_source].exists( curr_dest ) ) ) begin
                // If not, create the initial data
                m_min_latency_db[curr_source][curr_dest] = curr_latency;
                m_max_latency_db[curr_source][curr_dest] = curr_latency;
                m_tot_latency_db[curr_source][curr_dest] = curr_latency;
             end else begin
                // Otherwise, update the data
                if ( curr_latency < m_min_latency_db[curr_source][curr_dest] )
                   m_min_latency_db[curr_source][curr_dest] = curr_latency;
                if ( curr_latency > m_max_latency_db[curr_source][curr_dest] )
                  m_max_latency_db[curr_source][curr_dest] = curr_latency;
                m_tot_latency_db[curr_source][curr_dest] += curr_latency;
             end // if
          end // for
   
          // ----------------------------------------------------------------------
          // Report bandwidth + Latencies for each pair of sources and destinations
          // ----------------------------------------------------------------------
          if ( m_flow_db.first( curr_source ) ) begin
             do begin
                if ( m_flow_db[curr_source].first( curr_dest ) ) begin
                   do begin
                      if ( m_flow_db[curr_source][curr_dest].m_num_trans >= 2 ) begin
                         `uvm_info( m_msg_report_prefix,
                             $sformatf("FLOW %s TO %s : BANDWIDTH = %s : TRANSACTION RATE = %s : LATENCY(MIN/MAX/AVG) = %3.2f/%3.2f/%3.2f [ DETAILS : %s]",
                               curr_source, curr_dest,
                               m_flow_db[curr_source][curr_dest].get_bw_string(),
                               m_flow_db[curr_source][curr_dest].get_trans_rate_string(),
                               m_min_latency_db[curr_source][curr_dest],
                               m_max_latency_db[curr_source][curr_dest],
                               m_tot_latency_db[curr_source][curr_dest] / m_flow_db[curr_source][curr_dest].m_num_trans,
                               m_flow_db[curr_source][curr_dest].get_details_string() ), 
                               UVM_NONE );
                      end
                   end while ( m_flow_db[curr_source].next( curr_dest ) );
                end // if
             end while ( m_flow_db.next( curr_source ) );
          end // if
          
          // -----------------------------------------------------------------
          // Write Raw Transaction Log
          // -----------------------------------------------------------------
          if (!$value$plusargs("PERF_LOG=%s", perf_test )) begin
              perf_test = "NO";
          end
          
          if (!$value$plusargs("UVM_TESTNAME=%s", curr_test_name )) begin
              curr_test_name = "test_name";
          end // if
          if (!$value$plusargs("PERF_CSV=%s", perf_csv)) begin
            perf_csv = curr_test_name;
          end
          if (perf_csv != curr_test_name) begin 
            curr_test_name = perf_csv;
            `uvm_info(m_msg_prefix,$sformatf("Curr test name = %s",curr_test_name),UVM_NONE)
          end

          base_file_name = $sformatf("%s__%s__perf_trace", curr_test_name, get_name() );
          file_name = { base_file_name, "_raw.csv" };
          if (( m_trans_history_db.size() > 0 ) && (perf_test == "YES")) begin
             fh = $fopen( file_name, "w" );
             if (!fh) begin
                 `uvm_error( "FILE ERROR", $sformatf("Unable to open %s for writing", file_name ) ) ;
             end else begin
                 $fdisplay( fh, "SOURCE,DEST,SIZE (bits),START TIME(ns),END TIME(ns),LATENCY(ns)" );
                 for( i=0 ; i < m_trans_history_db.size() ; i++ ) begin
                     $fdisplay( fh, "%s,%s,%0d,%0d,%0d,%0d",
                         m_trans_history_db[i].m_source_id, 
                         m_trans_history_db[i].m_dest_id,
                         m_trans_history_db[i].m_num_bits,
                         m_trans_history_db[i].m_source_time_ns,
                         m_trans_history_db[i].m_dest_time_ns, 
                         m_trans_history_db[i].m_dest_time_ns-m_trans_history_db[i].m_source_time_ns);
                 end // for
   
                 $fclose( fh );
                 `uvm_info( m_msg_report_prefix, $sformatf("Wrote raw trace file to %s", file_name ), UVM_NONE );
             end // if
          end // if
   
          `uvm_info( m_msg_report_prefix, "PERF REPORT END", UVM_NONE );
       end // if m_got_some_traffic

    endfunction : report_phase

    // USER APIs to get the Bandwidth
    function string get_bw_per_source(string curr_source);
     if ( m_source_db.exists( curr_source ) ) begin
        return m_source_db[ curr_source ].get_bw_string();
     end  else begin
       `uvm_warning( m_msg_prefix, $sformatf("source id not found %s",  curr_source) );
       return "";
     end

    endfunction

    function string get_bw_per_destination(string curr_destination);
      if ( m_dest_db.exists( curr_destination ) ) begin
         return m_dest_db[ curr_destination ].get_bw_string();
     end  else begin
       `uvm_warning( m_msg_prefix, $sformatf("destination id not found %s",  curr_destination) );
       return "";
     end
    endfunction

    // user API to check the bw within a limit 
    function void check_bw_per_flow(string source, string dest, real expected_bw, int error_percentage);
          if ( m_flow_db.exists( source ) ) begin
            if ( m_flow_db[source].exists( dest ) ) begin
              if ( m_flow_db[source][dest].get_bw_real_gbps()  >=  expected_bw) begin
                if(((m_flow_db[source][dest].get_bw_real_gbps() - expected_bw)*100/m_flow_db[source][dest].get_bw_real_gbps()) > error_percentage) begin
                    `uvm_error( m_msg_report_prefix, $sformatf("FLOW %s TO %s : BANDWIDTH = %3.2f : Expected = %3.2f DIFF=%3.2f",
                                                           source, dest,
                                                           m_flow_db[source][dest].get_bw_real_gbps(), expected_bw,
                                                           ((m_flow_db[source][dest].get_bw_real_gbps() - expected_bw)*100/m_flow_db[source][dest].get_bw_real_gbps())
                                                           ));
                end else begin
                    `uvm_info( m_msg_report_prefix, $sformatf("FLOW %s TO %s : BANDWIDTH = %3.2f : Expected = %3.2f DIFF=%3.2f",
                                                           source, dest,
                                                           m_flow_db[source][dest].get_bw_real_gbps(), expected_bw,
                                                           ((m_flow_db[source][dest].get_bw_real_gbps() - expected_bw)*100/m_flow_db[source][dest].get_bw_real_gbps())
                                                           ), UVM_LOW);
                end
              end else begin
                if((( expected_bw - m_flow_db[source][dest].get_bw_real_gbps())*100/m_flow_db[source][dest].get_bw_real_gbps()) > error_percentage) begin
                    `uvm_error( m_msg_report_prefix, $sformatf("FLOW %s TO %s : BANDWIDTH = %3.2f : Expected = %3.2f DIFF=%3.2f",
                                                           source, dest,
                                                           m_flow_db[source][dest].get_bw_real_gbps(), expected_bw,
                                                           ((m_flow_db[source][dest].get_bw_real_gbps() - expected_bw)*100/m_flow_db[source][dest].get_bw_real_gbps())
                                                           ));
                end else begin
                    `uvm_info( m_msg_report_prefix, $sformatf("FLOW %s TO %s : BANDWIDTH = %3.2f : Expected = %3.2f DIFF=%3.2f",
                                                           source, dest,
                                                           m_flow_db[source][dest].get_bw_real_gbps(), expected_bw,
                                                           ((m_flow_db[source][dest].get_bw_real_gbps() - expected_bw)*100/m_flow_db[source][dest].get_bw_real_gbps())
                                                           ), UVM_LOW);
                end
              end
            end // if
          end // if
    endfunction 
endclass : perf_monitor_c

