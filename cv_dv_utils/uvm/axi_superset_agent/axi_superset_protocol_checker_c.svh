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
//  Description : Collect request/response from the monitor and the response
//                model and compare them to verify the axi_superset protocol
//
// ----------------------------------------------------------------------------

// -----------------------------------------------------------------------
// Class axi_superset_protocol_checker_c
// -----------------------------------------------------------------------
class axi_superset_protocol_checker_c extends uvm_scoreboard;

  `uvm_component_utils(axi_superset_protocol_checker_c)

  protected string name                ;
  event            reset_asserted      ;
  event            reset_deasserted    ;

  // Variable to configure the memory map concerning the scoreboard instance
  protected int    bus_size            ;

  // -----------------------------------------------------------------------
  // Analysis Ports
  // -----------------------------------------------------------------------
  uvm_tlm_analysis_fifo #(axi_superset_txn_c) m_write_req_packets_collected ;
  uvm_tlm_analysis_fifo #(axi_superset_txn_c) m_read_req_packets_collected  ;
  uvm_tlm_analysis_fifo #(axi_superset_txn_c) m_write_rsp_packets_collected ;
  uvm_tlm_analysis_fifo #(axi_superset_txn_c) m_read_rsp_packets_collected  ;

  // -----------------------------------------------------------------------
  // Data Structures to store axi_superset/chi req/rsp
  // -----------------------------------------------------------------------
  // Data structure to store analysis port outputs
  axi_superset_txn_c m_wreq_packet ;
  axi_superset_txn_c m_rreq_packet ;
  axi_superset_txn_c m_wrsp_packet ;
  axi_superset_txn_c m_rrsp_packet ;

  // Associative array to store transaction
  axi_superset_txn_c m_read_txn_db[axi_sig_id_t][$]  ;
  axi_superset_txn_c m_write_txn_db[axi_sig_id_t][$] ;

  // -----------------------------------------------------------------------
  // Counter for the number of request/response
  // -----------------------------------------------------------------------
  protected int m_count_read_req  ;
  protected int m_count_write_req ;
  protected int m_count_read_rsp  ;
  protected int m_count_write_rsp ;

  // -----------------------------------------------------------------------
  // Counters for expected responses. In case of some ATOPs, one request
  // gives rise to both read and write responses
  // -----------------------------------------------------------------------
  protected int m_count_exp_read_rsp;
  protected int m_count_exp_write_rsp;

  // -----------------------------------------------------------------------
  // Counter for the total number of bytes
  // -----------------------------------------------------------------------
  protected int m_write_bytes ;
  protected int m_read_bytes  ;

  // -----------------------------------------------------------------------
  // Agent configuration
  // -----------------------------------------------------------------------
  axi_superset_config_c  m_agent_config ;

  // ------------------------------------------------------------------------
  // Constructor
  // ------------------------------------------------------------------------
  function new(string name, uvm_component parent);
        super.new(name, parent);
        this.name = name;


  endfunction: new

  // ------------------------------------------------------------------------
  // Function set/get
  // ------------------------------------------------------------------------
  // AGENT CONFIGURATION
  function axi_superset_config_c get_agent_config();
    get_agent_config = m_agent_config  ;
  endfunction : get_agent_config

  function void set_agent_config( axi_superset_config_c config_i );
    `uvm_info(this.name,
              $sformatf("Setting the agent configuraiton CFG=%0s", config_i.convert2string() ),
              UVM_DEBUG)
    m_agent_config = config_i ;
  endfunction: set_agent_config

  // -----------------------------------------------------------------------
  // Build Phase
  // -----------------------------------------------------------------------
  function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      // Initialisation of the uvm_tlm_analysis_fifo for axi_superset interface
      m_write_req_packets_collected = new("m_write_req_packets_collected" , this) ;
      m_read_req_packets_collected  = new("m_read_req_packets_collected"  , this) ;
      m_write_rsp_packets_collected = new("m_write_rsp_packets_collected" , this) ;
      m_read_rsp_packets_collected  = new("m_read_rsp_packets_collected"  , this) ;

      // Initialisation of the axi_superset packets for the covergroups
      m_wreq_packet = axi_superset_txn_c::type_id::create("m_wreq_packet" , this) ;
      m_rreq_packet = axi_superset_txn_c::type_id::create("m_rreq_packet" , this) ;
      m_wrsp_packet = axi_superset_txn_c::type_id::create("m_wrsp_packet" , this) ;
      m_rrsp_packet = axi_superset_txn_c::type_id::create("m_rrsp_packet" , this) ;
 
      // Initialisation of the counters of the testbench
      // axi_superset transactions counters
      m_count_read_req  = 0 ;
      m_count_write_req = 0 ;
      m_count_read_rsp  = 0 ;
      m_count_write_rsp = 0 ;

      m_count_exp_read_rsp  = 0 ;
      m_count_exp_write_rsp = 0 ;

      // Number of bytes counters
      m_write_bytes = 0 ;
      m_read_bytes  = 0 ;

      `uvm_info(this.name, "Build stage complete.", UVM_LOW)
  endfunction: build_phase
  
  // ------------------------------------------------------------------------
  // Pre reset phase
  // ------------------------------------------------------------------------
  virtual task pre_reset_phase(uvm_phase phase);
      -> reset_asserted;
      `uvm_info(this.name, "Pre Reset stage complete.", UVM_LOW)
  endtask : pre_reset_phase

  // ------------------------------------------------------------------------
  // Reset phase
  // ------------------------------------------------------------------------
  task reset_phase(uvm_phase phase );
    super.reset_phase(phase);

    // Flushing the axi_superset uvm_tlm_analysis_fifo
    m_write_req_packets_collected.flush() ;
    m_read_req_packets_collected.flush()  ;
    m_write_rsp_packets_collected.flush() ;
    m_read_rsp_packets_collected.flush()  ;

    // Reset of the associative arrays
    m_read_txn_db.delete()  ;
    m_write_txn_db.delete() ;

      // Initialisation of the counters of the testbench
      // axi_superset transactions counters
      m_count_read_req  = 0 ;
      m_count_write_req = 0 ;
      m_count_read_rsp  = 0 ;
      m_count_write_rsp = 0 ;

      m_count_exp_read_rsp  = 0 ;
      m_count_exp_write_rsp = 0 ;

      // Number of bytes counters
      m_write_bytes = 0 ;
      m_read_bytes  = 0 ;
    `uvm_info(this.name, "Reset stage complete.", UVM_LOW)
  endtask: reset_phase
  
  // ------------------------------------------------------------------------
  // Post reset phase
  // ------------------------------------------------------------------------
  virtual task post_reset_phase(uvm_phase phase);
    -> reset_deasserted;
    `uvm_info(this.name, "Post Reset stage complete.", UVM_LOW)
  endtask : post_reset_phase

  // -----------------------------------------------------------------------
  // Run Phase
  // -----------------------------------------------------------------------
  virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      forever begin
        @(reset_deasserted);
        fork

          collect_write_req ( phase ) ;
          collect_read_req  ( phase ) ;
          collect_write_rsp ( phase ) ;
          collect_read_rsp  ( phase ) ;

        join_none
        @(reset_asserted);
        disable fork;
      end
  endtask: run_phase


  // -----------------------------------------------------------------------
  // -----------------------------------------------------------------------
  // Interface tasks 
  // -----------------------------------------------------------------------
  // -----------------------------------------------------------------------

  // -----------------------------------------------------------------------
  // Task collect_write_req
  //
  // Collect input write requests from the axi interface
  // -----------------------------------------------------------------------
  virtual task collect_write_req( uvm_phase phase );
    axi_superset_txn_c  write_req;

    forever begin
        // Wait to receive a packet from the analysis port and store it in the
        // m_axi_superset_req_packet data structure
        m_write_req_packets_collected.get(m_wreq_packet);

        // Creating a new object to store the input packet data structure,
        // before storing it inside a queue
        write_req = new;
        $cast(write_req, m_wreq_packet.clone());

        // Verification of the axi_superset write request
        check_write_req ( write_req );

        // Register the axi_superset transaction in an associative array
        m_write_txn_db[write_req.m_id].push_front(write_req);

        // Increment write request counter
        m_count_write_req++;
        m_count_exp_write_rsp++;

    end // forever
  endtask: collect_write_req

  // -----------------------------------------------------------------------
  // Task collect_read_req
  //
  // Collect input read requests from the axi interface
  // -----------------------------------------------------------------------
  virtual task collect_read_req( uvm_phase phase );
    string ids_s;
    axi_superset_txn_c  read_req;

    forever begin
        // Wait to receive a packet from the analysis port and store it in the
        // m_req_packet data structure
        m_read_req_packets_collected.get(m_rreq_packet);

        // Creating a new object to store the input packet data structure,
        // before storing it inside a queue
        read_req = new;
        $cast(read_req, m_rreq_packet.clone());

        // Verification of the axi read request
        check_read_req ( read_req );

        // Register the axi transaction in an associative array
        m_read_txn_db[read_req.m_id].push_front(read_req);

        // Increment read request counter
        m_count_read_req++;
        m_count_exp_read_rsp++;

    end // forever
  endtask: collect_read_req

  // -----------------------------------------------------------------------
  // Task collect_write_rsp
  //
  // Collect input write response from the axi interface
  // -----------------------------------------------------------------------
  virtual task collect_write_rsp( uvm_phase phase );
    axi_superset_txn_c  write_rsp;

    forever begin
        // Wait to receive a packet from the analysis port and store it in the
        // m_rsp_packet data structure
        m_write_rsp_packets_collected.get( m_wrsp_packet );

        // Creating a new object to store the response packet information,
        // before storing it inside a queue
        write_rsp = new;
        $cast( write_rsp, m_wrsp_packet.clone() );

        // Verification of the axi write response
        check_write_rsp ( write_rsp );

        // Increment the write rsp counter
        m_count_write_rsp++;

    end
  endtask : collect_write_rsp

  // -----------------------------------------------------------------------
  // Task collect_read_rsp
  //
  // Collect input read response from the axi interface
  // -----------------------------------------------------------------------
  virtual task collect_read_rsp( uvm_phase phase );
    axi_superset_txn_c  read_rsp;

    forever begin
        // Wait to receive a packet from the analysis port and store it in the
        // m_rsp_packet data structure
        m_read_rsp_packets_collected.get( m_rrsp_packet );

        // Creating a new object to store the response packet information,
        // before storing it inside a queue
        read_rsp = new;
        $cast( read_rsp, m_rrsp_packet.clone() );
        
        // If the rsp is the last of its burst, increment the corresponding
        // counter and register the event for the perf mon
        // Call the corresponding task to compare requests/responses
        check_read_rsp ( read_rsp );

        // Increment the read rsp counter
        m_count_read_rsp++;

    end
  endtask : collect_read_rsp


  // -----------------------------------------------------------------------
  // -----------------------------------------------------------------------
  //
  // VERIFICATION TASKS
  //
  // -----------------------------------------------------------------------
  // -----------------------------------------------------------------------

  // -----------------------------------------------------------------------
  // Task check_write_req
  //
  // Compare the corresponding write request from the source to the write
  // request received on the dest interface
  // -----------------------------------------------------------------------
  task check_write_req ( 
    axi_superset_txn_c  write_req
  );
    int nb_flits   ; // Number of flits of data of the transaction
    int bus_nbytes ; // Number of bytes of the data bus
    int nb_bytes   ; // Maximum number of bytes of the transaction for each flit of data

    // Computing some values necessary for the verification of the transaction
    nb_flits   = write_req.m_len + 1 ;
    bus_nbytes = m_agent_config.get_txn_config().get_data_width()/8 ;
    nb_bytes   = 2**write_req.m_size ;

    // If the unique id is configured in the agent, and that the ID of the
    // transaction alwritey exist, print an error.
    if ( m_agent_config.get_id_management_enable() ) begin
      if ( m_write_txn_db.exists(write_req.m_id) )
        `uvm_error(this.name,
          $sformatf("The agent was configured to generate only for unique ID, and the ID=%0h(h) is currently also used by another write transaction", write_req.m_id) )
    end

    // Check the number of flit of data
    if ( write_req.m_data.size() != nb_flits ) begin
      `uvm_error(this.name,
        $sformatf("Number of flits of data are not matching: WRITE_REQ=%0d(d) WRITE_REQ_LEN=%0h(h) ; WRITE_REQ_DATA=%0p(p)",
                  m_count_write_req,
                  write_req.m_len,
                  write_req.m_data ) )
    end

    // Check the number of flit of wstrb
    if ( write_req.m_wstrb.size() != nb_flits ) begin
      `uvm_error(this.name,
        $sformatf("Number of flits of wstrb are not matching: WRITE_REQ=%0d(d) WRITE_REQ_LEN=%0h(h) ; WRITE_REQ_WSTRB=%0p(p)",
                  m_count_write_req,
                  write_req.m_len,
                  write_req.m_wstrb ) )
    end

    // Check the number of flit of last
    if ( write_req.m_last.size() != nb_flits ) begin
      `uvm_error(this.name,
        $sformatf("Number of flits of last are not matching: WRITE_REQ=%0d(d) WRITE_REQ_LEN=%0h(h) ; WRITE_REQ_LAST=%0p(p)",
                  m_count_write_req,
                  write_req.m_len,
                  write_req.m_last ) )
    end

    // Check that only the last flit of last is tied to 1'b1
    foreach( write_req.m_last[i] ) begin
      if ( ( i != write_req.m_last.size() - 1 ) ? (write_req.m_last[i] == 1) : (write_req.m_last[i] == 0 ) ) begin
        `uvm_error(this.name,
          $sformatf("The last value doesn't match the protocol AXI: WRITE_REQ=%0d(d) WRITE_REQ_last=%0p(p)",
                    m_count_write_req,
                    i,
                    write_req.m_last ) )
        break;
      end // if
    end // foreach

    // Check that the size correspond to the bus width
    if ( nb_bytes > bus_nbytes ) begin
      `uvm_error(this.name,
        $sformatf("The size field value doesn't match the bus width: WRITE_REQ=%0d(d) WRITE_REQ_SIZE=%0h(h) ; DATA_bus_nbytes=%0d(d)",
                  m_count_write_req,
                  nb_bytes,
                  bus_nbytes ) )
    end

    // Check that the number of bytes exchanged for each flit respect the
    // protocol depending of the start address, the size of the transaction
    // and the number of flit exchanged
    foreach( write_req.m_wstrb[i] ) begin
      int lower_byte_lane, upper_byte_lane ;
      axi_sig_addr_t aligned_addr, address_n ;

      // Checking that the number of bytes exchanged in the flit doesn't
      // exceed the transaction size
      if ( nb_bytes < $countones(write_req.m_wstrb[i]) ) begin
        `uvm_error(this.name,
          $sformatf("The number of bytes exchanged doesn't match the size field value: WRITE_REQ=%0d(d) WRITE_REQ_SIZE=%0h(h) ; WRITE_REQ_WSTRB[flit=%0d]=%0x(x)",
                    m_count_write_req,
                    nb_bytes,
                    i,
                    write_req.m_wstrb[i] ) )
      end // if

      // Using the equation of the specification, section A3.4 of the IHI022H
      // version of the amba axi protocol to check if the position of the
      // exchanged bytes in the write strobe respects the protocol axi
      aligned_addr = int'( write_req.m_addr / nb_bytes ) * nb_bytes ;
      if ( i == 0 ) begin
        address_n       = write_req.m_addr ;
        lower_byte_lane = write_req.m_addr - int'(write_req.m_addr / bus_nbytes ) * bus_nbytes ;
        upper_byte_lane = aligned_addr + ( nb_bytes - 1 ) - int'( write_req.m_addr / bus_nbytes ) * bus_nbytes ;
      end else begin
        address_n       = aligned_addr + i * nb_bytes;
        lower_byte_lane = address_n - int'( address_n / bus_nbytes ) * bus_nbytes;
        upper_byte_lane = lower_byte_lane + nb_bytes - 1 ;
      end
      
      for ( int j = 0 ; j < bus_nbytes ; j++ ) begin
        if ( ( ( j > upper_byte_lane ) || ( j < lower_byte_lane ) ) && ( write_req.m_wstrb[i][j] == 1'b1 ) )
          `uvm_error(this.name,
            $sformatf("The write strobe enabled are not aligned on the address: WRITE_REQ=%0d(d) WRITE_REQ_ADDR=%0h(h) ; WRITE_REQ_NB_BYTES=%0h(h) ; WRITE_REQ_WSTRB[flit=%0d]=%0x(x)",
                      m_count_write_req,
                      write_req.m_addr,
                      nb_bytes,
                      i,
                      write_req.m_wstrb[i] ) )
      end
    end // foreach

    // Check if the cache value corresponds to a mem_type
    if ( get_mem_type( AXI_WRITE_REQ, write_req.m_cache ) == CACHE_RESERVED )
        `uvm_error(this.name,
          $sformatf("The cache value doesn't corresponds to anything in the memory type encoding: WRITE_REQ=%0d(d) WRITE_REQ_CACHE=%0h(h) ;",
                    m_count_write_req,
                    write_req.m_cache ) )

  endtask: check_write_req

  // -----------------------------------------------------------------------
  // Task check_read_req
  //
  // Compare the corresponding read request from the source to the read
  // request received on the dest interface
  // -----------------------------------------------------------------------
  task check_read_req ( 
    axi_superset_txn_c  read_req
  );

    // If the unique id is configured in the agent, and that the ID of the
    // transaction already exist, print an error.
    if ( m_agent_config.get_id_management_enable() ) begin
      if ( m_read_txn_db.exists(read_req.m_id) )
        `uvm_error(this.name,
          $sformatf("The agent was configured to generate only unique IDs, and the ID=%0h(h) is currently also used by another read transaction", read_req.m_id) )
    end

    // Check that the size correspond to the bus width
    if ( 2**read_req.m_size > m_agent_config.get_txn_config().get_data_width()/8 ) begin
      `uvm_error(this.name,
        $sformatf("The size field value doesn't match the bus width: READ_REQ=%0d(d) READ_REQ_SIZE=%0h(h) ; DATA_bus_nbytes=%0d(d)",
                  m_count_read_req,
                  read_req.m_size,
                  m_agent_config.get_txn_config().get_data_width() ) )
    end

    // Check if the cache value corresponds to a mem_type
    if ( get_mem_type( AXI_READ_REQ, read_req.m_cache ) == CACHE_RESERVED )
        `uvm_error(this.name,
          $sformatf("The cache value doesn't corresponds to anything in the memory type encoding: READ_REQ=%0d(d) READ_REQ_CACHE=%0h(h) ;",
                    m_count_read_req,
                    read_req.m_cache ) )

  endtask: check_read_req

  // -----------------------------------------------------------------------
  // Task check_write_rsp
  //
  // Compare the corresponding write response from the dest to the write
  // response received on the source interface
  // -----------------------------------------------------------------------
  task check_write_rsp ( 
    axi_superset_txn_c  write_rsp
  );
    axi_superset_txn_c  write_req ;
    
    if ( m_write_txn_db.exists( write_rsp.m_id ) ) begin
      write_req = m_write_txn_db[write_rsp.m_id].pop_back() ;
    end else begin
      `uvm_error(this.name, 
        $sformatf("No corresponding write request found in database m_write_txn_db: ID=%0h(h)", write_req) )
    end

    // Remove the transaction from the transaction associative array
    if ( m_write_txn_db[write_rsp.m_id].size() == 0 )
      m_write_txn_db.delete(write_rsp.m_id);

  endtask: check_write_rsp

  // -----------------------------------------------------------------------
  // Task check_read_rsp
  //
  // Compare the corresponding read response from the dest to the read
  // response received on the source interface
  // -----------------------------------------------------------------------
  task check_read_rsp ( 
    axi_superset_txn_c  read_rsp
  );
    int nb_flits ;
    
    axi_superset_txn_c  read_req ;
    
    if ( m_read_txn_db.exists( read_rsp.m_id ) ) begin
      read_req = m_read_txn_db[read_rsp.m_id].pop_back() ;
    end else begin
      `uvm_error(this.name, 
        $sformatf("No corresponding read request found in database m_read_txn_db: ID=%0h(h)", read_rsp.m_id) )
    end

    // Get the number of flit from the corresponding read transaction
    nb_flits = read_req.m_len + 1 ;

    // Check the number of flit of data
    if ( read_rsp.m_data.size() != nb_flits ) begin
      `uvm_error(this.name,
        $sformatf("Number of flits of data are not matching: READ_RSP=%0d(d) READ_REQ_LEN=%0h(h) ; READ_RSP_DATA=%0p(p)",
                  m_count_read_rsp,
                  read_req.m_len,
                  read_rsp.m_data ) )
    end

    // Check the number of flit of last
    if ( read_rsp.m_last.size() != nb_flits ) begin
      `uvm_error(this.name,
        $sformatf("Number of flits of last are not matching: READ_RSP=%0d(d) READ_REQ_LEN=%0h(h) ; READ_RSP_LAST=%0p(p)",
                  m_count_read_rsp,
                  read_req.m_len,
                  read_rsp.m_last ) )
    end

    // Check that only the last flit of last is tied to 1'b1
    foreach( read_rsp.m_last[i] ) begin
      if ( ( i != read_rsp.m_last.size() - 1 ) ? (read_rsp.m_last[i] == 1) : (read_rsp.m_last[i] == 0 ) ) begin
        `uvm_error(this.name,
          $sformatf("The last value doesn't match the protocol AXI: READ_RSP=%0d(d) READ_RSP_LAST=%0p(p)",
                    m_count_read_rsp,
                    read_rsp.m_last ) )
      end // if
    end // foreach

    // Check the number of flit of resp
    if ( read_rsp.m_resp.size() != nb_flits ) begin
      `uvm_error(this.name,
        $sformatf("Number of flits of resp are not matching: READ_RSP=%0d(d) READ_REQ_LEN=%0h(h) ; READ_RSP_RESP=%0p(p)",
                  m_count_read_rsp,
                  read_req.m_len,
                  read_rsp.m_resp ) )
    end

    // Remove the transaction from the transaction associative array
    if ( m_read_txn_db[read_rsp.m_id].size() == 0 )
      m_read_txn_db.delete(read_rsp.m_id);

  endtask: check_read_rsp

  // -----------------------------------------------------------------------
  // Report phase
  // -----------------------------------------------------------------------
  virtual function void report_phase(uvm_phase phase);
        // -----------------------------------------------------------------------
        // Check that the transaction counters are coherent
        // -----------------------------------------------------------------------
        if (m_count_exp_read_rsp != m_count_read_rsp)
            `uvm_error(this.name, "Number of expected read responses is not equal to the number of received read responses")
        if (m_count_exp_write_rsp != m_count_write_rsp)
            `uvm_error(this.name, "Number of expected write responses is not equal to the number of received write responses")

        // -----------------------------------------------------------------------
        // Check that the dynamic  arrays are empty at the end of the
        // simulation
        // -----------------------------------------------------------------------
        if ( m_read_txn_db.num() != 0  )
            `uvm_error(this.name, "The read response dynamic  array is not empty")
        if ( m_write_txn_db.num() != 0 )
            `uvm_error(this.name, "The write response dynamic  array is not empty")
        
  endfunction: report_phase

endclass: axi_superset_protocol_checker_c
