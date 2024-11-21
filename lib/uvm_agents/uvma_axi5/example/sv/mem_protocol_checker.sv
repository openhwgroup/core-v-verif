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
//  Description : Collect request/response from the monitor and the response
//                model and compare them to verify the uvma_axi protocol
//
// ----------------------------------------------------------------------------

// -----------------------------------------------------------------------
// Class uvma_axi_protocol_checker_c
// -----------------------------------------------------------------------
class uvma_axi_memory_data_checker_c extends uvm_scoreboard;

  `uvm_component_utils(uvma_axi_memory_data_checker_c)

  protected string name                ;
  event            reset_asserted      ;
  event            reset_deasserted    ;

  // -----------------------------------------------------------------------
  // Analysis Ports
  // -----------------------------------------------------------------------
  uvm_tlm_analysis_fifo #(uvma_axi_transaction_c) m_write_req_packets_collected ;
  uvm_tlm_analysis_fifo #(uvma_axi_transaction_c) m_read_req_packets_collected  ;
  uvm_tlm_analysis_fifo #(uvma_axi_transaction_c) m_write_rsp_packets_collected ;
  uvm_tlm_analysis_fifo #(uvma_axi_transaction_c) m_read_rsp_packets_collected  ;

  // -----------------------------------------------------------------------
  // Data Structures to store uvma_axi/chi req/rsp
  // -----------------------------------------------------------------------
  // Data structure to store analysis port outputs
  uvma_axi_transaction_c m_wreq_packet ;
  uvma_axi_transaction_c m_rreq_packet ;
  uvma_axi_transaction_c m_wrsp_packet ;
  uvma_axi_transaction_c m_rrsp_packet ;

  // Associative array to store transaction
  uvma_axi_transaction_c m_read_txn_db[uvma_axi_sig_id_t][$]  ;
  uvma_axi_transaction_c m_write_txn_db[uvma_axi_sig_id_t][$] ;

  logic [7:0] m_mem_array[uvma_axi_sig_addr_t] ;

  // -----------------------------------------------------------------------
  // Counter for the number of request/response
  // -----------------------------------------------------------------------
  protected int m_count_read_req  ;
  protected int m_count_write_req ;
  protected int m_count_read_rsp  ;
  protected int m_count_write_rsp ;

  uvma_axi_cfg_c         agent_cfg ;

  // ------------------------------------------------------------------------
  // Constructor
  // ------------------------------------------------------------------------
  function new(string name, uvm_component parent);
        super.new(name, parent);
        this.name = name;
  endfunction: new

  // -----------------------------------------------------------------------
  // Build Phase
  // -----------------------------------------------------------------------
  function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      // Initialisation of the uvm_tlm_analysis_fifo for uvma_axi interface
      m_write_req_packets_collected = new("m_write_req_packets_collected" , this) ;
      m_read_req_packets_collected  = new("m_read_req_packets_collected"  , this) ;
      m_write_rsp_packets_collected = new("m_write_rsp_packets_collected" , this) ;
      m_read_rsp_packets_collected  = new("m_read_rsp_packets_collected"  , this) ;

      // Initialisation of the counters of the testbench
      // uvma_axi transactions counters
      m_count_read_req  = 0 ;
      m_count_write_req = 0 ;
      m_count_read_rsp  = 0 ;
      m_count_write_rsp = 0 ;

      `uvm_info(this.name, "Build stage complete.", UVM_LOW)
  endfunction: build_phase
  
  // -----------------------------------------------------------------------
  // Functions set/get
  // -----------------------------------------------------------------------
  // AGENT CONFIGURATION
  function uvma_axi_cfg_c get_agent_config();
    get_agent_config = agent_cfg  ;
  endfunction : get_agent_config

  function void set_agent_config( uvma_axi_cfg_c config_i );
    `uvm_info(this.name,
              $sformatf("Setting the agent configuraiton CFG=%0s", config_i.convert2string() ),
              UVM_DEBUG)
    agent_cfg = config_i ;
  endfunction: set_agent_config

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

    // Flushing the uvma_axi uvm_tlm_analysis_fifo
    m_write_req_packets_collected.flush() ;
    m_read_req_packets_collected.flush()  ;
    m_write_rsp_packets_collected.flush() ;
    m_read_rsp_packets_collected.flush()  ;

    // Reset of the associative arrays
    m_read_txn_db.delete()  ;
    m_write_txn_db.delete() ;

    // Initialisation of the counters of the testbench
    // uvma_axi transactions counters
    m_count_read_req  = 0 ;
    m_count_write_req = 0 ;
    m_count_read_rsp  = 0 ;
    m_count_write_rsp = 0 ;

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
    uvma_axi_transaction_c  write_req;

    forever begin
        // Wait to receive a packet from the analysis port and store it in the
        // m_uvma_axi_req_packet data structure
        m_write_req_packets_collected.get(m_wreq_packet);

        // Creating a new object to store the input packet data structure,
        // before storing it inside a queue
        write_req = new;
        $cast(write_req, m_wreq_packet.clone());
        write_req.set_config(agent_cfg.get_txn_config());
        write_req.post_randomize() ;

        // Register the uvma_axi transaction in an associative array
        m_write_txn_db[write_req.m_id].push_front(write_req);

        // Increment write request counter
        m_count_write_req++;

    end // forever
  endtask: collect_write_req

  // -----------------------------------------------------------------------
  // Task collect_read_req
  //
  // Collect input read requests from the axi interface
  // -----------------------------------------------------------------------
  virtual task collect_read_req( uvm_phase phase );
    string ids_s;
    uvma_axi_transaction_c  read_req;

    forever begin
        // Wait to receive a packet from the analysis port and store it in the
        // m_req_packet data structure
        m_read_req_packets_collected.get(m_rreq_packet);

        // Creating a new object to store the input packet data structure,
        // before storing it inside a queue
        read_req = new;
        $cast(read_req, m_rreq_packet.clone());
        read_req.set_config(agent_cfg.get_txn_config());
        read_req.post_randomize() ;

        // Register the axi transaction in an associative array
        m_read_txn_db[read_req.m_id].push_front(read_req);

        // Increment read request counter
        m_count_read_req++;

    end // forever
  endtask: collect_read_req

  // -----------------------------------------------------------------------
  // Task collect_write_rsp
  //
  // Collect input write response from the axi interface
  // -----------------------------------------------------------------------
  virtual task collect_write_rsp( uvm_phase phase );
    uvma_axi_transaction_c  write_req;
    uvma_axi_transaction_c  write_rsp;

    forever begin
        // Wait to receive a packet from the analysis port and store it in the
        // m_rsp_packet data structure
        m_write_rsp_packets_collected.get( m_wrsp_packet );

        // Creating a new object to store the response packet information,
        // before storing it inside a queue
        write_rsp = new;
        $cast( write_rsp, m_wrsp_packet.clone() );

        if ( m_write_txn_db.exists( write_rsp.m_id ) ) begin
          write_req = m_write_txn_db[write_rsp.m_id].pop_back() ;
        end else begin
          `uvm_error(this.name, 
            $sformatf("No corresponding read request found in database m_write_txn_db: ID=%0h(h)", write_rsp.m_id) )
        end
        `uvm_info(this.name,
                  $sformatf("WRITE_REQ=%0s", write_req.convert2string() ),
                  UVM_NONE)
        `uvm_info(this.name,
                  $sformatf("WRITE_RSP=%0s", write_rsp.convert2string() ),
                  UVM_NONE)

        // Verification of the axi write response
        if ( write_rsp.m_resp[0] == OKAY ) begin
          write_mem ( write_req );
        end else begin
          `uvm_error(this.name, 
            $sformatf("Since the memory sent back an error for the write transaction ID=%0h(h), the memory is not updated with the corresponding data", write_rsp.m_id) )
        end

        // Increment the write rsp counter
        m_count_write_rsp++;

        // Remove the transaction from the transaction associative array
        if ( m_write_txn_db[write_rsp.m_id].size() == 0 )
          m_write_txn_db.delete(write_rsp.m_id);
    end
  endtask : collect_write_rsp

  // -----------------------------------------------------------------------
  // Task collect_read_rsp
  //
  // Collect input read response from the axi interface
  // -----------------------------------------------------------------------
  virtual task collect_read_rsp( uvm_phase phase );
    uvma_axi_transaction_c  read_rsp;

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
        read_mem ( read_rsp );

        // Increment the read rsp counter
        m_count_read_rsp++;

        // Remove the transaction from the transaction associative array
        if ( m_read_txn_db[read_rsp.m_id].size() == 0 )
          m_read_txn_db.delete(read_rsp.m_id);

    end
  endtask : collect_read_rsp


  // -----------------------------------------------------------------------
  // -----------------------------------------------------------------------
  //
  // MEMORY TASKS
  //
  // -----------------------------------------------------------------------
  // -----------------------------------------------------------------------

  // -----------------------------------------------------------------------
  // Task check_write_req
  //
  // Compare the corresponding write request from the source to the write
  // request received on the dest interface
  // -----------------------------------------------------------------------
  task write_mem ( 
    uvma_axi_transaction_c  write_req
  );
    int nb_flits   ; // Number of flits of data of the transaction
    int bus_nbytes ; // Number of bytes of the data bus
    int nb_bytes   ; // Maximum number of bytes of the transaction for each flit of data

    // Variables used for the byte lane computing
    uvma_axi_sig_addr_t aligned_addr, address_n ;
    int flag_wrap  ;

    // Computing some values necessary for the verification of the transaction
    nb_flits   = write_req.m_len + 1 ;
    bus_nbytes = agent_cfg.get_txn_config().get_data_width()/8 ;
    nb_bytes   = 2**write_req.m_size ;

    foreach( write_req.m_wstrb[i] ) begin

      aligned_addr  = uvma_axi_sig_addr_t'( write_req.m_flit_addr[i] / bus_nbytes ) * bus_nbytes ;
      address_n = aligned_addr;
      for ( int j = 0 ; j < bus_nbytes ; j++ ) begin
        if ( write_req.m_wstrb[i][j] ) begin
          m_mem_array[address_n] = write_req.m_data[i][8*j +: 8]; 
        end
        address_n += 1;
      end
    end // foreach

  endtask: write_mem

  // -----------------------------------------------------------------------
  // Task check_read_rsp
  //
  // Compare the corresponding read response from the dest to the read
  // response received on the source interface
  // -----------------------------------------------------------------------
  task read_mem ( 
    uvma_axi_transaction_c  read_rsp
  );
    uvma_axi_transaction_c  read_req ;

    int nb_flits   ; // Number of flits of data of the transaction
    int bus_nbytes ; // Number of bytes of the data bus
    int nb_bytes   ; // Maximum number of bytes of the transaction for each flit of data

    // Variables used for the byte lane computing
    uvma_axi_sig_addr_t aligned_addr, address_n ;
    uvma_axi_sig_addr_t wrap_boundary ;
    int flag_wrap  ;

    if ( m_read_txn_db.exists( read_rsp.m_id ) ) begin
      read_req = m_read_txn_db[read_rsp.m_id].pop_back() ;
    end else begin
      `uvm_error(this.name, 
        $sformatf("No corresponding read request found in database m_read_txn_db: ID=%0h(h)", read_rsp.m_id) )
    end

    `uvm_info(this.name,
              $sformatf("READ_REQ=%0s", read_req.convert2string() ),
              UVM_NONE)
    `uvm_info(this.name,
              $sformatf("READ_RSP=%0s", read_rsp.convert2string() ),
              UVM_NONE)
    // Computing some values necessary for the verification of the transaction
    nb_flits   = read_req.m_len + 1 ;
    bus_nbytes = agent_cfg.get_txn_config().get_data_width()/8 ;
    nb_bytes   = 2**read_req.m_size ;

    // Check that the number of bytes exchanged for each flit respect the
    // protocol depending of the start address, the size of the transaction
    // and the number of flit exchanged
    wrap_boundary = uvma_axi_sig_addr_t'( read_req.m_addr / ( nb_bytes * nb_flits ) ) * ( nb_bytes * nb_flits ) ;
    flag_wrap = 0 ;
    address_n = 0 ;
    foreach( read_rsp.m_data[i] ) begin
      uvma_axi_sig_data_t read_data_flit;

      // Using the equation of the specification, section A3.4 of the IHI022H
      // version of the amba axi protocol to check if the position of the
      // exchanged bytes in the write strobe respects the protocol axi
      // Equation from the specification
      if ( read_req.m_burst != FIXED ) begin // Burst mode INCR or WRAP

        // Computing the address and byte lane for the first flit of the
        // transaction
        if ( i == 0 ) begin
          address_n       = read_req.m_addr ;
        end else begin
          // Computing the flit address depending of the burst mode, and
          // if the transaction has wrapped or not.
          if ( ( read_req.m_burst == WRAP ) && flag_wrap ) begin // If burst mode is WRAP and the transaction has already wrapped
            address_n = read_req.m_addr + ( i * nb_bytes ) - ( nb_bytes * nb_flits ) ;
          end else begin // For burst mode INCR, and WRAP if the transaction has not wrapped
            address_n = aligned_addr + i * nb_bytes;
          end

        end
        aligned_addr  = uvma_axi_sig_addr_t'( read_req.m_addr / nb_bytes ) * nb_bytes ;

        // Checking for the burst mode WRAP if the address has wrapped
        if ( ( address_n == ( wrap_boundary + ( nb_bytes * nb_flits ) ) ) &&
             ( read_req.m_burst == WRAP ) ) begin
          flag_wrap = 1 ;
          address_n = wrap_boundary ;
        end // if wrap

      end else begin // Burst mode FIXED
        // Constant addr and byte lane for all flits of the transaction
        address_n = read_req.m_addr ;
      end // if FIXED
      
      address_n = uvma_axi_sig_addr_t'( address_n / bus_nbytes ) * bus_nbytes ;
      read_data_flit = 'h0;
      for ( int j = 0 ; j < bus_nbytes ; j++ ) begin
        if ( m_mem_array.exists( address_n) ) begin // This memory bytes was already accessed by a previous write
          read_data_flit[8*j +: 8] = m_mem_array[address_n] ;
        end else begin
          read_data_flit[8*j +: 8] = 8'h0 ;
        end
        address_n += 1;
      end

      if ( read_data_flit != read_rsp.m_data[i] ) begin
        `uvm_error(this.name, 
          $sformatf("The data flit are not corresponding: READ_TXN_ID=%0h(h) SB_DATA_FLIT=%0h(h) DUT_DATA_FLIT=%0h(h)", read_rsp.m_id, read_data_flit, read_rsp.m_data[i]) )
      end 
    end // foreach

  endtask: read_mem

  // -----------------------------------------------------------------------
  // Report phase
  // -----------------------------------------------------------------------
  virtual function void report_phase(uvm_phase phase);
        // -----------------------------------------------------------------------
        // Check that the dynamic  arrays are empty at the end of the
        // simulation
        // -----------------------------------------------------------------------
        if ( m_read_txn_db.num() != 0  )
            `uvm_error(this.name, "The read response dynamic  array is not empty")
        if ( m_write_txn_db.num() != 0 )
            `uvm_error(this.name, "The write response dynamic  array is not empty")
        
  endfunction: report_phase

endclass: uvma_axi_memory_data_checker_c
