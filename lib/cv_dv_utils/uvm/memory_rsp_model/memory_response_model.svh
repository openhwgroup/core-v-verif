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
// ----------------------------------------------------------------------------
//  Description : Receive a request from memory and schedule a response
//                set_enable_rd_output(0) => read response is blocked
//                set_enable_wr_output(0) => write response is blocked
//
// ----------------------------------------------------------------------------


// ----------------------------------------------------------------------------
// Memroy transaction: to be stored in a rd/wr rsp queue
// ----------------------------------------------------------------------------
class memory_txn #(int w_addr = 64, int w_data = 512, int w_id = 16) extends uvm_object;


    bit [w_id -1: 0]      id;
    bit [w_addr -1: 0]    addr;
    bit [w_data -1: 0]    data;
    bit [w_data/8 -1: 0]  strb;
    bit                   err;
    bit                   ex_fail; //exclusive_fail 
   
    mem_command_t         cmd;
    mem_atomic_t          atop;
    //////////////////////////////////////////////////////
    //Configuration Parameters
    //To be driven by the driver 
    /////////////////////////////////////////////////////
    int                    req_arrival_time;; 
    int                    global_transmit_time; //delay in clock cycle

    int                    req_ts, resp_ts;

     // ------------------------------------------------------------------------
     // Utilities for the variables
     // ------------------------------------------------------------------------
    `uvm_object_param_utils_begin( memory_txn#(w_addr, w_data, w_id) )
        `uvm_field_int( req_arrival_time,                 UVM_DEFAULT )
        `uvm_field_int( global_transmit_time,             UVM_DEFAULT )
    `uvm_object_utils_end


    function new( string name ="" );
        super.new( name );
    endfunction
 
   // ===========================================================================
   // convert2string()
   // ===========================================================================
   virtual function string convert2string( );
      string s ;
      string prefix;

      prefix = { get_full_name(), " :: MEM TXN " } ;

      s = { s, $sformatf("ID         = %0x(x)",  id      ),  " " };
      s = { s, $sformatf("ADDR       = %0x(x)",  addr    ),  " " };
      s = { s, $sformatf("DATA       = %0x(x)",  data    ),  " " };
      s = { s, $sformatf("ERR        = %0x(x)",  err     ),  " " };
      s = { s, $sformatf("EX ERR     = %0x(x)",  ex_fail  ),  " " };
      return s;  
   endfunction
endclass : memory_txn


// -----------------------------------------------------------
// Internal Memory of MRM
// -----------------------------------------------------------
class memory_c#(int w_data = 512) extends uvm_object;

    rand bit [w_data -1: 0]   data;

    // -------------------------------------------------------
    // Byte Granularity Indication of data corruption 
    // -------------------------------------------------------
    bit      [w_data/8 -1: 0] error;
 
    // -------------------------------------------------------
    // Used for exclusive acces
    // Keeps the information of reservation in case LDEX 
    // -------------------------------------------------------
    bit      [w_data/8 -1: 0] ldex_bytes[integer]; //src_id
    // ------------------------------------------------------------------------
    // Constructor
    // ------------------------------------------------------------------------
    function new( string name = "memory_c" );
        super.new(name);
        error = 0; 
    endfunction: new

endclass: memory_c

// -----------------------------------------------------------
// This Class is used to configure the delay between responses
// Every time a request is recieved, a new response is generated with a random
// delay 
// The delay depends on the response mode 
// NORMAL      = Many small delays and few large delays 
// ZERO_DELAY  = No delays 
// FIXED_DELAY = Fixed Delay defined by user 
// -----------------------------------------------------------
class mem_txn_rsp_delay extends uvm_object;
   // -------------------------------------------------------
   //delay to be added for each response in number of cycles   
   // -------------------------------------------------------
   rand int            rsp_delay;     

   // -------------------------------------------------------
   // rsp cfg, get from env 
   // -------------------------------------------------------
   memory_rsp_cfg       m_rsp_cfg; 

    // ------------------------------------------------------------------------
    // Utilities for the variables
    // ------------------------------------------------------------------------
   `uvm_object_utils_begin( mem_txn_rsp_delay )
       `uvm_field_int( rsp_delay,                        UVM_DEFAULT | UVM_UNSIGNED)
   `uvm_object_utils_end

    function new( string name ="" );
        super.new( name );
    endfunction



   //================================================================================
   //Constraint to generate respones delay 
   constraint rsp_delay_dist_c {           
      m_rsp_cfg.rsp_mode == NORMAL_RSP -> {
        rsp_delay dist 
                       {[0:10]    := 45,
                        [10:50]   := 45,         
                        [50:100]  := 8,
                        [100:200] := 2 }; // Typical delay of typical DRAM 
      }
      m_rsp_cfg.rsp_mode == ZERO_DELAY_RSP -> {
        rsp_delay == 0; 
      }
      m_rsp_cfg.rsp_mode == FIXED_DELAY_RSP -> {
        rsp_delay    == m_rsp_cfg.inter_data_cycle_fixed_delay; 
        rsp_delay    == m_rsp_cfg.inter_data_cycle_fixed_delay; 
      }
   };   

endclass: mem_txn_rsp_delay


// ----------------------------------------------------------------------------------------------
// Memory Response Model 
// Parameters 
// w_addr = address width 
// w_data = data width 
// w_id   = id width 
// ----------------------------------------------------------------------------------------------
class memory_response_model#(int w_addr = 64, int w_data = 512, int w_id = 16)  extends uvm_agent;
    
   //================================================================================
   //Variable declaration 
   //================================================================================
   `uvm_component_param_utils (memory_response_model#(w_addr, w_data, w_id) )

   // ------------------------------------------ 
   // New Entry to resposne queues 
   // ------------------------------------------ 
   mem_txn_rsp_delay       m_rsp_delay;
   
   // ------------------------------------------ 
   // Global Counter 
   // ------------------------------------------ 
   int                    global_cycle_count;

   // ------------------------------------
   // rsp cfg, get from env
   // ------------------------------------
   memory_rsp_cfg         m_rsp_cfg; 
   
   // -------------------------------------------------------
   // queues of response arranged in an order defined by user  
   // -------------------------------------------------------
   memory_txn#(w_addr, w_data, w_id)      rd_rsp_queue[$];   
   memory_txn#(w_addr, w_data, w_id)      wr_rsp_queue[$];   

   // -------------------------------------------------------
   // queue to check LDEX/STEX reservation status  
   // -------------------------------------------------------
   memory_txn#(w_addr, w_data, w_id)      amo_reservation_queue[$];   

   // ------------------------------------
   // Memory Shadow
   // ------------------------------------
   memory_c#(w_data)        m_memory[bit [w_addr -1: 0]];
   
   // ----------------------------------------------------
   // starts sending rsp only when these fields is enabled
   // ----------------------------------------------------
   protected bit       enable_rd_output; 
   protected bit       enable_wr_output; 

   event               reset_asserted;
   event               reset_deasserted;

   // ----------------------------------------
   // rd rsp count is fixed by the user
   // We can insert only that number of errors
   // ----------------------------------------
   protected int       rd_rsp_error_counter; 
   protected int       wr_rsp_error_counter; 
   protected int       wr_rsp_exclusive_fail_counter; 
   protected int       amo_rd_rsp_error_counter; 
   protected int       amo_wr_rsp_error_counter; 

   // ----------------------------------------
   // Handle to mem response interface
   // ----------------------------------------
   virtual memory_response_if#( w_addr, w_data, w_id )         m_mem_rsp_vif; 

   
    // -----------------------------------------------------------------------
    // Analysis Ports
    // -----------------------------------------------------------------------
    uvm_analysis_port #(memory_txn#(w_addr, w_data, w_id)) ap_mem_req;
    uvm_analysis_port #(memory_txn#(w_addr, w_data, w_id)) ap_mem_rd_rsp;
    uvm_analysis_port #(memory_txn#(w_addr, w_data, w_id)) ap_mem_wr_rsp;

   //================================================================================



   function new( string name = "memory_response_model", uvm_component parent = null);
       super.new( name, parent);

       // By default enable to rsp
       enable_wr_output = 1;
       enable_rd_output = 1;

       ap_mem_req      = new("ap_mem_req", this);
       ap_mem_rd_rsp   = new("ap_mem_rd_rsp", this);
       ap_mem_wr_rsp   = new("ap_mem_wr_rsp", this);

   endfunction


   //================================================================================
   function void build_phase(uvm_phase phase);
       string s_name;

        if(!uvm_config_db #( virtual memory_response_if #( w_addr, w_data, w_id ) )::get(this, "", get_name(), m_mem_rsp_vif )) begin
            `uvm_fatal("BUILD_PHASE", $sformatf("Unable to get m_mem_rsp_vif for %s from configuration database", get_name() ) );
        end
   endfunction : build_phase

   //================================================================================
   // Emit an event when the reset is asserted  
   //================================================================================
   virtual task pre_reset_phase(uvm_phase phase);
      if (m_rsp_cfg.m_enable) begin
          `uvm_info("RSP MODEL", "ENTERS PRE RESET PHASE", UVM_LOW);
          -> reset_asserted;
      end // if
   endtask : pre_reset_phase

   //================================================================================
   // Initialize global counter in reset phase 
   // Empty queues in the reset phase 
   //================================================================================
   virtual task reset_phase(uvm_phase phase);
      if (m_rsp_cfg.m_enable) begin
         m_memory.delete();    
         rd_rsp_queue.delete();   
         wr_rsp_queue.delete();
         amo_reservation_queue.delete();

         global_cycle_count = 0;
         rd_rsp_error_counter = 0;
         wr_rsp_error_counter = 0;
         m_mem_rsp_vif.rd_res_valid   = 1'b0; 
         m_mem_rsp_vif.wr_res_valid   = 1'b0;
         wr_rsp_exclusive_fail_counter = 0; 
         amo_rd_rsp_error_counter      = 0; 
         amo_wr_rsp_error_counter      = 0;

         `uvm_info("RSP MODEL", "OUT OF RESET PHASE", UVM_LOW);
      end // if
   endtask : reset_phase
   
    virtual task post_configure_phase( uvm_phase phase);
       if (m_rsp_cfg.m_enable) begin

        super.post_configure_phase(phase);

        `uvm_info("MEMORY RESPONSE MODEL", $sformatf("Response Order :%s", m_rsp_cfg.rsp_order), UVM_LOW);
        -> reset_deasserted;

        // Back Pressure variable 
        m_mem_rsp_vif.req_ready_bp = m_rsp_cfg.m_bp;
       end // if

    endtask


   // --------------------------------------------------------------------------------
   // RUN PHASE 
   // --------------------------------------------------------------------------------
   virtual task run_phase(uvm_phase phase);

      m_mem_rsp_vif.rd_res_valid   = 1'b0; 
      m_mem_rsp_vif.wr_res_valid   = 1'b0; 
      if (m_rsp_cfg.m_enable) begin
         
         forever begin
           @(reset_deasserted);
           fork
              global_cycle_counter();
 //             get_ready_bp();
              schedule_and_drive_rd_response(); 
              schedule_and_drive_wr_response(); 
              populate_wr_rsp_queue();
              populate_rd_rsp_queue();
              populate_amo_rd_wr_rsp_queue();
            join_none
           @(reset_asserted);
           disable fork;
         end //forever 
      end // if

   endtask : run_phase

   //================================================================================
   // FIXE ME: this global counter should be in common utilities
   // This is global cycle counter 
   //================================================================================
   task global_cycle_counter();
      forever begin
        m_mem_rsp_vif.wait_n_clocks(1);
        global_cycle_count++;
      end //forever 
   endtask : global_cycle_counter

   //================================================================================
   // Check responses delay against the global counter
   // As soon as the global transmit time >= global cycle count
   // send READ response 
   //================================================================================
   task schedule_and_drive_rd_response(); 
     int                                             q_index[$];
     memory_txn#(w_addr, w_data, w_id)        m_memory_rsp;
    
     forever begin
    
      // -----------------------------------------------------
      // user can use an API to set/unset enable_rd_output
      // ----------------------------------------------------
      // -----------------------------------------------------
      // If rsp ready is not used, 
      // drive the response as soon as it is available
      // else wait for ready 
      // -----------------------------------------------------
      wait((enable_rd_output == 1) && (rd_rsp_queue.size() > 0));
      
      wait ((rd_rsp_queue[0].global_transmit_time <= global_cycle_count));

      m_memory_rsp                 = rd_rsp_queue.pop_front();
      m_memory_rsp.resp_ts         = global_cycle_count;
      m_memory_rsp.req_ts          = m_memory_rsp.req_arrival_time;
      m_mem_rsp_vif.rd_res_id      <= m_memory_rsp.id;
      m_mem_rsp_vif.rd_res_err     <= m_memory_rsp.err;    
      m_mem_rsp_vif.rd_res_data    <= m_memory_rsp.data;
      m_mem_rsp_vif.rd_res_addr    <= m_memory_rsp.addr;    
      m_mem_rsp_vif.rd_res_ex_fail <= m_memory_rsp.err;
      m_mem_rsp_vif.rd_res_valid   <= 1'b1; 
      `uvm_info( "MEMORY RESPONSE MODEL", $sformatf("READ RSP : %s ", m_memory_rsp.convert2string()), UVM_LOW );

      // This agent can work either with or without a ready valid protocol 
`ifndef DV_UTILS_MRM_READ_RSP_READY
      m_mem_rsp_vif.wait_n_clocks(1);
      ap_mem_rd_rsp.write(m_memory_rsp);
      m_mem_rsp_vif.rd_res_valid   = 1'b0; 

`else
      // Wait for the request to be consumed
      do begin
        @(posedge m_mem_rsp_vif.clk);
      end while (!m_mem_rsp_vif.rd_res_ready); 
      m_mem_rsp_vif.rd_res_valid   = 1'b0; 
      ap_mem_rd_rsp.write(m_memory_rsp);
`endif

     end //forever 
   endtask : schedule_and_drive_rd_response

   //================================================================================
   // Check responses delay against the global counter
   // As soon as the global transmit time >= global cycle count
   // send WRITE response 
   //================================================================================
   task schedule_and_drive_wr_response(); 

     int                   q_index[$];
     memory_txn#(w_addr, w_data, w_id)        m_memory_rsp;
    
     forever begin

       // -----------------------------------------------------
       // user can use an API to set/unset enable_wr_output
       // ----------------------------------------------------

       // -----------------------------------------------------
       // If rsp ready is not used, 
       // drive the response as soon as it is available
       // else wait for ready 
       // -----------------------------------------------------
      wait((enable_wr_output == 1) && (wr_rsp_queue.size() > 0));
      
      wait (wr_rsp_queue[0].global_transmit_time <= global_cycle_count);

       m_memory_rsp                 = wr_rsp_queue.pop_front();
       m_memory_rsp.resp_ts         = global_cycle_count;
       m_memory_rsp.req_ts          = m_memory_rsp.req_arrival_time;
       m_mem_rsp_vif.wr_res_id      <= m_memory_rsp.id;
       m_mem_rsp_vif.wr_res_err     <= m_memory_rsp.err;
       m_mem_rsp_vif.wr_res_ex_fail <= m_memory_rsp.ex_fail;
       m_mem_rsp_vif.wr_res_addr    <= m_memory_rsp.addr;    
       m_mem_rsp_vif.wr_res_valid   <= 1'b1;

       `uvm_info( "MEMORY RESPONSE MODEL", $sformatf("WRITE RSP : %s ", m_memory_rsp.convert2string()), UVM_LOW );
`ifndef DV_UTILS_MRM_WRITE_RSP_READY
       m_mem_rsp_vif.wait_n_clocks(1);
       m_mem_rsp_vif.wr_res_valid   <= 1'b0;
       ap_mem_wr_rsp.write(m_memory_rsp);


`else
       // Wait for the request to be consumed
       do begin
         @(posedge m_mem_rsp_vif.clk);
       end while (!m_mem_rsp_vif.wr_res_ready); 
       ap_mem_wr_rsp.write(m_memory_rsp);
       m_mem_rsp_vif.wr_res_valid   <= 1'b0; 
`endif
      end //forever 
   endtask : schedule_and_drive_wr_response

   //--------------------------------------------------------------
   // In this task:
   // -> A new read request is recieved 
   // -> A new read response is generated 
   // ---> Read Response delay is generated (IN ORDER or OUT OF ORDER ) 
   // -> If it is a miss a new node with random data is added 
   //---------------------------------------------------------------
   task populate_rd_rsp_queue();

       int                     q_index[$];
       int                     q_index1[$];
       bit [w_addr -1:0]       req_addr; 
       bit [w_data -1:0]       new_data;
       int                     offset;          
       memory_txn#(w_addr, w_data, w_id)       new_rd_rsp_entry;     // contains addr and intruction
       // -----------------------------------------
       // New node to m_memory list 
       // -----------------------------------------
       memory_c#(w_data)                      new_node;     // contains addr and intruction
       

       forever begin
         m_mem_rsp_vif.wait_n_clocks(1);

         
         if(m_mem_rsp_vif.req_valid & m_mem_rsp_vif.req_ready & m_mem_rsp_vif.req_wrn & !m_mem_rsp_vif.req_amo) begin
 
          // --------------------------------------------------
          // The addresses are aligned according to the size of w_data 
          // get alined addr and offset according to the data width 
          // --------------------------------------------------
          req_addr    = m_mem_rsp_vif.req_addr;
          offset      = req_addr[$clog2(w_data/8) -1: 0];
          req_addr[$clog2(w_data/8) -1: 0] = 'h0;


          new_rd_rsp_entry        = new();

          // --------------------------------------------------
          // Check if DATA already exists in the memory
          // Else create a new memory mode 
          // --------------------------------------------------
          if(!m_memory.exists(req_addr))  begin

            new_node   = new();
            if(!new_node.randomize())  `uvm_fatal( "RSP_DELAY", "Response delay randomization failed" );
            m_memory[req_addr] = new_node;

          end
          
          new_rd_rsp_entry.data     = m_memory[req_addr].data;
          new_rd_rsp_entry.id       = m_mem_rsp_vif.req_id;

          // ---------------------------------------------------
          // IF error flag is on
          // --> time to time send an error response
          // --> 1% error transaction until confing num_rd_errors 
          // --------------------------------------------------
          if(m_rsp_cfg.insert_rd_error) begin
             if(rd_rsp_error_counter < m_rsp_cfg.num_rd_errors) begin
                new_rd_rsp_entry.err     = ($urandom_range(0, 100) == 50) ? 1: 0 ;
                if(new_rd_rsp_entry.err)  rd_rsp_error_counter++;
            end
          end

           // --------------------------------------------------
           // Populate Rsp Object
           // --------------------------------------------------
           new_rd_rsp_entry.addr             = m_mem_rsp_vif.req_addr; 
           new_rd_rsp_entry.req_arrival_time = global_cycle_count;

           // --------------------------------------------------------
           // Generate new response delay for the incoming transaction 
           // --------------------------------------------------------
           new_rd_rsp_entry.global_transmit_time     = generate_rsp_delay("READ");
           `uvm_info( "MEMORY RESPONSE MODEL", $sformatf("READ REQ : %0s", new_rd_rsp_entry.convert2string() ), UVM_LOW );

           // --------------------------------------------------
           //Add new rsp at appropriate place 
           // --------------------------------------------------
           q_index1             = rd_rsp_queue.find_last_index(rsp) with (rsp.id  == m_mem_rsp_vif.req_id);
           
           // --------------------------------------------------
           // IF ID already exists in the queue make it inorder response
           // --------------------------------------------------
           if(q_index1.size() > 0) begin

             rd_rsp_queue.insert(int'(q_index1[0]) + 1, new_rd_rsp_entry);
           
           end else begin

             q_index                = rd_rsp_queue.find_first_index(rsp) with (rsp.global_transmit_time > new_rd_rsp_entry.global_transmit_time);
          
             if(q_index.size() == 0) rd_rsp_queue.push_back(new_rd_rsp_entry);
             else                    rd_rsp_queue.insert(int'(q_index[0]), new_rd_rsp_entry);
           
           end
      
           new_rd_rsp_entry.cmd = MEM_READ;
           // FIXME: probably send unsolicited rsp as well 
           ap_mem_req.write(new_rd_rsp_entry);
           // ----------------------------------------------------------
           // Insert an unsolicted rsp once in a while if a flag is set
           // ---------------------------------------------------------
           if(m_rsp_cfg.unsolicited_rsp) begin

             if(($urandom_range(0, 5) == 3)) begin
             
               new_rd_rsp_entry            = new();
               new_rd_rsp_entry.id         = $urandom; 
               new_rd_rsp_entry.cmd        = MEM_READ; 
               new_rd_rsp_entry.global_transmit_time     = 0;
               rd_rsp_queue.push_back(new_rd_rsp_entry);
               `uvm_info( "MEMORY RESPONSE MODEL", $sformatf("UNSOLICITED RSP : %0d", new_rd_rsp_entry.convert2string() ), UVM_MEDIUM );
             
             end

           end

           q_index1.delete();
           q_index.delete();

         end
       end
   endtask: populate_rd_rsp_queue;  
      
   //---------------------------------------------------------------
   // In this task:
   // -> A new write request is recieved 
   // -> A new write response is generated 
   // ---> Write Response delay is generated (IN ORDER or OUT OF ORDER ) 
   // -> If it is a miss a new node with random data is added 
   //---------------------------------------------------------------
   virtual task populate_wr_rsp_queue();

       // -----------------------------------------
       // Index to search the queues
       // -----------------------------------------
       int                         q_index[$];
       int                         q_index1[$];

       // -----------------------------------------
       // New node to m_memory list 
       // -----------------------------------------
       memory_c#(w_data)                      new_node;     // contains addr and intruction

       memory_txn#(w_addr, w_data, w_id)           new_wr_rsp_entry;     
       bit  [w_data/8-1:0]       wr_stb;
       bit  [w_data-1:0]         wr_data;
       bit  [w_addr-1:0]         req_addr;
       int                       offset;
             
       forever begin
         m_mem_rsp_vif.wait_n_clocks(1);

         if((m_mem_rsp_vif.req_valid & m_mem_rsp_vif.req_ready & !m_mem_rsp_vif.req_wrn  & !m_mem_rsp_vif.req_amo)) begin

          // --------------------------------------------
          // Aligne the addr as per the data width 
          // --------------------------------------------
          req_addr    = m_mem_rsp_vif.req_addr;
          offset      = req_addr[$clog2(w_data/8) -1: 0];
          req_addr[$clog2(w_data/8) -1: 0] = 'h0;


           wr_stb  = m_mem_rsp_vif.req_strb;
           wr_data = m_mem_rsp_vif.req_data;


           // ---------------------------------------------------------------
           // Create a new m_memory node if this doesnt exists with a random data
           // ---------------------------------------------------------------
           if(!m_memory.exists(req_addr))  begin 
               
              new_node   = new();
              if(!new_node.randomize())  `uvm_fatal( "RSP_DELAY", "Response delay randomization failed" );
              m_memory[req_addr] = new_node;
           end

           // Update Data 
           foreach(wr_stb[i]) begin
             if(wr_stb[i] == 1'b1) begin
               m_memory[req_addr].data[8*i +: 8]      = wr_data[8*i +: 8];
             end //if
           end //foreach

           // --------------------------------------------------------
           // check if reservation exists(LDEX) for the same bytes accessed by
           // WRITE
           // --> If true, remove the reservation 
           // --------------------------------------------------------
           foreach(m_mem_rsp_vif.req_strb[i]) begin
             if(m_mem_rsp_vif.req_strb[i] == 1) begin
               if(m_memory[req_addr].ldex_bytes.exists(m_mem_rsp_vif.src_id)) begin
                 if( m_memory[req_addr].ldex_bytes[m_mem_rsp_vif.src_id][i] == 1) begin
                   m_memory[req_addr].ldex_bytes.delete(m_mem_rsp_vif.src_id);
                   break;
                 end
               end
             end
           end
           // --------------------------------------------------------
           // Generate new response with delay for the incoming transaction 
           // --------------------------------------------------------
           new_wr_rsp_entry                  = new();
           new_wr_rsp_entry.id               = m_mem_rsp_vif.req_id;
           new_wr_rsp_entry.addr             = m_mem_rsp_vif.req_addr; 
           new_wr_rsp_entry.strb             = m_mem_rsp_vif.req_strb; 
           new_wr_rsp_entry.req_arrival_time = global_cycle_count;
           new_wr_rsp_entry.global_transmit_time     = generate_rsp_delay("WRITE");
           `uvm_info( "MEMORY RESPONSE MODEL", $sformatf("WRITE REQ : %0s", new_wr_rsp_entry.convert2string() ), UVM_LOW );

           // --------------------------------------------------
           //Add new rsp at appropriate place 
           // --------------------------------------------------
           q_index1             = wr_rsp_queue.find_last_index(rsp) with (rsp.id  == m_mem_rsp_vif.req_id);
           
           // --------------------------------------------------
           // IF ID already exists in the queue make it inorder response
           // --------------------------------------------------
           if(q_index1.size() > 0) begin

             wr_rsp_queue.insert(int'(q_index1[0]) + 1, new_wr_rsp_entry);
           
           end else begin

             q_index                = wr_rsp_queue.find_first_index(rsp) with (rsp.global_transmit_time > new_wr_rsp_entry.global_transmit_time);
          
             if(q_index.size() == 0) wr_rsp_queue.push_back(new_wr_rsp_entry);
             else                    wr_rsp_queue.insert(int'(q_index[0]), new_wr_rsp_entry);
           
           end


           q_index.delete();
           q_index1.delete();

           // ---------------------------------------------
           // Insert an error response
           // ---------------------------------------------
           if(m_rsp_cfg.insert_wr_error) begin
              if(wr_rsp_error_counter < m_rsp_cfg.num_wr_errors) begin
                  new_wr_rsp_entry.err     = ($urandom_range(0, 100) == 50) ? 1: 0 ;
              end
              if(new_wr_rsp_entry.err)  wr_rsp_error_counter++;
           end

           new_wr_rsp_entry.cmd = MEM_WRITE;
           ap_mem_req.write(new_wr_rsp_entry);
           // ---------------------------------------------
           // Insert an unsolicted rsp once in a while
           // Only for the higher tracker ids
           // ---------------------------------------------
           if(m_rsp_cfg.unsolicited_rsp) begin

              if(($urandom_range(0, 5) == 3)) begin
           
                new_wr_rsp_entry            = new();
                new_wr_rsp_entry.id         = $urandom; 
                new_wr_rsp_entry.cmd        = MEM_WRITE;
                new_wr_rsp_entry.global_transmit_time     = 0;
                wr_rsp_queue.push_back(new_wr_rsp_entry);
                `uvm_info( "MEMORY RESPONSE MODEL", $sformatf("UNSOLICITED RSP : %0d", new_wr_rsp_entry.convert2string() ), UVM_MEDIUM );
              
              end
           
           end
         end // if 
       end
   endtask: populate_wr_rsp_queue; 
  
   // -----------------------------------------------------------------
   // In the case of AMO : 
   //  ->Two response read and write are expected
   //  -> Except for LDEX/STEX 
   // ----------------------------------------------------------------
   virtual task populate_amo_rd_wr_rsp_queue();

       // -----------------------------------------
       // Index to search the queues
       // -----------------------------------------
       int                         q_index[$];
       int                         q_index1[$];

       // -----------------------------------------
       // New node to m_memory list 
       // -----------------------------------------
       memory_c#(w_data)                      new_node;     // contains addr and intruction

       
       // -----------------------------------------
       // New node to rd and wr response list 
       // -----------------------------------------
       memory_txn#(w_addr, w_data, w_id)       new_wr_rsp_entry;     
       memory_txn#(w_addr, w_data, w_id)       new_rd_rsp_entry;     
       memory_txn#(w_addr, w_data, w_id)       copy_wr_rsp_entry;     // contains addr and intruction

       bit  [w_data/8-1:0]       wr_stb;
       bit  [w_data-1:0]         wr_data;
       bit  [w_data-1:0]         mem_data;
       bit  [w_data-1:0]         req_data;
       bit  [w_addr-1:0]         req_addr;
       int                       offset;
       bit                       cin;
       int                       last_one_strb; 
       
       forever begin
         m_mem_rsp_vif.wait_n_clocks(1);

         if((m_mem_rsp_vif.req_valid & m_mem_rsp_vif.req_ready & m_mem_rsp_vif.req_amo)) begin

          // ----------------------------------------
          // get alined addr and offset
          // ----------------------------------------
          req_addr    = m_mem_rsp_vif.req_addr;
          offset      = req_addr[$clog2(w_data/8) -1: 0];
          req_addr[$clog2(w_data/8) -1: 0] = 'h0;

          // ----------------------------------------
          // For analysis port 
          // ----------------------------------------
          copy_wr_rsp_entry       = new(); 
               
          copy_wr_rsp_entry.cmd   = MEM_ATOMIC;
          copy_wr_rsp_entry.data  = m_mem_rsp_vif.req_data;
          copy_wr_rsp_entry.strb  = m_mem_rsp_vif.req_strb;
          copy_wr_rsp_entry.atop  = m_mem_rsp_vif.amo_op; 
          ap_mem_req.write(copy_wr_rsp_entry);
           // ----------------------------------------------------
           // if new request address doesnt exixt in m_memory
           // push it in
           // else update the existing data 
           // ----------------------------------------------------
           // ----------------------------------------------------
           // Create a new m_memory node if this doesnt exists
           // ----------------------------------------------------
           if(!m_memory.exists(req_addr))  begin 
               
              new_node   = new();
              if(!new_node.randomize())  `uvm_fatal( "RSP_DELAY", "Response delay randomization failed" );
              m_memory[req_addr] = new_node;
              m_memory[req_addr].ldex_bytes[m_mem_rsp_vif.src_id] = 'h0; 
           end

           // -------------------------------------------------------
           // In the case of LDEX, reserve the words to be accessed
           // Remove previous lock 
           // -------------------------------------------------------
           if(m_mem_rsp_vif.amo_op == MEM_ATOMIC_LDEX) begin
             foreach(m_memory[req_addr].ldex_bytes[i]) m_memory[req_addr].ldex_bytes.delete(i);
             m_memory[req_addr].ldex_bytes[m_mem_rsp_vif.src_id] = m_mem_rsp_vif.req_strb; 
           end
           // --------------------------------------------------
           // Send read response  
           // --------------------------------------------------
           new_rd_rsp_entry          = new();
           new_rd_rsp_entry.data     = m_memory[req_addr].data;

           // --------------------------------------------------
           // In case of ATOMIC STEX , do not send read response
           // --------------------------------------------------
           if(!(m_mem_rsp_vif.amo_op == MEM_ATOMIC_STEX)) begin

             new_rd_rsp_entry.id         = m_mem_rsp_vif.req_id;
             // ---------------------------------------------
             // Insert an unsolicted rsp once in a while
             // ---------------------------------------------
             if(m_rsp_cfg.unsolicited_rsp) begin

                if(($urandom_range(0, 5) == 3)) begin
             
                  new_wr_rsp_entry            = new();
                  new_wr_rsp_entry.id         = $urandom; 
                  new_wr_rsp_entry.global_transmit_time     = 0;
                  wr_rsp_queue.push_back(new_wr_rsp_entry);
                  `uvm_info( "MEMORY RESPONSE MODEL", $sformatf("UNSOLICITED RSP : %0d", new_wr_rsp_entry.convert2string() ), UVM_MEDIUM );
                
                end
             
             end

             // ----------------------------------------------------
             // If error flag is set
             // -> Send AMO read error response
             // ----------------------------------------------------
             if(m_rsp_cfg.insert_amo_rd_error) begin
                if(amo_rd_rsp_error_counter < m_rsp_cfg.num_amo_rd_errors) begin
                   new_rd_rsp_entry.err     = ($urandom_range(0, 100) == 50) ? 1: 0 ;
                   if(new_rd_rsp_entry.err)  amo_rd_rsp_error_counter++;
               end
             end

             // --------------------------------------------------
             // Populate Rsp Object
             // --------------------------------------------------
             new_rd_rsp_entry.addr             = m_mem_rsp_vif.req_addr; 
             new_rd_rsp_entry.req_arrival_time = global_cycle_count;

             // --------------------------------------------------------
             // Generate new response delay for the incoming transaction 
             // --------------------------------------------------------
             new_rd_rsp_entry.global_transmit_time     = generate_rsp_delay("READ");
             `uvm_info( "MEMORY RESPONSE MODEL", $sformatf("AMO REQ : %0s", new_rd_rsp_entry.convert2string() ), UVM_LOW );

             // --------------------------------------------------
             //Add new rsp at appropriate place 
             // --------------------------------------------------
             q_index1             = rd_rsp_queue.find_last_index(rsp) with (rsp.id  == m_mem_rsp_vif.req_id);
             
             // --------------------------------------------------
             // IF ID already exists in the queue make it inorder response
             // --------------------------------------------------
             if(q_index1.size() > 0) begin

               rd_rsp_queue.insert(int'(q_index1[0]) + 1, new_rd_rsp_entry);
             
             end else begin

               q_index                = rd_rsp_queue.find_first_index(rsp) with (rsp.global_transmit_time > new_rd_rsp_entry.global_transmit_time);
          
               if(q_index.size() == 0) rd_rsp_queue.push_back(new_rd_rsp_entry);
               else                    rd_rsp_queue.insert(int'(q_index[0]), new_rd_rsp_entry);
             
             end
       
             q_index1.delete();
             q_index.delete();
           end // !MEM_ATOMIC_STEX
           
           
           wr_stb  = m_mem_rsp_vif.req_strb;
           wr_data = m_mem_rsp_vif.req_data;

           // -------------------------------------
           // Create a word from the bytes
           // Last strb is used to get the signed word
           // -------------------------------------
           mem_data      = 'h0;
           req_data      = 'h0;
           last_one_strb = 0; 
           for(int i = 0; i < w_data/8; i++) begin
             if ( wr_stb[i]) begin 
               mem_data[i*8 +: 8]   = m_memory[req_addr].data[i*8 +: 8]; 
               req_data[i*8 +: 8]   = wr_data[8*i +: 8];
               last_one_strb        = i; 
             end
           end


           `uvm_info("MEMORY RESPONSE MODEL", $sformatf("Before AMO Req ADDR = %0x(x) Req DATA = %0x(x) Mem DATA = %0x(x) index 1=%0d(d)", m_mem_rsp_vif.req_addr, req_data, mem_data, last_one_strb), UVM_FULL);

           // --------------------------------------------
           // Update the m_memory according to the AMO
           // --------------------------------------------
           cin = 0; 
           for(int k = 0; k < w_data/8; k++) begin

             if(wr_stb[k] == 1'b1) begin
               case(m_mem_rsp_vif.amo_op)
                 MEM_ATOMIC_STEX :     m_memory[req_addr].data[8*k +: 8]    =       wr_data[8*k +: 8]                                ; 
                 MEM_ATOMIC_CLR  :     m_memory[req_addr].data[8*k +: 8]    =      ~wr_data[8*k +: 8] & m_memory[req_addr].data[8*k +: 8];
                 MEM_ATOMIC_SET  :     m_memory[req_addr].data[8*k +: 8]    =       wr_data[8*k +: 8] | m_memory[req_addr].data[8*k +: 8];
                 MEM_ATOMIC_EOR  :     m_memory[req_addr].data[8*k +: 8]    =       wr_data[8*k +: 8] ^ m_memory[req_addr].data[8*k +: 8];
                 MEM_ATOMIC_SWAP :     m_memory[req_addr].data[8*k +: 8]    =       wr_data[8*k +: 8]                                ;
                 MEM_ATOMIC_ADD  :{cin,m_memory[req_addr].data[8*k +: 8]}   = adder(wr_data[8*k +: 8] , m_memory[req_addr].data[8*k +: 8], cin);
               endcase
             end
           end //foreach
       
           // -----------------------------
           // Min Max ATOMICs
           // -----------------------------
           case(m_mem_rsp_vif.amo_op)
              MEM_ATOMIC_SMAX :   begin
                // -------------------------------------------------------
                // Convert unsgined vector a signed vector
                // -------------------------------------------------------
                for(int i =(last_one_strb + 1)*8; i < w_data; i++) begin
                  mem_data[i]  = mem_data[(last_one_strb + 1)*8 -1];
                  req_data[i]  = req_data[(last_one_strb + 1)*8 -1];
                end
                if($signed(mem_data) < $signed(req_data)) begin
                  foreach (wr_stb[i]) begin
                    if(wr_stb[i]) m_memory[req_addr].data[8*i +: 8]      = wr_data[8*i +: 8];
                  end
                end
              end
              MEM_ATOMIC_SMIN :   begin
                // -------------------------------------------------------
                // Convert unsgined vector a signed vector
                // -------------------------------------------------------
                for(int i =(last_one_strb + 1)*8; i < w_data; i++) begin
                  mem_data[i]  = mem_data[(last_one_strb + 1)*8 -1];
                  req_data[i]  = req_data[(last_one_strb + 1)*8 -1];
                end
                if($signed(mem_data) > $signed(req_data)) begin
                  foreach (wr_stb[i]) begin
                    if(wr_stb[i]) m_memory[req_addr].data[8*i +: 8]      = wr_data[8*i +: 8];
                  end
                end
              end
              MEM_ATOMIC_UMAX :   begin
                if(mem_data < req_data) begin
                  foreach (wr_stb[i]) begin
                    if(wr_stb[i]) m_memory[req_addr].data[8*i +: 8]      = wr_data[8*i +: 8];
                  end
                end
              end
              MEM_ATOMIC_UMIN :   begin
                if(mem_data > req_data) begin
                  foreach (wr_stb[i]) begin
                    if(wr_stb[i]) m_memory[req_addr].data[8*i +: 8]      = wr_data[8*i +: 8];
                  end
                end
              end
           endcase

           
           `uvm_info("MEMORY RESPONSE MODEL", $sformatf("After AMO Req ADDR = %0x(x) DATA = %0x(x) Mem DATA = %0x(x)", m_mem_rsp_vif.req_addr, req_data, m_memory[req_addr].data), UVM_FULL);

           // --------------------------------------------------------
           // In case of ATOMIC LDEX do not send write response
           // --------------------------------------------------------
           if(!(m_mem_rsp_vif.amo_op == MEM_ATOMIC_LDEX)) begin
              new_wr_rsp_entry            = new();
              new_wr_rsp_entry.id         = m_mem_rsp_vif.req_id;
              new_wr_rsp_entry.ex_fail     = 0;

              // --------------------------------------------------------
              // In the case of STEX,
              // check if reservation exists for the same byte accessed by
              // STEX
              // For any other access remove the reservation 
              // --------------------------------------------------------
              if(m_memory[req_addr].ldex_bytes.exists(m_mem_rsp_vif.src_id)) begin
                if(m_mem_rsp_vif.amo_op == MEM_ATOMIC_STEX) begin
                  foreach(m_mem_rsp_vif.req_strb[i]) begin
                    if(m_mem_rsp_vif.req_strb[i] == 1) begin
                      if( m_memory[req_addr].ldex_bytes[m_mem_rsp_vif.src_id][i] == 0) begin
                        new_wr_rsp_entry.ex_fail = 1;
                       `uvm_info("MEMORY RESPONSE MODEL", $sformatf("SC FAILED %s", new_wr_rsp_entry.convert2string()), UVM_FULL);
                      end
                    end
                  end
                  m_memory[req_addr].ldex_bytes.delete(m_mem_rsp_vif.src_id);
                end
              end

              if(m_mem_rsp_vif.amo_op ==  MEM_ATOMIC_STEX) begin
                // ----------------------------------------------------
                // If error exclusive flag is set
                // ----------------------------------------------------
                if(m_rsp_cfg.insert_wr_exclusive_fail) begin
                   if(wr_rsp_exclusive_fail_counter < m_rsp_cfg.num_wr_exclusive_fails) begin
                       new_wr_rsp_entry.ex_fail     = ($urandom_range(0, 5) == 2) ? 1: 0 ;
                       `uvm_info("MEMORY RESPONSE MODEL", $sformatf("Inserted SC Exclusive Error %d", new_wr_rsp_entry.ex_fail), UVM_FULL);
                   end
                   if(new_wr_rsp_entry.ex_fail)  wr_rsp_exclusive_fail_counter++;
                end
              end
              // ----------------------------------------------------
              // If error flag is set
              // -> Send AMO write error response
              // ----------------------------------------------------
              if(m_rsp_cfg.insert_amo_wr_error) begin
                 if(amo_wr_rsp_error_counter < m_rsp_cfg.num_amo_wr_errors) begin
                     new_wr_rsp_entry.err     = ($urandom_range(0, 100) == 50) ? 1: 0 ;
                 end
                 if(new_wr_rsp_entry.err)  amo_wr_rsp_error_counter++;
              end


              new_wr_rsp_entry.addr             = m_mem_rsp_vif.req_addr; 
              new_wr_rsp_entry.req_arrival_time = global_cycle_count;
             // --------------------------------------------------------
             // Generate new response delay for the incoming transaction 
             // --------------------------------------------------------
             new_wr_rsp_entry.global_transmit_time     = generate_rsp_delay("WRITE");
             `uvm_info( "MEMORY RESPONSE MODEL", $sformatf("AMO WRITE REQ : %0s", new_wr_rsp_entry.convert2string() ), UVM_LOW );

             // --------------------------------------------------
             //Add new rsp at appropriate place 
             // --------------------------------------------------
             q_index1             = wr_rsp_queue.find_last_index(rsp) with (rsp.id  == m_mem_rsp_vif.req_id);
             
             // --------------------------------------------------
             // IF ID already exists in the queue make it inowrer response
             // --------------------------------------------------
             if(q_index1.size() > 0) begin

               wr_rsp_queue.insert(int'(q_index1[0]) + 1, new_wr_rsp_entry);
             
             end else begin

               q_index                = wr_rsp_queue.find_first_index(rsp) with (rsp.global_transmit_time > new_wr_rsp_entry.global_transmit_time);
          
               if(q_index.size() == 0) wr_rsp_queue.push_back(new_wr_rsp_entry);
               else                    wr_rsp_queue.insert(int'(q_index[0]), new_wr_rsp_entry);
             
             end


             q_index.delete();
             q_index1.delete();
           end // !MEM_ATOMIC_LDEX

           

         end// valid & ready & amo
       end // forever 
   endtask: populate_amo_rd_wr_rsp_queue; 

   // Function to generate rsp delay
   function int generate_rsp_delay(string S); 

     int   q_index[$];
     int   rsp_transmit_time;
      
     // -------------------------------
     //Generate response delay
     // -------------------------------
     m_rsp_delay = new();
     m_rsp_delay.m_rsp_cfg =  m_rsp_cfg; // rsp cfg, get from env 

     if(!m_rsp_delay.randomize() with {m_rsp_cfg ==  m_rsp_cfg;}) `uvm_fatal( "RSP_DELAY", "Response delay randomization failed" );
    
     case(m_rsp_cfg.rsp_order)
      IN_ORDER_RSP :
        begin
           if(m_rsp_cfg.rsp_mode == FIXED_DELAY_RSP) begin 
            
               // ----------------------------------------------------
               // In Fixed delay rsp add delay to the arrival time
               // ----------------------------------------------------
               rsp_transmit_time   = global_cycle_count + m_rsp_cfg.inter_data_cycle_fixed_delay;

           end else begin 

              if(S == "WRITE") begin
                if(wr_rsp_queue.size() == 0) rsp_transmit_time   = global_cycle_count + m_rsp_delay.rsp_delay;
                else                         rsp_transmit_time   = wr_rsp_queue[$].global_transmit_time  + m_rsp_delay.rsp_delay;
              end else begin
                if(rd_rsp_queue.size() == 0) rsp_transmit_time   = global_cycle_count + m_rsp_delay.rsp_delay;
                else                         rsp_transmit_time   = rd_rsp_queue[$].global_transmit_time  + m_rsp_delay.rsp_delay;
              end
           end
        end
      INVERSE_ORDER_RSP: // FIXME 
        begin

          if(S == "WRITE") begin
            if(wr_rsp_queue.size() == 0)   rsp_transmit_time   = m_rsp_delay.rsp_delay;
            else                           rsp_transmit_time   = wr_rsp_queue[0].global_transmit_time  - m_rsp_delay.rsp_delay;
          end else begin
            if(rd_rsp_queue.size() == 0)   rsp_transmit_time   = m_rsp_delay.rsp_delay;
            else                           rsp_transmit_time   = rd_rsp_queue[0].global_transmit_time  - m_rsp_delay.rsp_delay;
          end
        
        end
      OUT_OF_ORDER_RSP:
        begin

           rsp_transmit_time      = global_cycle_count + m_rsp_delay.rsp_delay;

           `uvm_info( "MEMORY RESPONSE MODEL: GENERATING DELAY", $sformatf("Generating delay : %0d(x) ",  m_rsp_delay.rsp_delay), UVM_MEDIUM );

           q_index.delete();
          
           // --------------------------------------------
           //If delay already exists in the queue
           //Generate another randome delay 
           // --------------------------------------------
           do begin

             if(S == "WRITE") q_index = wr_rsp_queue.find_index(rsp) with (rsp.global_transmit_time == rsp_transmit_time);
             else             q_index = rd_rsp_queue.find_index(rsp) with (rsp.global_transmit_time == rsp_transmit_time);

             if(!m_rsp_delay.randomize()) `uvm_fatal( "RSP_DELAY", "Response delay randomization failed" );

             `uvm_info( "MEMORY RESPONSE MODEL: GENERATING DELAY", $sformatf("Generating delay : %0d(x) ",  m_rsp_delay.rsp_delay), UVM_MEDIUM );
             rsp_transmit_time     = global_cycle_count + m_rsp_delay.rsp_delay;

           end while (q_index.size() > 0 );
        end 
      default:
        begin    
            `uvm_fatal( "RSP_CFG_FATAL", "Undefinded order configuration" );
        end
     endcase//begin case 

     q_index.delete();

     // Debug
     `uvm_info( "MEMORY RESPONSE MODEL", $sformatf("RANDOM DELAY VALUE : %0d", rsp_transmit_time ), UVM_MEDIUM );

     return rsp_transmit_time;
   endfunction: generate_rsp_delay;

   // API to clear rsp error cvounter 
   function void clear_rd_rsp_error_counter();
       rd_rsp_error_counter = 0;
   endfunction

   // API to clear rsp error cvounter 
   function void clear_wr_rsp_error_counter();
       wr_rsp_error_counter = 0;
   endfunction

   // API to enable rd/wr responses 
   // User can ask rsponse model to stop sending rsponses 
  function void set_enable_rd_output(bit value);
      `uvm_info("MEMORY RESPONSE MODEL", $sformatf("the values of enable is %0d(d)", value), UVM_MEDIUM);
      enable_rd_output = value;                                                                  
  endfunction                                                                                    
                                                                                                 
  function void set_enable_wr_output(bit value);                                                 
      `uvm_info("MEMORY RESPONSE MODEL", $sformatf("the values of enable is %0d(d)", value), UVM_MEDIUM);
      enable_wr_output = value;
  endfunction


  // Add a new entry in the m_memory
  //
  function void add_memory_node(bit [w_addr -1 : 0] addr, bit [w_data -1: 0] data);
     memory_c#(w_data)                      new_node;     // contains addr and intruction

     if(!m_memory.exists(addr)) begin 
       new_node        = new("new m_memory node");
       new_node.data   = data;
       m_memory[addr]      = new_node;
       `uvm_info("MEMORY RESPONSE MODEL", $sformatf("ADDR=%0x(x) DATA=%x(x)", addr, data), UVM_MEDIUM);
     end else begin                                                                            
       m_memory[addr].data    = data;                                                          
       `uvm_info("MEMORY RESPONSE MODEL", $sformatf("ADDR=%0x(x) DATA=%x(x)", addr, data), UVM_MEDIUM);
     end
   endfunction

  // delete a new entry in the m_memory
  //
  function void delete_memory_node(bit [w_addr -1 : 0] addr);

     if(m_memory.exists(addr)) begin 
       `uvm_info("MEMORY RESPONSE MODEL", $sformatf("ADDR=%0x(x)", addr), UVM_MEDIUM);
       m_memory.delete(addr);
     end
   endfunction

   // Function to addition and substraction
   function logic [8:0] adder(input logic [7:0] x, y, input logic cin);

      logic [7:0] s; // internal signals
      logic c;

      c = cin;
      for (int k = 0; k < 8; k++) begin
        s[k] = x[k] ^ y[k] ^ c;
        c = (x[k] & y[k]) | (c & x[k]) | (c & y[k]);
      end
      adder = {c, s};
   endfunction

   // APIs to get performance counters 

   function  bit [31:0]   get_wr_req_counter();
     get_wr_req_counter = m_mem_rsp_vif.wr_req_counter;
   endfunction
   function  bit [31:0]   get_rd_req_counter();
     get_rd_req_counter = m_mem_rsp_vif.rd_req_counter;
   endfunction
   function  bit [31:0]   get_bp_req_counter();
     get_bp_req_counter = m_mem_rsp_vif.bp_req_counter;
   endfunction
    
   function  bit [31:0]   get_wr_rsp_counter();
     get_wr_rsp_counter = m_mem_rsp_vif.wr_rsp_counter;
   endfunction
   function  bit [31:0]   get_rd_rsp_counter();
     get_rd_rsp_counter = m_mem_rsp_vif.rd_rsp_counter;
   endfunction
   function  bit [31:0]   get_bp_rsp_counter();
     get_bp_rsp_counter = m_mem_rsp_vif.bp_rsp_counter;
   endfunction
   function  bit [31:0]	  get_amo_req_counter();
     get_amo_req_counter = m_mem_rsp_vif.amo_req_counter;
   endfunction
endclass : memory_response_model

