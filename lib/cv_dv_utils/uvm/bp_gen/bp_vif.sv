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
//  Description :  Interface for a single wire backpressure signal.
//
//                 This interface is written so that the tasks can be
//                 synthesized in the emulator.
//                
// 
// ----------------------------------------------------------------------------


interface bp_vif ( input bit clk,
                  input bit rstn );
//pragma attribute interface_tif partition_interface_xif

import bp_vif_xrtl_pkg::*;

   // ----------------------------------------------------------------------
   // Interface parameters
   // ----------------------------------------------------------------------
   parameter integer unsigned p_is_active = 1;

   localparam                 fifo_depth = 8;
   localparam                 fifo_ptr_width = $clog2( fifo_depth );
   localparam                 burst_ptr_width = $clog2( bp_txns_per_xfer );
   localparam logic           p_bp_asserted_value = 1'b1;

   // ----------------------------------------------------------------------
   // ----------------------------------------------------------------------
   //                  REAL SIGNALS ON THE INTERFACE
   // ----------------------------------------------------------------------
   // ----------------------------------------------------------------------
   // Common control signals interface
   logic                    bp_out;

   // ------------------------------------------------------------------------
   // Shared class instance between HVL and HDL so HDL can call HVL
   // ------------------------------------------------------------------------
   bp_vif_xrtl hvl_obj;

   // ------------------------------------------------------------------------
   // FIFO to Hold Incoming TXNs
   // ------------------------------------------------------------------------
   driver_burst_bp_txn_t        txn_fifo [ fifo_depth ];

   reg [fifo_ptr_width-1:0]     rd_ptr_FF,       wr_ptr_FF;
   reg [burst_ptr_width-1:0]    rd_burst_ptr_FF, wr_burst_ptr_FF;

   // ------------------------------------------------------------------------
   // Buffer to hold current txn
   // ------------------------------------------------------------------------
   driver_single_bp_txn_t       curr_txn;    // current transaction on read side
   driver_burst_bp_txn_t        curr_burst;  // burst being assembled on write side
   
   // ------------------------------------------------------------------------
   // Variable to hold random seed
   // ------------------------------------------------------------------------
   integer unsigned              m_seed;
   bit                           m_load_seed = 0;

   // ------------------------------------------------------------------------
   // FIFO to hold Incoming Transactions
   // ------------------------------------------------------------------------

   // ------------------------------------------------------------------------
   // ------------------------------------------------------------------------
   //        API FOR DRIVING THE INTERFACE (EMULATION AND SIMULATION)
   // ------------------------------------------------------------------------
   // ------------------------------------------------------------------------
   event    done_sending;
   event    start_sending;

   // ------------------------------------------------------------------------
   // set_random_seed
   //
   // In this interface, we use $urandom to generate the clock-by-clock
   //   randomness when a specific percentage of BP is requested. We want
   //   each instance of this interface to obtain a different random seed.
   //   To ensure this is the case, the driver creates a seed in the UVM
   //   world and then provides this seed into the interface. The seed
   //   is then loaded in the process that uses the $urandom. The random
   //   generation is then seeded for that process (always block).
   // ------------------------------------------------------------------------
   function void set_seed( integer unsigned seed );
      m_seed = seed;
      m_load_seed = 1;
   endfunction : set_seed

   // ------------------------------------------------------------------------
   // task send()
   //
   // This task is used by the driver to send a BP transaction to the driver
   // ------------------------------------------------------------------------
   task send( driver_burst_bp_txn_t new_txns );
      begin
         for( int i=0 ; i<bp_txns_per_xfer ; i++ ) begin
/*
            $display("%m SENDING BP TXN : i=%0d V=%0b TYPE=%0d N=%0d", 
                i, new_txns.txns[i].valid, 
                   new_txns.txns[i].bp_type, 
                   new_txns.txns[i].N );
 */
         end // for
         txn_fifo[ wr_ptr_FF ] = new_txns ;
         wr_ptr_FF++;
      end
   endtask : send

   function fifo_empty( );
   begin
       fifo_empty = ( rd_ptr_FF == wr_ptr_FF );
   end
   endfunction : fifo_empty
      
   function fifo_full( );
   begin
       fifo_full = ( ( ( wr_ptr_FF + 1 ) % fifo_depth ) == rd_ptr_FF );
   end
   endfunction : fifo_full
      
   always @ ( posedge clk ) begin : BP_DRIVE_PROCESS

      integer bp_rand_value;

      // Only once, we load the random seed provided by UVM
      // It is to avoid rise condition between processes which could lead to have different seed
      if ( m_load_seed ) begin
         process::self.srandom( m_seed );
         m_load_seed = 0;
      end // if

      if ( ~rstn ) begin
         wr_ptr_FF <= 'd0;
         rd_ptr_FF <= 'd0;
         wr_burst_ptr_FF <= 'd0;
         rd_burst_ptr_FF <= 'd0;
         rd_burst_ptr_FF <= 'd0;
         curr_txn.N <= 0;
         bp_out <= ~p_bp_asserted_value;
      end else begin
         if ( ( curr_txn.N > 0 ) && ( curr_txn.valid ) ) begin
            case ( curr_txn.bp_type )
               BP_OFF     : bp_out <= ~p_bp_asserted_value;
               BP_ON      : bp_out <= p_bp_asserted_value; 
               BP_TOGGLE  : bp_out <= ( curr_txn.N % curr_txn.M ) ?  // M = toggle rate
                                      ~bp_out : bp_out;
               BP_PERCENT : begin
                               bp_rand_value = $urandom_range(100);
                               bp_out <= ( bp_rand_value < curr_txn.M ) ?
                                           p_bp_asserted_value : ~p_bp_asserted_value;
                            end
               default	  : bp_out <= ~p_bp_asserted_value; // BP_OFF by default
	    endcase
            curr_txn.N <= curr_txn.N - 'd1;
         end else begin
            // If FIFO is empty, send no BP and trigger event
            if ( ( rd_burst_ptr_FF == 'd0 ) && ( wr_ptr_FF == rd_ptr_FF ) ) begin
               bp_out <= ~p_bp_asserted_value;
               ->done_sending;
            end else begin
               // Update curr_txn
               curr_txn <= txn_fifo[ rd_ptr_FF ].txns[ rd_burst_ptr_FF ];
               // Advance Pointers
               rd_burst_ptr_FF <= rd_burst_ptr_FF + 1;
               if ( rd_burst_ptr_FF == ( bp_txns_per_xfer - 1 ) ) begin
                   rd_ptr_FF <= rd_ptr_FF + 'd1;
               end // if
            end // if
         end // if
      end // if
   end // always

   task force_bp_out(logic bp);
     force bp_out = bp;
   endtask
   task release_bp_out();
     release bp_out;
   endtask
endinterface: bp_vif


