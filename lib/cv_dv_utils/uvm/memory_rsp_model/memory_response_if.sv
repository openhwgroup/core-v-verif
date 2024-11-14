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
//  Description : The MEM interface
//                 It contains: 
//                 -> READ, WRITE and AMO request interface 
//                 -> READ, WRITE and AMO request counters 
//                 -> READ, WRITE response counters 
//
//                
// 
// ----------------------------------------------------------------------------

import memory_rsp_model_pkg::*;

// ==============================================================
// Memory interface is paramterized interface 
// The parameters are: 
// address width (addr_width)
// data width    (data_width) 
// id width      (id_width) 
// ==============================================================
interface memory_response_if ( input bit clk, input bit rstn );

    parameter  addr_width       = 64; 
    parameter  data_width       = 512;
    parameter  id_width         = 16; 

    localparam  strb_width  = data_width/8; 

    // ----------------------------------------------------------------------
    //                  REAL SIGNALS ON THE INTERFACE
    // ----------------------------------------------------------------------
    //
    // ------------------------------------------------------------------------
    // ------------------------------------------------------------------------
    //
    // Request Interface 
    //
    // ------------------------------------------------------------------------
    // For every request which is not amo, user needs to drive req_amo to zero
    // ------------------------------------------------------------------------
    logic                                          req_valid;

    // ---------------------------------------------------------------------------
    // The request ready signal is not driven. User needs to connect this signal. 
    // There are 2 possibilities:  
    // 1. Either user connects this signal to the internally generated req_ready_bp 
    // 2. Or user connects this signal to its own ready signal
    // 3. req_ready_bp_cfg: This configuration variable is used to generate req_ready_bp
    // ---------------------------------------------------------------------------
    logic                                          req_ready;         
    logic                                          req_ready_bp;      // user need to connect ready_bp to ready 
    bp_t                                           req_ready_bp_cfg;   

    // ----------------------------------------------------------------------
    //                  REAL SIGNALS ON THE INTERFACE
    // ----------------------------------------------------------------------
    logic  [addr_width-1:0]                        req_addr;
    logic                                          req_wrn; 
    logic  [id_width -1: 0]                        req_id;
    logic  [data_width-1:0]                        req_data;
    logic  [strb_width-1:0]                        req_strb;

    // ----------------------------------------------------------------------
    // Write Response Interface 
    // ----------------------------------------------------------------------
    logic                                          wr_res_valid;
    logic  [id_width -1: 0]                        wr_res_id;
    logic                                          wr_res_err;    
    logic  [addr_width-1:0]                        wr_res_addr;

    // ----------------------------------------------------------------------
    // In the legacy model there was no response ready signal 
    // to respect the back compatibility the DV_UTILS_MRM_WRITE_RSP_READY
    // ----------------------------------------------------------------------
    logic                                          wr_res_ready;

    // ----------------------------------------------------------------------
    // Read Response Interface 
    // ----------------------------------------------------------------------
    logic                                          rd_res_valid; 
    logic  [data_width-1:0]                        rd_res_data;
    logic  [id_width -1: 0]                        rd_res_id;
    logic                                          rd_res_err;
    logic  [addr_width-1:0]                        rd_res_addr;

    // ----------------------------------------------------------------------
    // In the legacy model there was no response ready signal 
    // to respect the back compatibility the DV_UTILS_MRM_READ_RSP_READY
    // ----------------------------------------------------------------------
    logic                                          rd_res_ready;
    
    // --------------------------------------------------------------
    // Amo Request interface 
    // --------------------------------------------------------------
    // --------------------------------------------------------------
    // In the case of AMOs, user needs to drive req_amo to 1
    // --------------------------------------------------------------
    logic                                          req_amo;  //input
    // --------------------------------------------------------------
    // Following AXI compatible amo operations are used 
    //    MEM_ATOMIC_ADD  = 4'b0000,
    //    MEM_ATOMIC_CLR  = 4'b0001, // NAND
    //    MEM_ATOMIC_SET  = 4'b0010, // OR
    //    MEM_ATOMIC_EOR  = 4'b0011,
    //    MEM_ATOMIC_SMAX = 4'b0100,
    //    MEM_ATOMIC_SMIN = 4'b0101,
    //    MEM_ATOMIC_UMAX = 4'b0110,
    //    MEM_ATOMIC_UMIN = 4'b0111,
    //    MEM_ATOMIC_SWAP = 4'b1000,
    //    MEM_ATOMIC_CMP  = 4'b1001,
    //      Reserved           = 4'b1010,
    //      Reserved           = 4'b1011,
    //    MEM_ATOMIC_LDEX = 4'b1100,
    //    MEM_ATOMIC_STEX = 4'b1101
    //      Reserved           = 4'b1110,
    //      Reserved           = 4'b1111
    // --------------------------------------------------------------
    mem_atomic_t			                       amo_op;

    // -------------------------------------------------------------------------
    // SRC_ID needs to be provided in the case where LDEX/STEX amo instruction
    // are used 
    // -------------------------------------------------------------------------
    logic  [id_width -1: 0]                        src_id;

    // -------------------------------------------------------------------------
    // Error in the case of Exclusive instruction  
    // -------------------------------------------------------------------------
    logic                                          wr_res_ex_fail; 
    logic                                          rd_res_ex_fail; 

    // ------------------------------------------------------------------------
    // memory counter to count number of memory req 
    // ------------------------------------------------------------------------
    bit [31:0]                                    wr_req_counter;
    bit [31:0]                                    rd_req_counter;
    bit [31:0]                                    bp_req_counter;

    bit [31:0]                                    wr_rsp_counter;
    bit [31:0]                                    rd_rsp_counter;
    bit [31:0]                                    bp_rsp_counter;
    bit [31:0]				                      amo_req_counter;

    // ------------------------------------------------------------------------
    // Flag to control Verbosity
    // ------------------------------------------------------------------------
    logic                                          verbose;


    /* pragma translate_off */

     assert property ( @(posedge clk) disable iff(!rstn) ( req_valid && req_ready ) -> !$isunknown( req_id          ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( req_valid && req_ready ) -> !$isunknown( req_wrn        ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( req_valid && req_ready ) -> !$isunknown( req_addr        ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( req_valid && req_ready ) -> !$isunknown( req_data        ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( req_valid && req_ready ) -> !$isunknown( req_strb        ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( req_valid && req_ready ) -> !$isunknown( req_amo        ) );

    `ifdef DV_UTILS_MRM_READ_RSP_READY
     assert property ( @(posedge clk) disable iff(!rstn) ( rd_res_valid && rd_res_ready ) -> !$isunknown( rd_res_id          ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( rd_res_valid && rd_res_ready ) -> !$isunknown( rd_res_addr        ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( rd_res_valid && rd_res_ready ) -> !$isunknown( rd_res_data        ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( rd_res_valid && rd_res_ready ) -> !$isunknown( rd_res_err        ) );
    `else
     assert property ( @(posedge clk) disable iff(!rstn) ( rd_res_valid  == 1 ) -> !$isunknown( rd_res_id          ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( rd_res_valid  == 1 ) -> !$isunknown( rd_res_addr        ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( rd_res_valid  == 1 ) -> !$isunknown( rd_res_data        ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( rd_res_valid  == 1 ) -> !$isunknown( rd_res_err        ) );
    `endif

    `ifdef DV_UTILS_MRM_WRITE_RSP_READY
     assert property ( @(posedge clk) disable iff(!rstn) ( wr_res_valid && wr_res_ready ) -> !$isunknown( wr_res_id          ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( wr_res_valid && wr_res_ready ) -> !$isunknown( wr_res_addr        ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( wr_res_valid && wr_res_ready ) -> !$isunknown( wr_res_err        ) );
    `else
     assert property ( @(posedge clk) disable iff(!rstn) ( wr_res_valid  == 1 ) -> !$isunknown( wr_res_id          ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( wr_res_valid  == 1 ) -> !$isunknown( wr_res_addr        ) );
     assert property ( @(posedge clk) disable iff(!rstn) ( wr_res_valid  == 1 ) -> !$isunknown( wr_res_err        ) );
    `endif
  /* pragma translate_on */





    // ------------------------------------------------------------------------
    // Enable verbosity based on command line
    // ------------------------------------------------------------------------
    initial begin
     if ( $test$plusargs("DEBUG") ) begin
         verbose = 1;
     end else begin
         verbose = 0;
      end // if
    end // if

    // ------------------------------------------------------------------------
    // Delay Task
    // ------------------------------------------------------------------------
    task wait_n_clocks( int N );          // pragma tbx xtf
      begin
         @(posedge clk);
         repeat (N-1) @( posedge clk );
      end
    endtask : wait_n_clocks 

    // ------------------------------------------------------------------------
    //                Clock Counter
    //
    // Free running clock counter used to timestamp transactions
    // ------------------------------------------------------------------------
    int unsigned clock_counter;

    always_ff @(posedge clk or negedge rstn) begin : CLK_COUNTER
       if (rstn==0) begin
          clock_counter <=0;
       end else begin
          clock_counter <= clock_counter+1;
       end // if
    end : CLK_COUNTER
  
  
       // Back Pressure on ready signal 
    always_ff @(posedge clk or negedge rstn) begin
      if(~rstn) begin
        req_ready_bp <= 0;
      end else begin
        case(req_ready_bp_cfg)
          NEVER :
          begin
           req_ready_bp <= 1'b1; 
          end
          LIGHT : 
          begin 
           if($urandom_range(1, 3) == 2)     req_ready_bp <= 1'b0;
           else                              req_ready_bp <= 1'b1; 
          end
          MEDIUM:
          begin 
           if($urandom_range(1, 10) >= 4)    req_ready_bp <= 1'b0;
           else                              req_ready_bp <= 1'b1; 
          end
          HEAVY: 
          begin 
           if($urandom_range(1, 20) >= 5)    req_ready_bp <= 1'b0;
           else                              req_ready_bp <= 1'b1; 
          end
        endcase
      end
    end

    // ------------------------------------------------------------------------
    // memory req counter
    // ------------------------------------------------------------------------
    always @(negedge clk or negedge rstn) begin : REQ_COUNTER
       if (rstn==0) begin
          rd_req_counter  <=0;
          wr_req_counter  <=0;
       end else if(req_valid & req_ready&req_wrn) begin
           rd_req_counter   <=  rd_req_counter  + 1;
       end else if(req_valid & req_ready&!req_wrn) begin
           wr_req_counter   <=  wr_req_counter  + 1;
      end // if
    end : REQ_COUNTER

    always @(negedge clk or negedge rstn) begin : RSP_COUNTER
       if (rstn==0) begin
          rd_rsp_counter  <=0;
          wr_rsp_counter  <=0;
       end else if(rd_res_valid) begin
          rd_rsp_counter   <=  rd_rsp_counter  + 1;
       end else if(wr_res_valid) begin
          wr_rsp_counter   <=  wr_rsp_counter  + 1;
      end // if
    end : RSP_COUNTER

    always @(negedge clk or negedge rstn) begin : BP_COUNTER
       if (rstn==0) begin
          bp_req_counter <=0;
       end else if(!req_ready) begin
          bp_req_counter++;
      end // if
    end : BP_COUNTER

    always @(negedge clk or negedge rstn) begin : AMO_REQ_COUNTER
       if (rstn==0) begin
          amo_req_counter  <=0;
       end else if(req_valid & req_ready & req_amo) begin
           amo_req_counter   <=  amo_req_counter  + 1;
      end // if
    end : AMO_REQ_COUNTER

endinterface: memory_response_if


