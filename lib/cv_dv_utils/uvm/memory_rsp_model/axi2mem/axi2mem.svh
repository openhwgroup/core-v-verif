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
//  Description : In this class we recieve transaction from the mem response model
//                The transaction is stored in a fifo and is driven to axi and
//                vice versa 
// ----------------------------------------------------------------------------


class axi2mem#(int unsigned w_addr = 0,  int unsigned w_data = 0, int unsigned w_id   = 0, int unsigned w_user = 0) extends uvm_component;

  localparam int unsigned STRB_WIDTH = w_data / 8;


    `uvm_component_param_utils( axi2mem#(w_addr,w_data,w_id,w_user))

    typedef struct packed
    {
       logic [w_addr-1:0]        addr;
       logic [7:0]               len;
       logic [2:0]               size;
       logic [5:0]               atop;
       logic [w_id-1:0]          id;
       axi_burst_t               burst;
       logic                     lock;
       axi_cache_t               cache;
       logic [2:0]               prot;
       logic [3:0]               qos;
       logic [3:0]               region;
       logic [w_user-1:0]        user;
    } aw_ar_chan_t;


    typedef struct packed
    {
      logic [STRB_WIDTH-1:0]    strb;
      logic [w_data-1:0]        data;
      logic                     last;
      logic [w_user-1:0]        user;
    } w_chan_t;

    typedef struct packed
    {
      aw_ar_chan_t aw_chan;
      w_chan_t      w_chan; 
    } aw_w_chan_t;

    typedef struct packed
    {
      axi_resp_t                resp;
      logic [w_id-1:0]          id;
      logic [w_user-1:0]        user;
    } b_chan_t;


    typedef struct packed
    {
       logic [w_data-1:0]        data;
       logic                     last;
       logic [w_id-1:0]          id;
       axi_resp_t                resp;
       logic [w_user-1:0]        user;
    } r_chan_t;

    // ------------------------------------------------------------------------
    // Local variable
    // ------------------------------------------------------------------------
    protected string name ;
    // ------------------------------------------------------------------------
    // Modules
    // -----------------------------------------------------------------------
    virtual memory_response_if#( w_addr, w_data, w_id )       mem_rd_vif; 
    virtual memory_response_if#( w_addr, w_data, w_id )       mem_wr_vif; 
    virtual axi_if#( w_addr, w_data, w_id, w_user )           axi_vif; 
    
    // ------------------------------------------------------------------------
    // Queue to store upcoming transactions 
    // -----------------------------------------------------------------------
   // mailbox #( r_chan_t)     mb_ar_chan   = new(10);
   // mailbox #( r_chan_t)     mb_r_chan    = new(10);
   // mailbox #( aw_ar_chan_t) mb_aw_chan   = new(10);
   // mailbox #( w_chan_t)     mb_w_chan    = new(10);
   // mailbox #( aw_w_chan_t)  mb_aw_w_chan = new(10);
   // mailbox #( b_chan_t)     mb_b_chan    = new(10);

    aw_ar_chan_t mb_ar_chan[$];
    r_chan_t     mb_r_chan[$] ;
    aw_ar_chan_t mb_aw_chan[$];
    w_chan_t     mb_w_chan[$] ;
    aw_w_chan_t  mb_aw_w_chan[$];
    b_chan_t     mb_b_chan[$];
    // ------------------------------------------------------------------------
    // queue to reconstuct the response for multiple mem responses 
    // -----------------------------------------------------------------------
    aw_ar_chan_t       q_num_aw_chan_req[integer][$];
    aw_ar_chan_t       q_num_ar_chan_req[integer][$];
    // ----------------------------------------------------------------------- 
    // Constructor
    // ----------------------------------------------------------------------- 
    function new( string name , uvm_component parent = null ); 
      super.new( name , parent);
      this.name = name;
    endfunction



   //================================================================================
   // Build Phase
   //================================================================================
   function void build_phase(uvm_phase phase);

        if(!uvm_config_db #( virtual axi_if #( w_addr, w_data, w_id, w_user ) )::get(this, "", get_name(), axi_vif )) begin
            `uvm_fatal("BUILD_PHASE", $sformatf("Unable to get axi_vif for %s from configuration database", get_name() ) );
        end

        if(!uvm_config_db #( virtual memory_response_if #( w_addr, w_data, w_id ) )::get(this, "", $sformatf("%s_rd", get_name()), mem_rd_vif )) begin
            `uvm_fatal("BUILD_PHASE", $sformatf("Unable to get mem_wr_vif for %s from configuration database", get_name() ) );
        end

        if(!uvm_config_db #( virtual memory_response_if #( w_addr, w_data, w_id ) )::get(this, "", $sformatf("%s_wr", get_name()), mem_wr_vif )) begin
            `uvm_fatal("BUILD_PHASE", $sformatf("Unable to get mem_wr_vif for %s from configuration database", get_name() ) );
        end
   endfunction : build_phase

    // ------------------------------------------------------------------------
    // Reset phase // 
    // ------------------------------------------------------------------------ 
    virtual task reset_phase(uvm_phase phase);
      super.reset_phase(phase);
      `uvm_info(this.name, "Reset stage complete.", UVM_LOW)
      axi_vif.b_valid  = 1'b0;
      axi_vif.r_valid  = 1'b0;
      mem_rd_vif.req_valid   = 1'b0;
      mem_wr_vif.req_valid   = 1'b0;

      mb_ar_chan.delete();
      mb_r_chan.delete();
      mb_aw_chan.delete();
      mb_w_chan.delete();
      mb_aw_w_chan.delete();
      mb_b_chan.delete();

      q_num_aw_chan_req.delete();
      q_num_ar_chan_req.delete();
    endtask
    // ----------------------------------------------------------------------- 
    // Main phase
    // ----------------------------------------------------------------------- 
    virtual task main_phase ( uvm_phase phase );

 
       // ----------------------------------------------------------------------------
       // write_axi_r_chan_fifo : new sequence item is created and new transaction 
       // ----------------------------------------------------------------------------
       fork 
         write_aw_chan_fifo(); 
         write_w_chan_fifo(); 
         create_mem_req_from_aw_w_chan_fifo(); 
         convert_aw_w_chan_to_mem_req(); 
         write_ar_chan_fifo();
         convert_ar_chan_to_mem_req(); 
         write_b_chan_fifo(); 
         convert_b_chan_to_mem_intf(); 
         write_r_chan_fifo(); 
         convert_r_chan_to_mem_intf(); 
       join_none

       super.main_phase(phase);
    endtask


    // ----------------------------------
    // put 
    // ----------------------------------
    virtual task write_aw_chan_fifo( );

       aw_ar_chan_t     req;
       // Drive axi iterface
       forever begin

         @ (posedge axi_vif.clk);

         if(axi_vif.aw_ready && axi_vif.aw_valid ) begin
             req.addr   = axi_vif.aw_addr   ;
             req.len    = axi_vif.aw_len    ;
             req.size   = axi_vif.aw_size   ;
             req.atop   = axi_vif.aw_atop   ;
             req.id     = axi_vif.aw_id     ;
             req.burst  = axi_vif.aw_burst  ;
             req.lock   = axi_vif.aw_lock   ;
             req.cache  = axi_vif.aw_cache  ;
             req.prot   = axi_vif.aw_prot   ;
             req.qos    = axi_vif.aw_qos    ;
             req.region = axi_vif.aw_region ;
             req.user   = axi_vif.aw_user   ;
           
             mb_aw_chan.push_back(req);
             `uvm_info("AXI2MEM AW CHAN REQ", $sformatf("ADDR %0x(x)", req.addr), UVM_HIGH);
         end

       end
    endtask
    // ----------------------------------
    // ----------------------------------
    virtual task write_w_chan_fifo( );

       w_chan_t         req;
       // Drive axi iterface
       forever begin

         @ (posedge axi_vif.clk);
         if(axi_vif.w_ready && axi_vif.w_valid ) begin
            req.strb  =  axi_vif.w_strb;
            req.data  =  axi_vif.w_data;
            req.last  =  axi_vif.w_last;
            req.user  =  axi_vif.w_user;
            mb_w_chan.push_back(req);
         end

       end
    endtask

    // --------------------------------------------------------
    // get
    // Get write request and get corresponding data 
    // create extended mem request to be sent to the mem model
    // --------------------------------------------------------
    virtual task create_mem_req_from_aw_w_chan_fifo( );
       aw_ar_chan_t        aw_req;
       w_chan_t            w_req;
       aw_w_chan_t         aw_w_req;
       int                 cnt;
       bit [w_addr - 1: 0] start_addr; 
       bit [w_addr - 1: 0] aligned_addr; 
       int unsigned        num_bytes; 
       int unsigned        burst_length;
       int unsigned        lower_byte_lane;
       int unsigned        upper_byte_lane;
       int unsigned        wd_strb;
       // Drive axi iterface
       forever begin

         // -------------------------------------
         // Get the write request 
         // -------------------------------------
         wait (mb_aw_chan.size() > 0);
         aw_req       = mb_aw_chan.pop_front();
         num_bytes    = 2**aw_req.size;
         burst_length = aw_req.len + 1;
         start_addr   = aw_req.addr;
         aligned_addr = (start_addr/num_bytes)*num_bytes; 
         wd_strb      = w_data/8;
         cnt = 0;

         // -------------------------------------
         // Look for the corresponding data
         // -------------------------------------
         do begin

            wait(mb_w_chan.size() > 0);
            w_req = mb_w_chan.pop_front();

            // --------------------------------
            // Get the addr 
            // --------------------------------
            case(aw_req.burst)
             BURST_INCR  : aw_req.addr  = (cnt == 0)? start_addr : (aligned_addr + cnt * num_bytes);
             BURST_FIXED : aw_req.addr  = start_addr;
             default     : aw_req.addr  = start_addr; // FIXME: Add other options 
            endcase

            cnt++;
            aw_w_req.aw_chan = aw_req; 
            aw_w_req.w_chan  = w_req;
            mb_aw_w_chan.push_back(aw_w_req);

         end while(w_req.last == 0);

         // -------------------------------------
         // To reconstruct the response
         // -------------------------------------
         q_num_aw_chan_req[aw_req.id].push_back(aw_req); 
       end
    endtask

    // --------------------------------------²------------------
    // get
    // Drive this to memory response model 
    // --------------------------------------------------------
    virtual task convert_aw_w_chan_to_mem_req( );
       aw_w_chan_t req;

       // Drive mem iterface
       mem_wr_vif.req_valid       = 1'b0;

       forever begin
       //  for (int i = 0; i <= req.aw_chan.len; i++) begin
 
         if(mb_aw_w_chan.size() == 0) begin 
           @ (posedge mem_wr_vif.clk);
         end else begin
           req = mb_aw_w_chan.pop_front();
           mem_wr_vif.req_valid     = 1'b1;
           mem_wr_vif.req_addr      = req.aw_chan.addr;
           mem_wr_vif.req_wrn       = 1'b0; 
           mem_wr_vif.req_id        = req.aw_chan.id ;
           mem_wr_vif.src_id        = req.aw_chan.id ;

           // ---------------------------------------
           // Drive every flit of data (len + 1)
           // ---------------------------------------
           mem_wr_vif.req_data      = req.w_chan.data;
           mem_wr_vif.req_strb      = req.w_chan.strb;

           // AMO = 1, WRN = 0 => AtomicStore
           // AMO = 1, WRN = 1 => AtomicLoad
           mem_wr_vif.req_amo = 0;
           case(req.aw_chan.atop[5:4])
             AXI_ATOMIC_NONE   : mem_wr_vif.req_amo = 0; 
             AXI_ATOMIC_STORE  : 
             begin
               // Does not require a read response 
               mem_wr_vif.req_amo = 1;  
               mem_wr_vif.req_wrn = 0;
               case(req.aw_chan.atop[2:0])
                 AXI_ATOMIC_ADD   : mem_wr_vif.amo_op = MEM_ATOMIC_ADD ;
                 AXI_ATOMIC_CLR   : mem_wr_vif.amo_op = MEM_ATOMIC_CLR ;
                 AXI_ATOMIC_EOR   : mem_wr_vif.amo_op = MEM_ATOMIC_SET ;
                 AXI_ATOMIC_SET   : mem_wr_vif.amo_op = MEM_ATOMIC_EOR ;
                 AXI_ATOMIC_SMAX  : mem_wr_vif.amo_op = MEM_ATOMIC_SMAX;
                 AXI_ATOMIC_SMIN  : mem_wr_vif.amo_op = MEM_ATOMIC_SMIN;
                 AXI_ATOMIC_UMAX  : mem_wr_vif.amo_op = MEM_ATOMIC_UMAX;
                 AXI_ATOMIC_UMIN  : mem_wr_vif.amo_op = MEM_ATOMIC_UMIN;
               endcase  
               q_num_ar_chan_req[req.aw_chan.id].push_back(0);
             end
             AXI_ATOMIC_LOAD   : begin
               // Requires a read response 
               mem_wr_vif.req_amo = 1;  
               mem_wr_vif.req_wrn = 0;
               case(req.aw_chan.atop[2:0])
                 AXI_ATOMIC_ADD   : mem_wr_vif.amo_op = MEM_ATOMIC_ADD ;
                 AXI_ATOMIC_CLR   : mem_wr_vif.amo_op = MEM_ATOMIC_CLR ;
                 AXI_ATOMIC_EOR   : mem_wr_vif.amo_op = MEM_ATOMIC_SET ;
                 AXI_ATOMIC_SET   : mem_wr_vif.amo_op = MEM_ATOMIC_EOR ;
                 AXI_ATOMIC_SMAX  : mem_wr_vif.amo_op = MEM_ATOMIC_SMAX;
                 AXI_ATOMIC_SMIN  : mem_wr_vif.amo_op = MEM_ATOMIC_SMIN;
                 AXI_ATOMIC_UMAX  : mem_wr_vif.amo_op = MEM_ATOMIC_UMAX;
                 AXI_ATOMIC_UMIN  : mem_wr_vif.amo_op = MEM_ATOMIC_UMIN;
               endcase              
             end
             AXI_ATOMIC_OTHERS : begin
               // Requires a read response 
               mem_wr_vif.req_amo = 1;  
               mem_wr_vif.req_wrn = 0;
               case(req.aw_chan.atop[3:0])
                 AXI_ATOMIC_SWAP : mem_wr_vif.amo_op = MEM_ATOMIC_SWAP;
                 AXI_ATOMIC_CMP  : mem_wr_vif.amo_op = MEM_ATOMIC_CMP;                
               endcase
               q_num_ar_chan_req[req.aw_chan.id].push_back(0);
             end

           endcase
  
           if(req.aw_chan.lock == 1) begin 
             mem_wr_vif.amo_op    = MEM_ATOMIC_STEX;
             mem_rd_vif.req_amo   = 1;
           end
           do begin
             @ (posedge mem_wr_vif.clk);
           end while (mem_wr_vif.req_ready == 1'b0);
       //   end // for 
           mem_wr_vif.req_valid = 1'b0;
         end
       end
    endtask


    // --------------------------------------²------------------
    // get
    // Drive this to memory response model 
    // --------------------------------------------------------
    virtual task write_ar_chan_fifo();
       aw_ar_chan_t req;

       forever begin
         @ (posedge axi_vif.clk);
         if(axi_vif.ar_ready && axi_vif.ar_valid ) begin
             req.addr   = axi_vif.ar_addr   ;
             req.len    = axi_vif.ar_len    ;
             req.size   = axi_vif.ar_size   ;
          //   req.atop   = axi_vif.ar_atop   ;
             req.id     = axi_vif.ar_id     ;
             req.burst  = axi_vif.ar_burst  ;
             req.lock   = axi_vif.ar_lock   ;
             req.cache  = axi_vif.ar_cache  ;
             req.prot   = axi_vif.ar_prot   ;
             req.qos    = axi_vif.ar_qos    ;
             req.region = axi_vif.ar_region ;
             req.user   = axi_vif.ar_user   ;
           
             mb_ar_chan.push_back(req);
             q_num_ar_chan_req[axi_vif.ar_id].push_back(req);
             `uvm_info("AXI2MEM AR CHAN REQ", $sformatf("ADDR %0x(x) ID %0x(x)", req.addr, req.id), UVM_HIGH);
         end
       end
    endtask

    // -------------------------------------------------
    // Get the request from mb_ar_fifo 
    // Convert the request to memory rsp model 
    // Calculate the addr in the case of burst (len > 0) 
    // Get the strb (it is used in the case of exclusive accès to fix the
    // reservation ) 
    // -------------------------------------------------
    virtual task convert_ar_chan_to_mem_req( );
       aw_ar_chan_t req;
       bit [w_addr - 1:0] start_addr; 
       bit [w_addr - 1:0] aligned_addr; 
       int unsigned       num_bytes; 
       int unsigned       burst_length;
       int unsigned       lower_byte_lane;
       int unsigned       upper_byte_lane;
       int unsigned       wd_strb;
       // -----------------------
       // Drive mem iterface
       // -----------------------
       mem_rd_vif.req_valid       = 1'b0;

       forever begin

         if(mb_ar_chan.size() == 0) begin 
           @ (posedge mem_rd_vif.clk); 
         end else begin

           req          = mb_ar_chan.pop_front();

           // --------------------------------------------------------
           // Calculate request addr in the case of burst (len > 0)
           // --------------------------------------------------------
           num_bytes    = 2**req.size;
           burst_length = req.len + 1;
           start_addr   = req.addr;
           aligned_addr = (start_addr/num_bytes)*num_bytes; 
           wd_strb      = w_data/8;

           for (int i = 0; i <= req.len; i++) begin

             mem_rd_vif.req_valid     = 1'b1;
             mem_rd_vif.req_wrn       = 1'b1;
             mem_rd_vif.req_id        = req.id ;
             mem_rd_vif.src_id        = req.id ;
             mem_rd_vif.req_data      = 'h0;
             mem_rd_vif.req_amo       = 0;

             case(req.burst)
              BURST_INCR  : mem_rd_vif.req_addr  = (i == 0)? start_addr : (aligned_addr + i * num_bytes);
              BURST_FIXED : mem_rd_vif.req_addr  = start_addr;
              default     : mem_rd_vif.req_addr  = start_addr; // FIXME: Add other options 
             endcase
           
             // ------------------------------------------
             // In the case of Burst = INCR
             // ------------------------------------------
             if(i == 0) begin
               lower_byte_lane = start_addr - (start_addr / wd_strb) * wd_strb;
               upper_byte_lane = aligned_addr + (num_bytes - 1) - ((start_addr / wd_strb) * wd_strb);
             end else begin
               lower_byte_lane = (aligned_addr + (i - 1) * num_bytes) - (start_addr / wd_strb) * wd_strb;
               upper_byte_lane = lower_byte_lane + num_bytes - 1;
             end


             // ----------------
             // Get the strb
             // ----------------
             mem_rd_vif.req_strb = 'h0;
             for(int i = lower_byte_lane; i <= upper_byte_lane; i++) mem_rd_vif.req_strb[i] = 1; 
   
             if(req.lock == 1) begin 
               mem_rd_vif.amo_op        = MEM_ATOMIC_LDEX;
               mem_rd_vif.req_amo       = 1;
             end


             do begin
               @ (posedge mem_rd_vif.clk);
             end while (mem_rd_vif.req_ready == 1'b0);

             mem_rd_vif.req_valid = 1'b0;
           end // for
         end
       end
    endtask

    // --------------------------------------²------------------
    // B CHAN put
    // Construct the AXI response from memory interface
    //
    // --------------------------------------------------------
    virtual task write_b_chan_fifo( );
       // Drive axi iterface
       b_chan_t        rsp;
       int             cnt;
       int             err_cnt;
       int             ex_fail_cnt;
       aw_ar_chan_t    req;
       cnt     = 0; 
       err_cnt = 0;
       ex_fail_cnt = 0;
       forever begin
         @ (posedge mem_wr_vif.clk);
         if(mem_wr_vif.wr_res_valid) begin

           // ------------------------------------------------------
           // In a burst there could be multiple error responses  
           // ------------------------------------------------------
           if(mem_wr_vif.wr_res_err== 1) err_cnt++;
           if(mem_wr_vif.wr_res_ex_fail == 1) ex_fail_cnt++;

           // ------------------------------------------------------
           // First response: Get the request 
           // ------------------------------------------------------
           if(cnt == 0) begin
             req = q_num_aw_chan_req[mem_wr_vif.wr_res_id].pop_front;
           end 

           // ------------------------------------------------------
           // Error response 
           // Depending on the status of exclusive accès 
           // ------------------------------------------------------
           if(req.lock == 1) begin
             if(err_cnt == 0 && ex_fail_cnt == 0) begin
               rsp.resp = RESP_EXOKAY;
             end else if(err_cnt == 0 && ex_fail_cnt == 1) begin
               rsp.resp = RESP_OKAY;
             end else if(err_cnt == 1) begin
               rsp.resp = RESP_SLVERR;
             end 
           end else begin 
             if(err_cnt == 0) begin
               rsp.resp = RESP_OKAY;
             end else begin
               rsp.resp = RESP_SLVERR;
             end
           end

           rsp.id   = mem_wr_vif.wr_res_id;
           rsp.user = req.user;

           // ------------------------------------------------------
           // check if the last response is received from the memory
           // ------------------------------------------------------
           if(req.len == cnt) begin
             cnt     = 0;
             err_cnt = 0;
             ex_fail_cnt = 0;
             mb_b_chan.push_back(rsp);
           end else begin
             cnt++;
           end



         end // if
       end
    endtask

    // --------------------------------------²------------------
    // B CHAN get
    // 
    // --------------------------------------------------------
    virtual task convert_b_chan_to_mem_intf( );
       // Drive axi iterface
       b_chan_t        rsp;
       forever begin
         if(mb_b_chan.size() == 0) begin
           @ (posedge axi_vif.clk);
         end else begin
           rsp = mb_b_chan.pop_front();

           axi_vif.b_id        = rsp.id; 
           axi_vif.b_resp      = rsp.resp; 
           axi_vif.b_user      = rsp.user;

           axi_vif.b_valid  = 1'b1;

           do begin
             @ (posedge axi_vif.clk);
           end while (axi_vif.b_ready == 1'b0);

           axi_vif.b_valid  = 1'b0;
         end
       end
    endtask

    // ----------------------------------
    // R CHAN FIFO
    // In the case of burst (len > 0) 
    // send multiple responses 
    // ----------------------------------
    virtual task write_r_chan_fifo( );
       aw_ar_chan_t    ar_req[integer]; 
       r_chan_t         req;
       r_chan_t         q_rsp[integer][$];
       int              cnt[integer];
       // Drive axi iterface
       forever begin
          @ (posedge mem_rd_vif.clk);
          if(mem_rd_vif.rd_res_valid ) begin

            req.data        =  mem_rd_vif.rd_res_data;
            req.id          =  mem_rd_vif.rd_res_id;

            if(!cnt.exists(req.id)) cnt[req.id] = 0;
            if(cnt[req.id] == 0) begin
              ar_req[req.id] = q_num_ar_chan_req[mem_rd_vif.rd_res_id].pop_front();
            end 

            if(cnt[req.id] == ar_req[req.id].len) begin 
              req.last = 1;
              cnt[req.id] = 0; 
            end else begin
              req.last = 0; 
              cnt[req.id]++; 
            end

            if(ar_req[req.id].lock == 1) begin
              if(mem_rd_vif.rd_res_err == 0 && mem_rd_vif.rd_res_ex_fail == 0) begin
                req.resp = RESP_EXOKAY;
              end 
              else if(mem_rd_vif.rd_res_err == 0 && mem_rd_vif.rd_res_ex_fail == 1) begin
                req.resp = RESP_OKAY;
              end 
              else if(mem_rd_vif.rd_res_err == 1) begin
                req.resp = RESP_SLVERR;
              end 
            end
            else begin 
              if(mem_rd_vif.rd_res_err == 0) begin
                req.resp = RESP_OKAY;
              end else begin
                req.resp = RESP_SLVERR;
              end
            end


            req.user        =  'h0;
 
            q_rsp[req.id].push_back(req);

            if(req.last == 1) begin
              while(q_rsp[req.id].size() > 0) begin
                mb_r_chan.push_back(q_rsp[req.id].pop_front());
              end 
            end // last

          end // if mem_req_valid

       end
    endtask

    // --------------------------------------²------------------
    // B CHAN get
    // 
    // --------------------------------------------------------
    virtual task convert_r_chan_to_mem_intf( );
       // Drive axi iterface
       r_chan_t        rsp;
       forever begin
         if( mb_r_chan.size() == 0) begin 
           @ (posedge axi_vif.clk);
         end else begin
           rsp =  mb_r_chan.pop_front();

           axi_vif.r_id        = rsp.id; 
           axi_vif.r_data      = rsp.data; 
           axi_vif.r_resp      = rsp.resp; 
           axi_vif.r_user      = rsp.user;
           axi_vif.r_last      = rsp.last;

           axi_vif.r_valid  = 1'b1;

           do begin
             @ (posedge axi_vif.clk);
           end while (axi_vif.r_ready == 1'b0);

           axi_vif.r_valid  = 1'b0;
         end
       end
    endtask


endclass
