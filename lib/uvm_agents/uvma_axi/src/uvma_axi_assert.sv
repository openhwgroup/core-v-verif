// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

module  uvma_axi_assert (uvma_axi_intf axi_assert, input bit clk, input rst_n);

   import uvm_pkg::*;

/*** AXI4 protocol checks ***/

//********************************** RESET *********************************** //

   // Check if, During reset, Manager interface drive aw_valid, ar_valid and w_valid LOW (Section A3.1.2)
   property AXI4_RESET ;
     @(posedge clk) !rst_n |-> (!axi_assert.aw_valid && !axi_assert.ar_valid && !axi_assert.w_valid && !axi_assert.b_valid && !axi_assert.r_valid);
   endproperty

   axi_reset                 : assert property (AXI4_RESET)
                         else `uvm_error("AXI4 protocol checks assertion", "Violation of AXI4_RESET");

   cov_axi_reset             : cover property (AXI4_RESET);

// *************************** WRITE DATA CHANNEL ************************** //
   int burst_len[$];   //Store burst len for each burst
   int data_count[$];   //Count write data for each ID
   int wlast_count = 0;   //Count WLast signal
   int burst_resp[];   //Store  the number of response that have to be done
   int aw_ex_tr[];   // Store exclusive read transaction
   int ass_aw_id;   //Store aw_id every clock cycle
   int ass_b_id;   //Store b_id every clock cycle
   int tr_count[$];   // Count the number of write transfer
   int tr_len[$];   // Store the lenght of every transaction
   longint start_add[$];   // Store the address of every transaction
   int tr_size[$];   // Store the size of every transaction
   int burst[$];   // Store the burst type of every transaction
   longint aligned_address;   //The aligned version of the start address
   bit aligned;   // Check whether addr is aligned to nbytes
   int lower_byte_lane;   //The byte lane of the lowest addressed byte of a transfer
   int upper_byte_lane;   //The byte lane of the highest addressed byte of a transfer
   int lower_wrap_boundary;   // The lowest address within a wrapping burst
   int upper_wrap_boundary;   // The highest address within a wrapping burst
   int bus_width;   // The number of byte lanes in the data bus
   int valid_resp[];  //Store  the number of Wlast for each outstanding transaction ID
   //Variable for checking assertion coverage
   int cov_w_data_num = 0;
   int cov_w_data_num_not = 0;
   int cov_errm_wstrb = 0;

   // Check if the number of write data items matches AWLEN for the corresponding address (Section A3.4.1)
   always @(posedge clk) begin
      if(rst_n) begin
         if(axi_assert.aw_valid && axi_assert.aw_ready) begin
            data_count.push_back(0);
            burst_len.push_back(axi_assert.aw_len);
         end
         if(axi_assert.w_valid && axi_assert.w_ready) begin
            data_count[0]++;
            if(burst_len[0] == (data_count[0]-1)) begin
               w_data_num : assert(axi_assert.w_last) begin          // Check if The Master assert the WLAST signal when it is driving the final write transfer in the burst
                  cov_w_data_num++;
               end else begin
                  `uvm_error("AXI4 protocol checks assertion", "Violation of w_data_num");
                  cov_w_data_num++;
               end
               data_count.pop_front();
               burst_len.pop_front();
            end else begin
               w_data_num_not : assert(!axi_assert.w_last) begin     // Check if The Master don't assert the WLAST signal when the WDATA count is not equal to AWLEN
                  cov_w_data_num_not++;
               end else begin
                  `uvm_error("AXI4 protocol checks assertion", "Violation of w_data_num_not");
                  cov_w_data_num_not++;
               end
            end
         end
      end
   end

   always @(posedge clk) begin
      if(rst_n) begin
         if(axi_assert.aw_valid && axi_assert.aw_ready) begin
            ass_aw_id = signed'(axi_assert.aw_id);
            if(ass_aw_id >= burst_resp.size()) begin
               burst_resp = new[ass_aw_id+1] (burst_resp);
               burst_resp[ass_aw_id] = 1;
               valid_resp = new[ass_aw_id+1] (valid_resp);
               if(axi_assert.aw_lock) begin
                  aw_ex_tr = new[ass_aw_id+1] (aw_ex_tr);
                  aw_ex_tr[ass_aw_id] = 1;
               end
            end else begin
               burst_resp[ass_aw_id]++;
               if(axi_assert.aw_lock) begin
                  aw_ex_tr[ass_aw_id] = 1;
               end
            end
         end
         if(axi_assert.w_valid && axi_assert.w_ready) begin
	        if(axi_assert.w_last) begin
	           valid_resp[ass_aw_id]++;
	        end
	     end
         if(axi_assert.b_valid && axi_assert.b_ready) begin
            ass_b_id  = signed'(axi_assert.b_id);
            burst_resp[ass_b_id]--;
            axi4_bresp_timing : assert(valid_resp[ass_b_id] >= 1) else begin  // Check if The Subordinate wait for AWVALID, AWREADY, WVALID,  WREADY and also WLAST to be asserted before asserting BVALID (Section A3.3.1)
               `uvm_error("AXI4 protocol checks assertion", "Violation of axi4_bresp_timing");
            end
            if(axi_assert.b_resp == 1) begin
               axi4_bresp_exokay : assert(aw_ex_tr[ass_b_id] >= 1) begin  // Check if an EXOKAY write response it's given only to an exclusive write access (Section A7.2)
                  aw_ex_tr[ass_b_id]--;
               end else begin
                  `uvm_error("AXI4 protocol checks assertion", "Violation of axi4_bresp_exokay");
               end
            end
         end
      end
   end

   final begin
      foreach(burst_resp[i]) begin
         axi4_bresp_all_done : assert(burst_resp[i] == 0)   // Check if All write transaction addresses are matched with a corresponding buffered response (Section A3.4.5)
         else begin
            `uvm_error("AXI4 protocol checks assertion", "Violation of bresp_all_done");
         end
      end
   end

   // Check if Write strobes is asserted for the correct byte lanes only (Section A3.4.4)
   // The value of the WSTRB depend on the signalled AWSIZE and Start Address

   // In order to determine the values that the Strbs can take, it is necessary
   // to know first the byte lanes that contain the valid data. The burst mode affects
   // these channels and also the address.  See Section A3.4.2 for more explanation
   always @(posedge clk) begin
      if(axi_assert.aw_valid && axi_assert.aw_ready) begin
         tr_count.push_back(0);
         tr_len.push_back(axi_assert.aw_len);
         start_add.push_back(axi_assert.aw_addr);
         tr_size.push_back(2**(axi_assert.aw_size));
         burst.push_back(axi_assert.aw_burst);
         bus_width = $bits(axi_assert.w_strb);
      end
      if(axi_assert.w_valid && axi_assert.w_ready) begin
         tr_count[0]++;
         aligned_address = (int'(start_add[0]/tr_size[0]) * tr_size[0]);
         aligned = (aligned_address == start_add[0]) ? 1 : 0;
         lower_byte_lane = start_add[0] - (int'(start_add[0]/bus_width)) * bus_width;
         if(aligned) begin
            upper_byte_lane = lower_byte_lane + tr_size[0] - 1;
         end else begin
            upper_byte_lane = aligned_address + tr_size[0] - 1 - (int'(start_add[0]/bus_width)) * bus_width;
         end
         for(int i = 0; i < bus_width; i++) begin
            if(i < lower_byte_lane || i > upper_byte_lane) begin
               // Check if strobe bits associated to the lanes that do not contain valid data are equal to zero.
               // For the other bits of the strob can take any value even if it is not compatible with the size of
               // the Transfer (this property it is not mentioned in the spec but it is quoted in a forum on the ARM site)
               axi4_errm_wstrb : assert(axi_assert.w_strb[i] == 0) begin
                  cov_errm_wstrb++;
               end else begin
                  cov_errm_wstrb++;
                  `uvm_error("AXI4 protocol checks assertion", "Violation of axi4_errm_wstrb");
               end
            end
         end
         // All transfers after the first are aligned
         if(burst[0] == 0) begin
            if(!aligned) begin
               start_add[0] = aligned_address;
            end
         end else begin
            // Increment address
            if(aligned) begin
               start_add[0] = start_add[0] + tr_size[0];
               if(burst[0] == 2) begin
                  //addr must be aligned for a wrapping burst
                  lower_wrap_boundary = int'(start_add[0]/tr_size[0]) * tr_size[0] * tr_len[0];
                  upper_wrap_boundary = lower_wrap_boundary + tr_size[0] * tr_len[0];
                  if(start_add[0] >= upper_wrap_boundary) begin
                     start_add[0] = lower_wrap_boundary;
                  end
               end
            end else begin
               start_add[0] = aligned_address + tr_size[0];
            end
         end
         if(tr_len[0] == (tr_count[0]-1)) begin
            tr_count.pop_front();
            tr_len.pop_front();
            start_add.pop_front();
            tr_size.pop_front();
            burst.pop_front();
         end
      end
   end


// *************************** Read Data channel ************************** //

   int ar_id_tr[];   //Store the number of transaction
   int ar_len_tr[][];   //Store the lenght of every burst
   int tab[];
   int ass_ar_id;   //Store ar_id every clock cycle
   int ass_r_id;   //Store ar_id every clock cycle
   int size;   //Store transfer size every clock cycle
   int ar_ex_tr[];   // Store exclusive read transaction
   //Variable for checking assertion coverage
   int cov_r_burst_ter_early;
   int cov_errs_rid_property;
   int cov_r_last_property = 0;

   always @(posedge clk) begin
      if(rst_n) begin
         ass_ar_id = signed'(axi_assert.ar_id);
         size = signed'(ar_id_tr.size());
         if(axi_assert.ar_valid && axi_assert.ar_ready) begin
            if(size <= ass_ar_id) begin
               `uvm_info("AXI4 protocol checks assertion", "new ID", UVM_HIGH)
               ar_id_tr = new[ass_ar_id+1] (ar_id_tr);
               ar_id_tr[ass_ar_id] = 1;
               ar_len_tr = new[ass_ar_id+1] (ar_len_tr);
               ar_len_tr[ass_ar_id] = new[1];
               ar_len_tr[ass_ar_id][0] = signed'(axi_assert.ar_len+1);
               if(axi_assert.ar_lock) begin
                  ar_ex_tr = new[ass_aw_id+1] (aw_ex_tr);
                  ar_ex_tr[ass_aw_id] = 1;
               end
            end else begin
               `uvm_info("AXI4 protocol checks assertion", "new TR", UVM_HIGH)
               ar_id_tr[ass_ar_id] = ar_id_tr[ass_ar_id] + 1;
               ar_len_tr[ass_ar_id] = new[ar_id_tr[ass_ar_id]] (ar_len_tr[ass_ar_id]);
               ar_len_tr[ass_ar_id][ar_id_tr[ass_ar_id]-1] = signed'(axi_assert.ar_len+1);
               if(axi_assert.ar_lock) begin
                  ar_ex_tr[ass_ar_id]++;
               end
            end
         end
         ass_r_id = signed'(axi_assert.r_id);
         if(axi_assert.r_valid) begin
            axi4_errs_rid : assert(ar_len_tr[ass_r_id][0] >= 1) begin   // Check if slave send a read data that follow the address that it relates to (Section A5.2)
               ar_len_tr[ass_r_id][0] = ar_len_tr[ass_r_id][0] - 1;
               cov_errs_rid_property++;
            end else begin
               `uvm_error("AXI4 protocol checks assertion", "Violation of axi4_errs_rid");
               cov_errs_rid_property++;
            end
            if(ar_len_tr[ass_r_id][0] == 0) begin
               r_last_assert : assert(axi_assert.r_last) begin    // Check if The subordinate assert the RLAST signal when it is driving the final read transfer in the burst (Section A3.2.2)
                  cov_r_last_property++;
               end else begin
                  `uvm_error("AXI4 protocol checks assertion", "Violation of r_last_assert");
                  cov_r_last_property++;
               end
               if(axi_assert.r_ready) begin
                  if(axi_assert.r_resp == 1) begin
                     axi4_rresp_exokay : assert(ar_ex_tr[ass_b_id] >= 1) begin // Check if an EXOKAY write response it's given only to an exclusive read access (Section A7.2)
                        ar_ex_tr[ass_r_id]--;
                     end else begin
                        `uvm_error("AXI4 protocol checks assertion", "Violation of axi4_rresp_exokay");
                     end
                  end
                  tab = new[ar_id_tr[ass_r_id]];
                  ar_id_tr[ass_r_id]--;
                  foreach(ar_len_tr[i,j]) begin
                     tab[j] = ar_len_tr[ass_r_id][j];
                  end
                  for(int i = 0; i<tab.size(); i++) begin
                     ar_len_tr[ass_r_id][i] = tab[i+1];
                  end
               end else begin
                  ar_len_tr[ass_r_id][0]++;
               end
            end else begin
               // Check if the read burst not terminate early (Section A3.4.1)
               r_burst_ter_early : assert(!(axi_assert.r_last)) begin
                  cov_r_burst_ter_early++;
               end else begin
                  `uvm_error("AXI4 protocol checks assertion", "Violation of r_burst_ter_early");
                  cov_r_burst_ter_early++;
               end
            end
         end
      end
   end


   final begin
      // Check if all outstanding read bursts have completed (Section A3.4.1)
      foreach(ar_len_tr[i,j]) begin
         axi4_errs_rdata_num : assert(ar_len_tr[i][j] == 0)
         else begin
            `uvm_error("AXI4 protocol checks assertion", "Violation of axi4_errs_rdata_num");
         end
      end

      `uvm_info("AXI4 protocol checks assertion", $sformatf("coverage cov_w_data_num property = %d", cov_w_data_num), UVM_HIGH)
      `uvm_info("AXI4 protocol checks assertion", $sformatf("coverage cov_w_data_num_not property = %d", cov_w_data_num_not), UVM_HIGH)
      `uvm_info("AXI4 protocol checks assertion", $sformatf("coverage cov_errm_wstrb property = %d", cov_errm_wstrb), UVM_HIGH)
      `uvm_info("AXI4 protocol checks assertion", $sformatf("coverage r_last property = %d", cov_r_last_property),UVM_HIGH)
      `uvm_info("AXI4 protocol checks assertion", $sformatf("coverage axi4_errs_rid property = %d", cov_errs_rid_property),UVM_HIGH)
      `uvm_info("AXI4 protocol checks assertion", $sformatf("coverage burst_ter_early property = %d", cov_r_burst_ter_early), UVM_HIGH)
   end

   bind uvma_axi_assert
      uvma_axi_aw_assert         axi_aw_assert(.axi_assert(axi_assert),
                                            .clk(clk),
                                            .rst_n(rst_n)
                                           );

   bind uvma_axi_assert
      uvma_axi_ar_assert         axi_ar_assert(.axi_assert(axi_assert),
                                            .clk(clk),
                                            .rst_n(rst_n)
                                           );

   bind uvma_axi_assert
      uvma_axi_w_assert          axi_w_assert(.axi_assert(axi_assert),
                                            .clk(clk),
                                            .rst_n(rst_n)
                                           );

   bind uvma_axi_assert
      uvma_axi_r_assert          axi_r_assert(.axi_assert(axi_assert),
                                            .clk(clk),
                                            .rst_n(rst_n)
                                           );

   bind uvma_axi_assert
      uvma_axi_b_assert          axi_b_assert(.axi_assert(axi_assert),
                                            .clk(clk),
                                            .rst_n(rst_n)
                                           );

endmodule : uvma_axi_assert
