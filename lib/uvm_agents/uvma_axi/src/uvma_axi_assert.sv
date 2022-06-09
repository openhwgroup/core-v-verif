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
   bit aw[$];   //Store  the number of write transfer that will be done
   bit w[$];   //Store the number write transfer that is done
   int burst_len[$];   //Store burst len for each burst
   int data_count[$];   //Count write data for each ID
   int wlast_count = 0;   //Count WLast signal
   //Variable for checking assertion coverage
   int cov_w_data_num = 0;
   int cov_w_data_num_not = 0;
   int cov_aw_property = 0;
   int cov_w_property = 0;

   // Check the dependence between the write channels (Section A3.3.1)
   always @ (posedge clk) begin
      if(rst_n) begin
         if(axi_assert.aw_valid && axi_assert.aw_ready) begin
            for(int i = 0; i < axi_assert.aw_len+1; i++) begin
               aw.push_back(1);
            end
         end
         if(axi_assert.w_valid && axi_assert.w_ready) begin
            w_dep_aw : assert(aw.size() != 0) begin
               cov_aw_property++;
            end else begin
               `uvm_error("AXI4 protocol checks assertion", "Violation of w_dep_aw");
               cov_aw_property++;
            end
            aw.pop_back();
         end
	     if(axi_assert.w_last) begin
	        w.push_back(1);
	     end
         if(axi_assert.b_valid && axi_assert.b_ready ) begin
            b_dep_w : assert((w.size() != 0)) begin
               cov_w_property++;
            end else begin
               `uvm_error("AXI4 protocol checks assertion", "Violation of b_dep_w");
               cov_w_property++;
            end
            if (w.size() != 0) begin
               w.pop_back();
            end
         end
      end
   end

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

// *************************** Read Data channel ************************** //

   int ar_id_tr[];   //Store the number of transaction
   int ar_len_tr[][];   //Store the lenght of every burst
   int tab[];
   int ass_ar_id;   //Store ar_id every clock cycle
   int ass_r_id;   //Store ar_id every clock cycle
   int size;   //Store transfer size every clock cycle
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
            end else begin
               `uvm_info("AXI4 protocol checks assertion", "new TR", UVM_HIGH)
               ar_id_tr[ass_ar_id] = ar_id_tr[ass_ar_id] + 1;
               ar_len_tr[ass_ar_id] = new[ar_id_tr[ass_ar_id]] (ar_len_tr[ass_ar_id]);
               ar_len_tr[ass_ar_id][ar_id_tr[ass_ar_id]-1] = signed'(axi_assert.ar_len+1);
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

      `uvm_info("AXI4 protocol checks assertion", $sformatf("coverage w_dep_aw property = %d", cov_aw_property), UVM_HIGH)
      `uvm_info("AXI4 protocol checks assertion", $sformatf("coverage b_dep_w property = %d", cov_w_property), UVM_HIGH)
      `uvm_info("AXI4 protocol checks assertion", $sformatf("coverage cov_w_data_num property = %d", cov_w_data_num), UVM_HIGH)
      `uvm_info("AXI4 protocol checks assertion", $sformatf("coverage cov_w_data_num_not property = %d", cov_w_data_num_not), UVM_HIGH)
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
