// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)

/**
 * Encapsulates assertions targeting uvma_cvxif_intf.
 */
module uvma_cvxif_assert #(int unsigned X_HARTID_WIDTH = 32, int unsigned X_ID_WIDTH = 3, int unsigned X_NUM_RS = 3)
   (uvma_cvxif_intf cvxif_assert,
    input logic clk,
    input logic reset_n
   );

   import uvm_pkg::*;

   // ---------------------------------------------------------------------------
    // Local variables
   // ---------------------------------------------------------------------------
   string info_tag = "CVXIF_ASSERT";

   /**
    * Compressed interface
   */

   // Check that offload only compressed instruction on compressed interface
   property CVXIF_COMPRESSED_INSTR;
      @(posedge cvxif_assert.clk) disable iff (!cvxif_assert.reset_n) cvxif_assert.compressed_valid |-> cvxif_assert.compressed_req.instr[1:0] != 2'b11;
   endproperty

   // Check that co-pro reject uncompressed instruction on the compressed interface
   property CVXIF_REJECT_COMPRESSED_REQ;
      @(posedge cvxif_assert.clk) disable iff (!cvxif_assert.reset_n)
      (cvxif_assert.compressed_valid && cvxif_assert.compressed_ready && cvxif_assert.compressed_req.instr[1:0] == 2'b11) |-> !cvxif_assert.compressed_resp.accept;
   endproperty

   // Check that during an compressed request transaction, "instr", "hartid" signal should remain stable
   property CVXIF_STABLE_COMPRESSED_REQ;
      @(posedge cvxif_assert.clk) disable iff (!cvxif_assert.reset_n)
      (cvxif_assert.compressed_valid && !cvxif_assert.compressed_ready) |=> ($stable(cvxif_assert.compressed_req.instr) && $stable(cvxif_assert.compressed_req.hartid));
   endproperty

   // Check that compressed interface respond with an uncompressed instruction
   property CVXIF_UNCOMPRESSED_RESP;
      @(posedge cvxif_assert.clk) disable iff (!cvxif_assert.reset_n)
      (cvxif_assert.compressed_valid && cvxif_assert.compressed_ready && cvxif_assert.compressed_resp.accept) |-> cvxif_assert.compressed_resp.instr[1:0] == 2'b11;
   endproperty

/********************************************** Assert Property ******************************************************/

   compressed_instr               : assert property (CVXIF_COMPRESSED_INSTR)
                                       else `uvm_error (info_tag , "Violation: UNVALID COMPRESSED INSTRUCTION");

   compressed_req_rejected        : assert property (CVXIF_REJECT_COMPRESSED_REQ)
                                       else `uvm_error (info_tag , "Violation: UNVALID 16-BIT INSTRUCTION");

   compressed_req_stable          : assert property (CVXIF_STABLE_COMPRESSED_REQ)
                                       else `uvm_error (info_tag , "Violation: COMPRESSED REQUEST PACKET IS NOT STABLE DURING A COMPRESSED TRANSACTION");

   uncompressed_resp              : assert property (CVXIF_UNCOMPRESSED_RESP)
                                       else `uvm_error (info_tag , "Violation: UNVALID 32-BIT INSTRUCTION IN RESPONSE");

/********************************************** Cover Property ******************************************************/

   cov_compressed_instr           : cover property(CVXIF_COMPRESSED_INSTR);

   cov_reject_uncompressed        : cover property(CVXIF_REJECT_COMPRESSED_REQ);

   cov_compressed_stable          : cover property(CVXIF_STABLE_COMPRESSED_REQ);

   cov_uncompressed_resp          : cover property(CVXIF_UNCOMPRESSED_RESP);

   /**
    * Issue interface
   */

   // Check that if a transaction is rejected, all x_issue_resp signals shall be deasserted
   property CVXIF_REJECT_ISSUE_REQ;
      @(posedge cvxif_assert.clk) disable iff (!cvxif_assert.reset_n)
      (cvxif_assert.issue_valid && cvxif_assert.issue_ready && !cvxif_assert.issue_resp.accept) |-> (!cvxif_assert.issue_resp.writeback && !cvxif_assert.issue_resp.register_read);
   endproperty

   // Check that during an issue request transaction, the "instr", "hartid" and "id" signals should remain stable
   property CVXIF_STABLE_ISSUE_REQ;
      @(posedge cvxif_assert.clk) disable iff (!cvxif_assert.reset_n)
      (cvxif_assert.issue_valid && !cvxif_assert.issue_ready) |=> ($stable(cvxif_assert.issue_req.instr) && $stable(cvxif_assert.issue_req.hartid) && $stable(cvxif_assert.issue_req.id));
   endproperty

   // Check that during an issue request transaction, each bit of "rs_valid" not allowed to transition back to 0
   property CVXIF_RS_VALID(i);
      @(posedge cvxif_assert.clk) disable iff (!cvxif_assert.reset_n)
      (cvxif_assert.issue_valid && !cvxif_assert.issue_ready) |=> !($fell(cvxif_assert.register.rs_valid[i]));
   endproperty

/********************************************** Assert Property ******************************************************/

   reject_issue_req                 : assert property (CVXIF_REJECT_ISSUE_REQ)
                                         else `uvm_error (info_tag , "Violation: ISSUE RESP PACKET IS NOT DEASSERTED AFTER REJECTING ISSUE TRANSACTION");

   issue_req_stable                 : assert property (CVXIF_STABLE_ISSUE_REQ)
                                         else `uvm_error (info_tag , "Violation: ISSUE REQ PACKET IS NOT STABLE DURING AN ISSUE TRANSACTION");

   always @(posedge cvxif_assert.clk) begin
       for (int i = 0; i < X_NUM_RS ; i++)  begin
          rs_valid           : assert property (CVXIF_RS_VALID(i))
                                  else `uvm_error (info_tag ,$sformatf("Violation: RS_VALID[%1d] IS NOT ALLOWED TO BACK TO 0 DURING A TRANSACTION", i));
          cov_rs_valid       : cover property (CVXIF_RS_VALID(i)); 
       end
   end

/********************************************** Cover Property ******************************************************/

   cov_reject_issue_req          : cover property(CVXIF_REJECT_ISSUE_REQ);
	      
   cov_stable_issue              : cover property(CVXIF_STABLE_ISSUE_REQ);
					      
   /**
    * Commit_interface
   */

   //Check that "x_commit_valid" shall asserted exactly one cycle for every offloaded instruction by the co-pro (whether accepted or not)
   property CVXIF_COMMIT_VALID_ONE_CYCLE;
      bit [X_HARTID_WIDTH-1:0] hartid;
      bit [X_ID_WIDTH-1:0] id;
      @(posedge cvxif_assert.clk) disable iff (!cvxif_assert.reset_n)
      (cvxif_assert.commit_valid ,id = cvxif_assert.commit_req.id) |=> (cvxif_assert.commit_valid && cvxif_assert.commit_req.id != id) || (!cvxif_assert.commit_valid);
   endproperty

   //Check that a commit transaction shall be present for every transaction
   property CVXIF_COMMIT_FOR_ISSUE;
      bit [X_HARTID_WIDTH-1:0] hartid;
      bit [X_ID_WIDTH-1:0] id;
      @(posedge cvxif_assert.clk) disable iff (!cvxif_assert.reset_n)
      ((cvxif_assert.issue_ready && cvxif_assert.issue_valid), hartid = cvxif_assert.issue_req.hartid, id = cvxif_assert.issue_req.id)
      |-> (##[0:$] (cvxif_assert.commit_valid && cvxif_assert.commit_req.hartid == hartid && cvxif_assert.commit_req.id == id));
   endproperty

/********************************************** Assert Property ******************************************************/

   commit_valid_one_cycle        : assert property (CVXIF_COMMIT_VALID_ONE_CYCLE)
                                      else `uvm_error (info_tag , "Violation: COMMIT_VALID SHOULD BE PRESENT EXCACTLY ONE CYCLE");

   commit_for_issue              : assert property (CVXIF_COMMIT_FOR_ISSUE)
                                      else `uvm_error (info_tag , "Violation: COMMIT TRANSACTION SHALL BE PRESENT FOR EVERY ISSUE TRANSACTION");

/********************************************** Cover Property ******************************************************/

   cov_commit_one_cycle          : cover property(CVXIF_COMMIT_VALID_ONE_CYCLE);

   cov_commit_for_issue          : cover property(CVXIF_COMMIT_FOR_ISSUE);

   /**
    * Result_interface
   */

   //Check that signals in results shall remain stable during a result transaction
   property CVXIF_RESULT_STABLE;
       @(posedge cvxif_assert.clk) disable iff (!cvxif_assert.reset_n)
       (cvxif_assert.result_valid && !cvxif_assert.result_ready) |=>   $stable(cvxif_assert.result.hartid) &&
                                                                       $stable(cvxif_assert.result.id)     &&
                                                                       $stable(cvxif_assert.result.rd)     &&
                                                                       $stable(cvxif_assert.result.data)   &&
                                                                       $stable(cvxif_assert.result.we);
   endproperty

   //Check proper end of result transaction
   property CVXIF_RESULT_END;
       bit [X_ID_WIDTH-1:0] id;
       @(posedge cvxif_assert.clk) disable iff (!cvxif_assert.reset_n)
       (cvxif_assert.result_valid && cvxif_assert.result_ready, id = cvxif_assert.result.id) |=> (cvxif_assert.result_valid && cvxif_assert.result.id != id) || !cvxif_assert.result_valid;
   endproperty

   //Check that result_valid is assserted only if commit_valid is 1 and commit_kill is deasserted
   property CVXIF_RESULT_FOR_COMMIT;
      bit [X_HARTID_WIDTH-1:0] hartid;
      bit [X_ID_WIDTH-1:0] id;
      @(posedge cvxif_assert.clk) disable iff (!cvxif_assert.reset_n)
      (cvxif_assert.commit_valid && !cvxif_assert.commit_req.commit_kill, hartid = cvxif_assert.commit_req.hartid, id = cvxif_assert.commit_req.id)
      |-> ##[0:$] (cvxif_assert.result_valid && hartid == cvxif_assert.result.hartid && id == cvxif_assert.result.id);
   endproperty


/********************************************** Assert Property ******************************************************/

   result_stable                : assert property (CVXIF_RESULT_STABLE)
                                     else `uvm_error (info_tag , "Violation: RESULT PACKET IS NOT STABLE DURING A RESULT TRANSACTION");

   result_trn_end               : assert property (CVXIF_RESULT_END)
                                     else `uvm_error (info_tag , "Violation: RESULT TRANSACTION DID NOT END PROPERLY");

   result_for_commit            : assert property (CVXIF_RESULT_FOR_COMMIT)
                                     else `uvm_error (info_tag , "Violation: RESULT TRANSACTION SHALL BE PRESENT FOR EVERY COMMIT TRANSACTION NOT KILLED");

/********************************************** Cover Property ******************************************************/

   cov_result_stable            : cover property(CVXIF_RESULT_STABLE);

   cov_result_trn_end           : cover property(CVXIF_RESULT_END);

   cov_result_for_commit        : cover property(CVXIF_RESULT_FOR_COMMIT);

endmodule : uvma_cvxif_assert
