// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_INTF_SV__
`define __UVMA_CVXIF_INTF_SV__


//CoreV-X-Interface v1.0.0
interface uvma_cvxif_intf (

  input logic  clk,
  input logic  reset_n);

   import uvma_cvxif_pkg::*;

   x_compressed_req_t    compressed_req;
   x_issue_req_t         issue_req;
   x_commit_t            commit_req;
   x_register_t          register;

   x_compressed_resp_t   compressed_resp;
   x_issue_resp_t        issue_resp;
   x_result_t            result;

   logic                 issue_ready;
   logic                 compressed_ready;
   logic                 register_ready;
   logic                 result_valid;

   logic                 issue_valid;
   logic                 compressed_valid;
   logic                 register_valid;
   logic                 commit_valid;
   logic                 result_ready;

   /**
    * cvxif clocking block
   */
   clocking slv_cvxif_cb @(posedge clk or reset_n);
      input  issue_req, compressed_req, commit_req, register, issue_valid, register_valid, commit_valid, compressed_valid, result_ready;
      output issue_resp, compressed_resp, result, issue_ready, register_ready, compressed_ready, result_valid;
   endclocking : slv_cvxif_cb

endinterface;


`endif //__UVMA_CVXIF_INTF_SV__
