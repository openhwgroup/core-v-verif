// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_RESP_ITEM_SV__
`define __UVMA_CVXIF_RESP_ITEM_SV__


/**
 * Object rebuilt from the CVXIF monitor
 */

class uvma_cvxif_resp_item_c extends uvm_sequence_item;

   rand x_compressed_resp_t   compressed_resp;
   rand x_issue_resp_t        issue_resp;
   rand x_result_t            result;

   rand logic                 issue_ready;
   rand logic                 compressed_ready;
   rand logic                 register_ready;
   rand logic                 result_valid;

   rand logic                 delay_resp;

   logic                      compressed_valid;
   logic                      issue_valid;

   `uvm_object_utils(uvma_cvxif_resp_item_c)

   /**
    * Default constructor.
   */
   extern function new(string name="uvma_cvxif_resp_item");

endclass : uvma_cvxif_resp_item_c

function uvma_cvxif_resp_item_c::new(string name="uvma_cvxif_resp_item");

   super.new(name);

endfunction : new


`endif //__UVMA_CVXIF_RESP_ITEM_SV__

