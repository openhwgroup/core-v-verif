// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_CFG_SV__
`define __UVMA_CVXIF_CFG_SV__

/**
 * Object encapsulating all parameters for creating, connecting and running all
 * Clock & Reset agent (uvma_cvxif_agent_c) components.
 */
class uvma_cvxif_cfg_c extends uvm_object;

   rand bit                                       enabled_cvxif;
   bit                                            cvxif_plusarg_valid;
   rand bit                                       cov_model_enabled;
   rand int unsigned                              hold_issue_ready;
   rand int unsigned                              hold_issue_not_ready;
   rand int unsigned                              hold_compressed_ready;
   rand int unsigned                              hold_compressed_not_ready;
   rand bit                                       zero_delay_mode;
   rand int unsigned                              instr_delayed;
   rand uvma_cvxif_slv_drv_ordering_mode          ordering_mode;
   rand uvma_cvxif_issue_ready_mode_enum          issue_ready_mode;
   rand uvma_cvxif_compressed_ready_mode_enum     compressed_ready_mode;

   constraint reasonable_values {
      soft hold_issue_ready          inside {[1:2]};
      soft hold_issue_not_ready      inside {[1:2]};
      soft hold_compressed_ready     inside {[1:2]};
      soft hold_compressed_not_ready inside {[1:2]};
      if (zero_delay_mode) {
        instr_delayed == 0;
      }
      else {
        soft instr_delayed inside {[2:4]};
      }
   }

   constraint hold_ready_values {
      hold_issue_ready          != 0;
      hold_compressed_ready     != 0;
   }

   constraint defaults_val {
      soft issue_ready_mode       == UVMA_CVXIF_ISSUE_READY_RANDOMIZED;
      soft compressed_ready_mode  == UVMA_CVXIF_COMPRESSED_READY_FIX;
      soft ordering_mode          == UVMA_CVXIF_ORDERING_MODE_IN_ORDER;
      soft zero_delay_mode        == 1;
      soft cov_model_enabled      == 1;
      soft enabled_cvxif          == 0;
   }

   `uvm_object_utils_begin(uvma_cvxif_cfg_c)
      `uvm_field_int ( cov_model_enabled,              UVM_DEFAULT)
      `uvm_field_int ( enabled_cvxif,                  UVM_DEFAULT)
      `uvm_field_int ( hold_issue_ready,               UVM_DEFAULT)
      `uvm_field_int ( hold_issue_not_ready,           UVM_DEFAULT)
      `uvm_field_int ( hold_compressed_ready,          UVM_DEFAULT)
      `uvm_field_int ( hold_compressed_not_ready,      UVM_DEFAULT)
      `uvm_field_int ( instr_delayed,                  UVM_DEFAULT)
      `uvm_field_int ( zero_delay_mode,                UVM_DEFAULT)
      `uvm_field_enum  (uvma_cvxif_slv_drv_ordering_mode,      ordering_mode, UVM_DEFAULT);
      `uvm_field_enum  (uvma_cvxif_issue_ready_mode_enum,      issue_ready_mode, UVM_DEFAULT);
      `uvm_field_enum  (uvma_cvxif_compressed_ready_mode_enum, compressed_ready_mode, UVM_DEFAULT);
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_cvxif_cfg");

endclass : uvma_cvxif_cfg_c


function uvma_cvxif_cfg_c::new(string name="uvma_cvxif_cfg");

   super.new(name);

   // Read plusargs for defaults
   if ($test$plusargs("enabled_cvxif")) begin
      cvxif_plusarg_valid = 1;
   end

endfunction : new


`endif //__UVMA_CVXIF_CFG_SV__
