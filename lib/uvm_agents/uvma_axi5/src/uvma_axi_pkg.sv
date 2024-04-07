// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group
// Co-Author: Abdelaali Khardazi

/***** AXI4 slave agent package *****/

`ifndef __UVMA_AXI_PKG_SV__
`define __UVMA_AXI_PKG_SV__

// Pre-processor macros
`include "uvm_macros.svh"


// Interfaces / Modules / Checkers
`include "uvma_axi_aw_assert.sv"
`include "uvma_axi_w_assert.sv"
`include "uvma_axi_ar_assert.sv"
`include "uvma_axi_r_assert.sv"
`include "uvma_axi_b_assert.sv"
`include "uvma_axi_assert.sv"
`include "uvma_axi_amo_assert.sv"

package uvma_axi_pkg;

   import uvm_pkg::*;
   import uvml_mem_pkg  ::*;
   import uvml_trn_pkg  ::*;
   import uvml_logs_pkg ::*;

   // Package Parameters
   parameter int MAX_NB_TXN_BURST = 256 ; // Maximum value from the protocol

   parameter int MAX_ID_WIDTH   = 64   ; // subjective maximum
   parameter int MAX_ADDR_WIDTH = 64   ; // subjective maximum
   parameter int MAX_DATA_WIDTH = 64   ; // subjective maximum
   parameter int MAX_USER_WIDTH = 512  ; // subjective maximum

   parameter int MAX_LOOP_WIDTH    = 8  ; // Maximum from the protocol
   parameter int MAX_MMUSID_WIDTH  = 32 ; // Maximum from the protocol
   parameter int MAX_MMUSSID_WIDTH = 20 ; // Maximum from the protocol

   `include "uvma_axi_tdefs.sv"

   `include "uvma_axi_transaction_cfg.sv"
   `include "uvma_axi_transaction.sv"

    // Objects
   `include "uvma_axi_cfg.sv"
   `include "uvma_axi_cntxt.sv"

   `include "uvma_axi_seq_item_logger.sv"

   `include "uvma_axi_synchronizer.sv"
   `include "uvma_axi_amo_synchronizer.sv"

   `include "uvma_axi_vsqr.sv"
   `include "uvma_axi_drv.sv"
   `include "uvma_axi_mon.sv"
   `include "uvma_axi_covg.sv"
   `include "uvma_axi_agent.sv"

    // Sequences
   `include "uvma_axi_seq_lib.sv"

endpackage : uvma_axi_pkg

`endif
