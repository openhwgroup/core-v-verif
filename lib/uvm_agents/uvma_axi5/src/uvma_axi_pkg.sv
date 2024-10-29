// Copyright 2022 Thales DIS SAS
// Copyright 2024 CoreLab Tech
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
`include "uvma_axi_macros.sv"

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
   parameter int MAX_NB_TXN_BURST  = `UVMA_AXI_MAX_NB_TXN_BURST  ; // Maximum value from the protocol

   parameter int MAX_ID_WIDTH      = `UVMA_AXI_ID_MAX_WIDTH      ; // subjective maximum
   parameter int MAX_ADDR_WIDTH    = `UVMA_AXI_ADDR_MAX_WIDTH    ; // subjective maximum
   parameter int MAX_DATA_WIDTH    = `UVMA_AXI_DATA_MAX_WIDTH    ; // subjective maximum
   parameter int MAX_USER_WIDTH    = `UVMA_AXI_USER_MAX_WIDTH    ; // subjective maximum

   parameter int MAX_LOOP_WIDTH    = `UVMA_AXI_LOOP_MAX_WIDTH    ; // Maximum from the protocol
   parameter int MAX_MMUSID_WIDTH  = `UVMA_AXI_MMUSID_MAX_WIDTH  ; // Maximum from the protocol
   parameter int MAX_MMUSSID_WIDTH = `UVMA_AXI_MMUSSID_MAX_WIDTH ; // Maximum from the protocol

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
   `include "uvma_axi_mst_seq.svh"

endpackage : uvma_axi_pkg

`endif
