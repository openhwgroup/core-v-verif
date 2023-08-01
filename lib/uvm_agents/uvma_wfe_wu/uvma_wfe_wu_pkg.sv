//
// Copyright 2023 Silicon Labs Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//


`ifndef __UVMA_WFE_WU_PKG_SV__
`define __UVMA_WFE_WU_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_hrtbt_macros.sv"
`include "uvma_wfe_wu_macros.sv"

// Interface(s) / Module(s) / Checker(s)
`include "uvma_wfe_wu_if.sv"
`ifdef UVMA_WFE_WU_INC_IF_CHK
`include "uvma_wfe_wu_if_chk.sv"
`endif


/**
 * Encapsulates all the types needed for an UVM agent capable of driving and/or
 * monitoring wfe wakeup.
 */
package uvma_wfe_wu_pkg;

   import uvm_pkg       ::*;
   import uvml_hrtbt_pkg::*;
   import uvml_trn_pkg  ::*;
   import uvml_logs_pkg ::*;

   // Constants / Structs / Enums
   `include "uvma_wfe_wu_constants.sv"
   `include "uvma_wfe_wu_tdefs.sv"

   // Objects
   `include "uvma_wfe_wu_cfg.sv"
   `include "uvma_wfe_wu_cntxt.sv"

   // High-level transactions
   `include "uvma_wfe_wu_mon_trn.sv"
   `include "uvma_wfe_wu_mon_trn_logger.sv"
   `include "uvma_wfe_wu_seq_item.sv"
   `include "uvma_wfe_wu_seq_item_logger.sv"

   // Agent components
   `include "uvma_wfe_wu_cov_model.sv"
   `include "uvma_wfe_wu_drv.sv"
   `include "uvma_wfe_wu_mon.sv"
   `include "uvma_wfe_wu_sqr.sv"
   `include "uvma_wfe_wu_agent.sv"

   // Sequences
   `include "uvma_wfe_wu_base_seq.sv"
   `include "uvma_wfe_wu_seq_lib.sv"

endpackage : uvma_wfe_wu_pkg


`endif // __UVMA_WFE_WU_PKG_SV__

