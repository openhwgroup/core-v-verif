//
// Copyright 2023 OpenHW Group
// Copyright 2023 Datum Technology Corporation
//
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
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


`ifndef __UVMC_RVFI_SB_PKG_SV__
`define __UVMC_RVFI_SB_PKG_SV__

// Pre-processor macros
`include "uvm_macros.svh"

package uvmc_rvfi_scoreboard_pkg;

  import uvm_pkg       ::*;
  import uvml_hrtbt_pkg::*;
  import uvml_trn_pkg  ::*;
  import uvml_logs_pkg ::*;
  import uvma_core_cntrl_pkg::*;
  import uvmc_rvfi_reference_model_pkg::*;
  import uvma_rvfi_pkg::*;

   // DPI imports
  `include "dpi_dasm_imports.svh"

  `include "uvma_rvfi_constants.sv"
  `include "uvma_rvfi_tdefs.sv"
  `include "uvmc_rvfi_scoreboard_utils.sv"
  `include "uvmc_rvfi_scoreboard.sv"

endpackage : uvmc_rvfi_scoreboard_pkg


`endif // __UVM_RVFI_SB_PKG_SV__
