//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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

module uvmt_cv32e40s_zc_assert
  import uvm_pkg::*;
  import uvma_rvfi_pkg::*;
  import cv32e40s_pkg::*;
  (
      uvma_rvfi_instr_if rvfi
  );


  // ---------------------------------------------------------------------------
  // Local parameters
  // ---------------------------------------------------------------------------
  //localparam WFI_INSTR_MASK     = 32'h ffff_ffff;

  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------
  string info_tag = "CV32E40S_ZC_ASSERT";
  //logic [31:0] pc_at_dbg_req; // Capture PC when debug_req_i or ebreak is active


  // ---------------------------------------------------------------------------
  // Clocking blocks
  // ---------------------------------------------------------------------------

  // Single clock, single reset design, use default clocking
  default clocking @(posedge rvfi.clk); endclocking
  default disable iff !(rvfi.reset_n);


    // ---------------------------------------
    // Assertions
    // ---------------------------------------



endmodule : uvmt_cv32e40s_zc_assert
