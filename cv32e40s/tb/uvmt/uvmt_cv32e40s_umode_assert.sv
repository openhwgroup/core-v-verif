// Copyright 2022 OpenHW Group
// Copyright 2022 Silicon Labs, Inc.
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


module  uvmt_cv32e40s_umode_assert
  import uvm_pkg::*;
(
  input  clk_i,
  input  rst_ni,

  input        rvfi_valid,
  input [ 2:0] rvfi_mode,
  input [63:0] rvfi_order,

  input [31:0] rvfi_csr_misa_rdata,
  input [31:0] rvfi_csr_mscratch_rdata,
  input [31:0] rvfi_csr_mscratch_rmask,
  input [31:0] rvfi_csr_mscratch_wdata,
  input [31:0] rvfi_csr_mscratch_wmask,
  input [31:0] rvfi_csr_mstatus_rdata
);

  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;

  string info_tag = "CV32E40S_UMODE_ASSERT";

  localparam int MISA_U_POS = 20;
  localparam int MISA_S_POS = 18;
  localparam int MISA_N_POS = 13;

  localparam int MPP_POS = 11;
  localparam int MPP_LEN =  2;

  localparam int MODE_U = 2'b 00;
  localparam int MODE_M = 2'b 11;


  a_misa_bits: assert property (
    rvfi_valid
    |->
     rvfi_csr_misa_rdata[MISA_U_POS] &&
    !rvfi_csr_misa_rdata[MISA_S_POS] &&
    !rvfi_csr_misa_rdata[MISA_N_POS]
  ) else `uvm_error(info_tag, "misa has wrong extension bits");

  a_no_unsupported_modes: assert property (
    rvfi_valid
    |->
    (rvfi_mode inside {MODE_U, MODE_M})
  ) else `uvm_error(info_tag, "non-supported privilege level executed");
  cov_umode: cover property (
    rvfi_valid && (rvfi_mode == MODE_U)
  );
  cov_mmode: cover property (
    rvfi_valid && (rvfi_mode == MODE_M)
  );

  a_initial_mode: assert property (
    rvfi_valid && (rvfi_order inside {0, 1})  // TODO:ropeders use "rst_ni" instead of "rvfi_order"?
    |->
    (rvfi_mode == MODE_M)
  ) else `uvm_error(info_tag, "priv mode out of reset should be machine-mode");

  a_mscratch_reliable: assert property (
    rvfi_valid && (rvfi_mode == MODE_U)
    |->
    (rvfi_csr_mscratch_wmask == 'd 0)
    // TODO:ropeders what about "mscratchcsw" and "mscratchcswl" too?
  ) else `uvm_error(info_tag, "mscratch should not change in user-mode");
  cov_mscratch_changing: cover property (
    rvfi_valid  &&
    (rvfi_csr_mscratch_wmask != 'd 0)
  );

  a_mpp_mode: assert property (
    rvfi_valid
    |->
    rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] inside {MODE_M, MODE_U}
    // TODO:ropeders sufficient with just "rdata" or need "wdata & wmask" too?
  ) else `uvm_error(info_tag, "mpp can only hold user- and machine-mode");
  cov_mpp_mmode: cover property (
    rvfi_valid  &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] == MODE_M)
  );
  cov_mpp_umode: cover property (
    rvfi_valid  &&
    (rvfi_csr_mstatus_rdata[MPP_POS+:MPP_LEN] == MODE_U)
  );

endmodule : uvmt_cv32e40s_umode_assert
