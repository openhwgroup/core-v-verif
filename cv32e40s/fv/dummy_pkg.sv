// TODO:silabs-robin  Delete this file, make core-v-verif files fv compatible.


// Copyright 2022 Silicon Labs, Inc.
// Copyright 2022 OpenHW Group
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
// SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0


// Defines

`include "uvma_obi_memory_macros.sv"


// Packages

package uvmt_cv32e40s_pkg;
  `include "uvmt_cv32e40s_constants.sv"
  `include "uvmt_cv32e40s_tdefs.sv"

  import cv32e40s_pkg::*;
endpackage

package uvme_cv32e40s_pkg;
  `include "uvme_cv32e40s_constants.sv"
endpackage

package uvma_rvfi_pkg;
  `include "uvma_rvfi_constants.sv"
  `include "uvma_rvfi_tdefs.sv"
endpackage

package uvma_fencei_pkg;
endpackage


// Interfaces

interface uvma_clknrst_if_t;
  logic  clk;
  logic  reset_n;
endinterface : uvma_clknrst_if_t


// Modules


// Fin
