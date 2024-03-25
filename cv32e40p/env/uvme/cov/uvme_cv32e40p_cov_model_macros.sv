// Copyright 2024 OpenHW Group
// SPDX-License-Identifier: Apache-2.0 WITH SHL-210
`ifndef __UVMA_CV32E40P_COV_MODEL_MACROS_SV__
`define __UVMA_CV32E40P_COV_MODEL_MACROS_SV__

// Macro to remove instrucitons that are not supported based on standard ext_*_supported variable names (from commmon core control cfg class)
`ifdef UNSUPPORTED_WITH
  `define WITH iff
`else
   `define WITH with
`endif

`endif // __UVMA_CV32E40P_COV_MODEL_MACROS_SV__