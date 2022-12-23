//
// Copyright (c) 2022 Imperas Software Ltd., www.imperas.com
// 
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
// either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.
//
//
 
// SystemVerilog Functional Coverage Available for extensions: 
//   RV32ZCA
//   RV32ZCB
//   RV32ZCBZBB
//   RV32ZCBZMUL
//   RV32ZCMP
//   RV32ZCMT

///////////////////////
// Platform Options  // 
///////////////////////

// Base ISA.  Uncomment one of these:
`define COVER_BASE_RV32I
//`define COVER_BASE_RV32E
//`define COVER_BASE_RV64I
//`define COVER_BASE_RV64E



//////////////////////////
// Select Coverage Level// 
//////////////////////////
// Uncomment one of these (higher cover levels enable lower levels):

// Compliance Basic
//`define COVER_LEVEL_COMPL_BAS

// Compliance Extended
//`define COVER_LEVEL_COMPL_EXT

// DV Un-privileged Basic
//`define COVER_LEVEL_DV_UP_BAS

// DV Un-privileged Extended
//`define COVER_LEVEL_DV_UP_EXT

// DV Privileged Basic
//`define COVER_LEVEL_DV_PR_BAS

// DV Privileged Extended
`define COVER_LEVEL_DV_PR_EXT


//////////////////////
// Select Extensions//
//////////////////////
// Uncomment to enable coverage
`define COVER_RV32ZCA
//`define COVER_RV32ZCA_ILLEGAL
`define COVER_RV32ZCB
//`define COVER_RV32ZCB_ILLEGAL
`define COVER_RV32ZCBZBB
//`define COVER_RV32ZCBZBB_ILLEGAL
`define COVER_RV32ZCBZMUL
//`define COVER_RV32ZCBZMUL_ILLEGAL
`define COVER_RV32ZCMP
//`define COVER_RV32ZCMP_ILLEGAL
`define COVER_RV32ZCMT
//`define COVER_RV32ZCMT_ILLEGAL
 

