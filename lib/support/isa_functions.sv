// Copyright 2023 Silicon Labs, Inc.
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

// -------------------------------------------------------------------
// This file holds functions related to the ISA
// -------------------------------------------------------------------

  `include "isa_constants.sv"
  `include "isa_constants_csr.sv"
  `include "isa_tdefs.sv"
  `include "isa_tdefs_csr.sv"
  `include "isa_support.sv" //TODO: krdosvik, change name to isa_disassembler when no outstanding PR


  //TODO: krdosvik, add function when A disassembler PR is in.