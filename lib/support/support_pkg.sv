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
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

`ifndef __SUPPORT_PKG_SV__
`define __SUPPORT_PKG_SV__

//TODO: krdosvik, change name to isa_disassembler when no outstanding PR
package support_pkg;
  `include "isa_constants.sv"
  `include "isa_typedefs.sv"
  `include "isa_typedefs_csr.sv"
  `include "isa_support.sv"
  `include "isa_utility.sv"
endpackage

`endif // __SUPPORT_PKG_SV__

