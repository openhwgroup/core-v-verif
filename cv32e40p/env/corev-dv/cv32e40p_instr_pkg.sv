//
// Copyright 2023 OpenHW Group
// Copyright 2023 Dolphin Design
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
//****************************************************************************************************************


package cv32e40p_instr_pkg;

 typedef enum bit [11:0] {
    // User Custom CSRs
    LPSTART0        = 'hCC0,  // Hardware Loop 0 Start
    LPEND0          = 'hCC1,  // Hardware Loop 0 End
    LPCOUNT0        = 'hCC2,  // Hardware Loop 0 Counter
    LPSTART1        = 'hCC4,  // Hardware Loop 1 Start
    LPEND1          = 'hCC5,  // Hardware Loop 1 End
    LPCOUNT1        = 'hCC6,  // Hardware Loop 1 Counter
    UHARTID         = 'hCD0,  // Hardware Thread ID
    PRIVLV          = 'hCD1,  // Privilege Level
    ZFINX           = 'hCD2   // ZFINX ISA
  } custom_csr_reg_t;

endpackage
