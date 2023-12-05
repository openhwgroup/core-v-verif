// ----------------------------------------------------------------------------
// Copyright 2023 CEA*
// *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//[END OF HEADER]
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//  Description : Package for generic reset generator 
//                
// 
// ----------------------------------------------------------------------------

package reset_driver_pkg;

    timeunit 1ns;

    import uvm_pkg::*;

    class dummy_sequence_item_c extends uvm_sequence_item;
    endclass : dummy_sequence_item_c

    class dummy_c extends uvm_sequence #(dummy_sequence_item_c);
    endclass : dummy_c

    `include "uvm_macros.svh";
    `include "reset_driver_c.svh";

endpackage : reset_driver_pkg


