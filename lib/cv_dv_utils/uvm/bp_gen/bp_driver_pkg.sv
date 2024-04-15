// ----------------------------------------------------------------------------
//Copyright 2023 CEA*
//*Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
//
//Licensed under the Apache License, Version 2.0 (the "License");
//you may not use this file except in compliance with the License.
//You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
//Unless required by applicable law or agreed to in writing, software
//distributed under the License is distributed on an "AS IS" BASIS,
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//See the License for the specific language governing permissions and
//limitations under the License.
//[END OF HEADER]
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//  Description : Package containing back pressure generator classes
//                
// 
// ----------------------------------------------------------------------------

package bp_driver_pkg;

   timeunit 1ns;

   import bp_vif_xrtl_pkg::*;
   import uvm_pkg::*;
typedef enum {
    NO_BP,
    HEAVY_BP,
    OCCASSIONAL_BP,
    MOSTLY_BP
} bp_type_t;

   `include "uvm_macros.svh";
   `include "bp_txn.svh";
   `include "bp_driver.svh";
   `include "bp_sequencer.svh";
   `include "bp_sequences.svh";
   `include "bp_virtual_sequence.svh";
   `include "bp_agent.svh";

endpackage : bp_driver_pkg


