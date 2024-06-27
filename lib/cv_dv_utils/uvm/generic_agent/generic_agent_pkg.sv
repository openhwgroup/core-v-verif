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

package generic_agent_pkg;
  timeunit 1ns;
  timeprecision 1ps;
 
import uvm_pkg::*;
`include "uvm_macros.svh"

   `include "generic_txn.svh" 
   `include "generic_driver.svh"
   `include "generic_sequencer.svh"
   `include "generic_sequences.svh"
   `include "generic_monitor.svh"
   `include "generic_agent.svh" 
endpackage
