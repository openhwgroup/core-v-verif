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
//  Description : Sequencer for generic request
// ----------------------------------------------------------------------------

class generic_sequencer#(type req_t, type rsp_t) extends uvm_sequencer #(generic_txn#(req_t, rsp_t), generic_txn#(req_t, rsp_t));

  `uvm_sequencer_param_utils(generic_sequencer#(req_t, rsp_t))

  // -------------------------------------------------------------------------
  // Constructor
  // -------------------------------------------------------------------------
  function new(string name = "generic_sequencer", uvm_component parent);
      super.new(name, parent);
      
  endfunction: new
  
endclass: generic_sequencer
