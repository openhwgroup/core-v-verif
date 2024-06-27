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
//  Description : generic sequence lib
//              : It is advisable to drive every sequence from signle request/single request in region
// ----------------------------------------------------------------------------
class generic_base_sequence#(type req_t, type rsp_t) extends uvm_sequence #(generic_txn#(req_t, rsp_t));


  `uvm_object_param_utils( generic_base_sequence#(req_t, rsp_t) )

  generic_sequencer  #(req_t, rsp_t)m_sequencer;
  int                num_txn, rsp_count;

  function new( string name = "base_data_txn_sequence" );
    super.new(name);

    if (!$value$plusargs("NB_TXNS=%d", num_txn )) begin
      num_txn = 10000;
    end // if
    `uvm_info( get_full_name(), $sformatf("NUM_TXN=%0d", num_txn), UVM_HIGH );

    use_response_handler(1);
  endfunction: new

  task pre_body();
    $cast(m_sequencer, get_sequencer());
  endtask: pre_body

  virtual task body( );
    super.body();
  endtask

  // The response_handler function serves to keep the sequence response FIFO empty
  function void response_handler(uvm_sequence_item response);
    rsp_count++;
    `uvm_info("generic SEQUENCE BASE", $sformatf("Number of responses %0d(d)", rsp_count), UVM_HIGH);
  endfunction: response_handler

  protected task send_txn( input generic_txn#(req_t, rsp_t)  item);
    generic_txn#(req_t, rsp_t) item_clone;

    if ( !$cast( item_clone, item.clone() ) )
      `uvm_error(this.get_name(),"Error during the cast of the transaction");


      // Start the item
      start_item( item_clone );

      // Send the transction to the driver
      finish_item( item_clone );
  endtask


endclass: generic_base_sequence
