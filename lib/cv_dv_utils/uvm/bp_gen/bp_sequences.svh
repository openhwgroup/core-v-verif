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
//  Description : This file contains a library of sequences that can
//                be injected on the back-pressure IF.
//
// ----------------------------------------------------------------------------

// Occassional BP Sequence - about 20 %, short BP
class occassional_bp_sequence extends uvm_sequence #( bp_txn );
    `uvm_object_utils( occassional_bp_sequence );


   function new( string name = "occassional_bp_sequence" );
      super.new(name);
   endfunction: new

   virtual task body( );
       bp_txn  m_bp_txn;
       m_bp_txn = bp_txn::type_id::create("bp_txn");

       forever begin
           start_item( m_bp_txn );
           if  (!m_bp_txn.randomize() with {
              m_bp_type dist {    BP_OFF :/ 80,
                                  BP_ON  :/ 20,
                               BP_TOGGLE :/ 0,
                              BP_PERCENT :/ 0 };
              m_N >= 5; 
              m_N <= 30; } ) begin
              `uvm_fatal("body","Randomization failed");
           end // if
           `uvm_info( "BP TXN BEGIN FINISH", m_bp_txn.convert2string, UVM_DEBUG );
           finish_item( m_bp_txn );
       end // forever
   endtask: body

endclass : occassional_bp_sequence

// Heavy BP Sequence - about 20 %, short BP
class heavy_bp_sequence extends uvm_sequence #( bp_txn );
    `uvm_object_utils( heavy_bp_sequence );


   function new( string name = "heavy_bp_sequence" );
      super.new(name);
   endfunction: new

   virtual task body( );
       bp_txn  m_bp_txn;
       m_bp_txn = bp_txn::type_id::create("bp_txn");

       forever begin
           start_item( m_bp_txn );
           if  (!m_bp_txn.randomize() with {
              m_bp_type dist { BP_OFF :/ 50,
                             BP_ON  :/ 50 };
              m_N >= 1; 
              m_N <= 50; } ) begin
              `uvm_fatal("body","Randomization failed");
           end // if
           `uvm_info( "BP TXN BEGIN FINISH", m_bp_txn.convert2string, UVM_DEBUG );
           finish_item( m_bp_txn );
       end // forever
   endtask: body

endclass : heavy_bp_sequence

//
class no_bp_sequence extends uvm_sequence #( bp_txn );
    `uvm_object_utils( no_bp_sequence );


   function new( string name = "no_bp_sequence" );
      super.new(name);
   endfunction: new

   virtual task body( );
       bp_txn  m_bp_txn;
       m_bp_txn = bp_txn::type_id::create("bp_txn");

       forever begin
           start_item( m_bp_txn );
           if  (!m_bp_txn.randomize() with {
              m_bp_type == BP_OFF;
                    m_N == 500; } ) begin
              `uvm_fatal("body","Randomization failed");
           end // if
           `uvm_info( "BP TXN BEGIN FINISH", m_bp_txn.convert2string, UVM_DEBUG );
           finish_item( m_bp_txn );
       end // forever
   endtask: body

endclass : no_bp_sequence

// Heavy BP Sequence - about 20 %, short BP
class mostly_bp_sequence extends uvm_sequence #( bp_txn );
    `uvm_object_utils( mostly_bp_sequence );


   function new( string name = "mostly_bp_sequence" );
      super.new(name);
   endfunction: new

   virtual task body( );
       bp_txn  m_bp_txn;
       m_bp_txn = bp_txn::type_id::create("bp_txn");

       start_item( m_bp_txn );
       if  (!m_bp_txn.randomize() with {
          m_bp_type == BP_OFF;
          m_N >= 1; 
          m_N <= 10; } ) begin
          `uvm_fatal("body","Randomization failed");
       end // if
       finish_item( m_bp_txn );
       forever begin
       start_item( m_bp_txn );
       if  (!m_bp_txn.randomize() with {
          m_bp_type == BP_OFF;
          m_N == 5; } ) begin
          `uvm_fatal("body","Randomization failed");
       end // if
       `uvm_info( "BP TXN BEGIN FINISH", m_bp_txn.convert2string, UVM_DEBUG );
       finish_item( m_bp_txn );
       start_item( m_bp_txn );
       if  (!m_bp_txn.randomize() with {
          m_bp_type == BP_ON;
          m_N == 70; } ) begin
          `uvm_fatal("body","Randomization failed");
       end // if
       `uvm_info( "BP TXN BEGIN FINISH", m_bp_txn.convert2string, UVM_DEBUG );
       finish_item( m_bp_txn );
       end // forever
   endtask: body

endclass : mostly_bp_sequence
