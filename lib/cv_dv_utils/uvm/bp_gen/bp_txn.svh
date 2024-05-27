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
//  Description : This is a sequence item for back pressure transactions
//                
// 
// ----------------------------------------------------------------------------

class bp_txn extends uvm_sequence_item;

   // -------------------------------------------------------------------------
   // Random Fields for the BP transaction
   // -------------------------------------------------------------------------
   rand  bp_drive_type_t            m_bp_type;
   rand int                         m_N;   // duration
   rand int                         m_M;   // either percent or toggle freq
   
   // -------------------------------------------------------------------------
   // UVM Utils for randomized fields
   // -------------------------------------------------------------------------
   `uvm_object_utils_begin( bp_txn )
      `uvm_field_enum( bp_drive_type_t, m_bp_type, UVM_DEFAULT              );
      `uvm_field_int(  m_N                       , UVM_DEFAULT | UVM_DEC    );
      `uvm_field_int(  m_M                       , UVM_DEFAULT | UVM_DEC    );
   `uvm_object_utils_end

   // -------------------------------------------------------------------------
   // Constructor
   // -------------------------------------------------------------------------
   function new( string name = "bp_driver" );
       super.new(name);
   endfunction : new

   // -------------------------------------------------------------------------
   // convert2string
   // -------------------------------------------------------------------------
   virtual function string convert2string;
      string s;
      s = super.convert2string();
      s = $sformatf( "%s TYPE=%s N=%0d(d) M=%0d(d)", s, m_bp_type.name(), m_N, m_M );
      return s;
   endfunction : convert2string

endclass : bp_txn
