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
//  Description : generic transaction used in the driver to drive the requests
// ----------------------------------------------------------------------------

// -----------------------------------------------------------------------
// Class generic_txn
//
// Contains fields that are sent to the scoreboard for further analysis
// -----------------------------------------------------------------------
class generic_txn#(type req_t, type rsp_t) extends uvm_sequence_item;
   `uvm_object_param_utils(generic_txn #(req_t, rsp_t))
    //          Request Type 
    rand req_t          m_req;
    rsp_t               m_rsp;

    rand int            m_txn_idle_cycles;
    // ------------------------------------------------------------------------
    // Constructor
    // ------------------------------------------------------------------------
    function new(string name = "generic_txn");
        super.new(name);
    endfunction

    // ------------------------------------------------------------------------
    // convert2string
    // ------------------------------------------------------------------------
    virtual function string convert2string;
        string s;
        s = super.convert2string();
        return s;
    endfunction: convert2string

    function generic_txn #(req_t, rsp_t) clone();

      generic_txn #(req_t, rsp_t) ret; 
      ret = new("clone");

      ret.m_req = m_req;
      ret.m_rsp = m_rsp; 
      ret.m_txn_idle_cycles = m_txn_idle_cycles;

      return ret; 

    endfunction 
endclass: generic_txn
