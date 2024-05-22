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
//  Description : A virtual sequence. To be able to run one of the 4 back
//                pressure sequence 
//                
// 
// ----------------------------------------------------------------------------
import uvm_pkg::*;
`include "uvm_macros.svh";

import bp_driver_pkg::*;

// base class of virtual sequence 
class bp_vseq_base extends uvm_sequence #(uvm_sequence_item);
 `uvm_object_utils(bp_vseq_base)

 // Type of the back pressure to be applied
 bp_type_t    which_bp;
 /// Target Agent Sequencers
 bp_sequencer bp_sqr;
 
 /// Constructor
 function new (string name = "bp_vseq_base");
   super.new(name);
 endfunction: new

 // APIs to get bp type and sequencer 
 function void set_bp_type(bp_type_t bp);
   which_bp = bp;
 endfunction 

 function void set_bp_sequencer(bp_sequencer sqr);
   bp_sqr = sqr;
 endfunction 
endclass: bp_vseq_base

///// Virtual Sequence Class
class bp_virtual_sequence extends bp_vseq_base;
 `uvm_object_utils(bp_virtual_sequence)
 
 /// Constructor
 function new (string name = "bp_virtual_sequence");
   super.new(name);
 endfunction: new
 
 /// Sequence Body Task
 task body();

    // Following three sequences are defined in bp_seq agent
   occassional_bp_sequence o_bp_sequence;
 
   heavy_bp_sequence       h_bp_sequence;

   no_bp_sequence          n_bp_sequence;

   mostly_bp_sequence      m_bp_sequence; 

   // occasional backpressure
   o_bp_sequence   = occassional_bp_sequence::type_id::create("o_bp_seq");   
 
   // heavy backpressure
   h_bp_sequence   = heavy_bp_sequence::type_id::create("h_bp_seq");   

   // No backpressure
   n_bp_sequence   = no_bp_sequence::type_id::create("no_bp_seq");   

   // 
   m_bp_sequence   = mostly_bp_sequence::type_id::create("no_bp_seq");   

     case (which_bp)
        OCCASSIONAL_BP: begin
            o_bp_sequence.start(bp_sqr);
        end
        NO_BP: begin
            n_bp_sequence.start(bp_sqr);
        end
        HEAVY_BP: begin
            h_bp_sequence.start(bp_sqr);
        end
        MOSTLY_BP: begin
            m_bp_sequence.start(bp_sqr);
        end
        default: `uvm_fatal("VSEQ FATAL", $sformatf("Back pressure %s doesnt exists", which_bp ))
     endcase
 endtask: body // body 
endclass: bp_virtual_sequence
