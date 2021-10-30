// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVME_CV32E40S_BASE_VSEQ_SV__
`define __UVME_CV32E40S_BASE_VSEQ_SV__


/**
 * Abstract object from which all other CV32E40S virtual sequences extend.
 * Does not generate any sequence items of its own. Subclasses must be run on
 * CV32E40S Virtual Sequencer (uvme_cv32e40s_vsqr_c) instance.
 */
class uvme_cv32e40s_base_vseq_c extends uvm_sequence#(
   .REQ(uvm_sequence_item),
   .RSP(uvm_sequence_item)
);

   // Environment handles
   uvme_cv32e40s_cfg_c    cfg;
   uvme_cv32e40s_cntxt_c  cntxt;


   `uvm_object_utils(uvme_cv32e40s_base_vseq_c)
   `uvm_declare_p_sequencer(uvme_cv32e40s_vsqr_c)


   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40s_base_vseq");

   /**
    * Retrieve cfg and cntxt handles from p_sequencer.
    */
   extern virtual task pre_start();

endclass : uvme_cv32e40s_base_vseq_c


function uvme_cv32e40s_base_vseq_c::new(string name="uvme_cv32e40s_base_vseq");

   super.new(name);

endfunction : new


task uvme_cv32e40s_base_vseq_c::pre_start();

   cfg   = p_sequencer.cfg  ;
   cntxt = p_sequencer.cntxt;

endtask : pre_start


`endif // __UVME_CV32E40S_BASE_VSEQ_SV__
