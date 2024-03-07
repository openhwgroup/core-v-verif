// Copyright 2023 OpenHW Group
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


`ifndef __UVMC_RVFI_SPIKE_SV__
`define __UVMC_RVFI_SPIKE_SV__

/**
 * Component that implements reference model functionality with Spike
 */


class uvmc_rvfi_spike#(int ILEN=DEFAULT_ILEN,
                                  int XLEN=DEFAULT_XLEN
) extends uvmc_rvfi_reference_model;

   `uvm_component_param_utils(uvmc_rvfi_spike)

   /**
    * Default constructor.
    */
   function new(string name="uvmc_rvfi_spike", uvm_component parent=null);

       super.new(name, parent);

   endfunction : new

   /**
    * Build phase
    */
   function void build_phase(uvm_phase phase);
       st_core_cntrl_cfg st;

       super.build_phase(phase);

       st = cfg.to_struct();

       rvfi_initialize_spike(cfg.core_name, st);
   endfunction : build_phase

   /**
    * Step function - Steps the core and returns a rvfi transaction
    */
   virtual function uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) step (int i, uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t);

       st_rvfi s_core, s_reference_model;
       uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) t_reference_model;

       s_core = t.seq2rvfi();

       rvfi_spike_step(s_core, s_reference_model);

       t_reference_model = new("t_reference_model");
       t_reference_model.rvfi2seq(s_reference_model);
       return t_reference_model;

   endfunction : step

endclass : uvmc_rvfi_spike

`endif // __UVMC_RVFI_SPIKE_SV__

