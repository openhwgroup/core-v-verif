// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2022 Silicon Labs, Inc.
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


`ifndef __UVMA_CLIC_SEQ_ITEM_SV__
`define __UVMA_CLIC_SEQ_ITEM_SV__


/**
 * Object created by Interrupt agent sequences extending uvma_clic_seq_base_c.
 */
class uvma_clic_seq_item_c extends uvml_trn_seq_item_c;

   rand uvma_clic_seq_item_action_enum   action;
   rand int unsigned                     index;
   rand bit [8:0]                        level;
   rand bit [1:0]                        privilege_mode;
   rand bit                              sel_hardware_vectoring;

   rand int unsigned                     skew; // Skew (in cycles) before applying individual interrupt actions per interrupt
   rand int unsigned                     repeat_count; // Number of times to apply action to interrupt

   rand int unsigned                     no_skew_wgt;
   rand int unsigned                     skew_wgt;


   // TODO FIXME update actually used signals
   `uvm_object_utils_begin(uvma_clic_seq_item_c)
      `uvm_field_enum(uvma_clic_seq_item_action_enum, action, UVM_DEFAULT)
      `uvm_field_int(index, UVM_DEFAULT)
      `uvm_field_int(level, UVM_DEFAULT)
      `uvm_field_int(privilege_mode, UVM_DEFAULT)
      `uvm_field_int(sel_hardware_vectoring, UVM_DEFAULT)
      `uvm_field_int(skew, UVM_DEFAULT)
      `uvm_field_int(no_skew_wgt, UVM_DEFAULT)
      `uvm_field_int(skew_wgt, UVM_DEFAULT)
      `uvm_field_int(repeat_count, UVM_DEFAULT)
   `uvm_object_utils_end

  //constraint irq_index_c {
  //  irq_index inside {[0:4095]};
  //}

  // FIXME TODO move to core specific cfg
  constraint irq_privilege_mode_c {
    privilege_mode == 2'b11;
  }
  constraint irq_privilege_level_c {
    level inside {[0:255]};
  }
  constraint irq_index_c {
    index inside {[0:1023]};
  }

   constraint valid_repeat_count_c {
      repeat_count != 0;
   }

   constraint default_repeat_count_c {
      soft repeat_count == 1;
   }

   constraint valid_skew_wgt {
      no_skew_wgt + skew_wgt != 0;
      skew_wgt == 1;
      no_skew_wgt == 0;
   }

   constraint default_skew_wgt_c {
      no_skew_wgt inside {[0:5]};
      skew_wgt inside {[0:3]};
   }

   constraint skew_wgt_order_c {
         solve skew_wgt before skew;
         solve no_skew_wgt before skew;
   }

   constraint default_skew_c {
         skew dist { 0      :/ no_skew_wgt,
                     [1:32] :/ skew_wgt};
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_clic_seq_item");

endclass : uvma_clic_seq_item_c

`pragma protect begin


function uvma_clic_seq_item_c::new(string name="uvma_clic_seq_item");

   super.new(name);

endfunction : new


`pragma protect end


`endif // __UVMA_CLIC_SEQ_ITEM_SV__
