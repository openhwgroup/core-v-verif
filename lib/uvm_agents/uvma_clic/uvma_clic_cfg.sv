//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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
//


`ifndef __UVMA_CLIC_CFG_SV__
`define __UVMA_CLIC_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running all
 * Clock & Reset agent (uvma_clic_agent_c) components.
 */
class uvma_clic_cfg_c extends uvm_object;

   // Common options
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;
   rand bit                      is_mmode_irq_only;

   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;

   // Implementation options
   rand bit[31:0]                valid_irq_mask;   ///< State variable: the valid clics for the core under test
   rand bit[31:0]                enabled_irq_mask; ///< The mask of clics that can be driven
   rand bit                      clear_irq_on_ack;

   `uvm_object_utils_begin(uvma_clic_cfg_c)
      `uvm_field_int (                         enabled           , UVM_DEFAULT)
      `uvm_field_enum(uvm_active_passive_enum, is_active         , UVM_DEFAULT)
      `uvm_field_int (                         is_mmode_irq_only , UVM_DEFAULT)
      `uvm_field_int (                         cov_model_enabled , UVM_DEFAULT)
      `uvm_field_int (                         trn_log_enabled   , UVM_DEFAULT)
      `uvm_field_int (                         clear_irq_on_ack  , UVM_DEFAULT)
      `uvm_field_int (                         enabled_irq_mask  , UVM_DEFAULT)
   `uvm_object_utils_end


   constraint defaults_cons {
      soft enabled           == 1;
      soft is_active         == UVM_PASSIVE;
      soft is_mmode_irq_only == 0;
      soft cov_model_enabled == 0;
      soft trn_log_enabled   == 1;
      soft clear_irq_on_ack  == 1;
      soft enabled_irq_mask  == 32'hffff_ffff;
   }

   constraint valid_irq {
      // Should always have at least one valid clic enabled
      (enabled_irq_mask & valid_irq_mask) != 0;
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_clic_cfg");

endclass : uvma_clic_cfg_c

function uvma_clic_cfg_c::new(string name="uvma_clic_cfg");

   super.new(name);

endfunction : new

`endif // __UVMA_CLIC_CFG_SV__
