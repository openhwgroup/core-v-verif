// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// 
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
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


`ifndef __UVML_HRTBT_MON_SV__
`define __UVML_HRTBT_MON_SV__


/**
 * Component implementing a per-phase timeout that can be reset. Enables test
 * benches to terminate simulation only once the design has achieved a quiet
 * state, without the use of '#' delays.
 */
class uvml_hrtbt_mon_c extends uvm_component;
   
   // Configuration
   bit           enabled          = 1;
   int unsigned  startup_timeout  = uvml_hrtbt_default_startup_timeout ;
   int unsigned  heartbeat_period = uvml_hrtbt_default_heartbeat_period;
   int unsigned  refresh_period   = uvml_hrtbt_default_refresh_period  ;
   
   // State
   uvml_hrtbt_entry_struct  timestamps[$];
   bit                      observed_heartbeat = 0;
   
   
   `uvm_component_utils_begin(uvml_hrtbt_mon_c)
      `uvm_field_int(enabled         , UVM_DEFAULT)
      `uvm_field_int(startup_timeout , UVM_DEFAULT)
      `uvm_field_int(heartbeat_period, UVM_DEFAULT)
      `uvm_field_int(refresh_period  , UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor
    */
   extern function new(string name="uvml_hrtbt_mon", uvm_component parent=null);
   
   /**
    * Prints out configuration and ensures activity within startup_timeout.
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * Each phase calls phase_loop()
    */
   extern virtual task pre_reset_phase     (uvm_phase phase);
   extern virtual task reset_phase         (uvm_phase phase);
   extern virtual task post_reset_phase    (uvm_phase phase);
   extern virtual task pre_configure_phase (uvm_phase phase);
   extern virtual task configure_phase     (uvm_phase phase);
   extern virtual task post_configure_phase(uvm_phase phase);
   extern virtual task pre_main_phase      (uvm_phase phase);
   extern virtual task main_phase          (uvm_phase phase);
   extern virtual task post_main_phase     (uvm_phase phase);
   extern virtual task pre_shutdown_phase  (uvm_phase phase);
   extern virtual task shutdown_phase      (uvm_phase phase);
   extern virtual task post_shutdown_phase (uvm_phase phase);
   
   /**
    * 
    */
   extern task phase_loop(uvm_phase phase);
   
   /**
    * 
    */
   extern task eval_heartbeat();
   
   /**
    * 
    */
   extern function void heartbeat(uvm_component owner, int id=0);
   
   /**
    * 
    */
   extern function void reset();
   
   /**
    * 
    */
   extern function string print_comp_names();
   
endclass : uvml_hrtbt_mon_c


function uvml_hrtbt_mon_c::new(string name="uvml_hrtbt_mon", uvm_component parent=null);
  
  super.new(name, parent);
  
endfunction : new


task uvml_hrtbt_mon_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);

   if (enabled) begin
      `uvm_info("HRTBT", $sformatf("Starting heartbeat monitor with startup_timeout=%0t, heartbeat_period=%0t, refresh_period=%0t",
         startup_timeout,
         heartbeat_period,
         refresh_period
      ), UVM_NONE)
      
      #(startup_timeout * 1ns);
      if (!observed_heartbeat) begin
         //`uvm_fatal("HRTBT", $sformatf("Did not observe heartbeat in first %0dns", startup_timeout))
         `uvm_info("HRTBT", $sformatf("Did not observe heartbeat in first %0dns", startup_timeout), UVM_NONE)
      end
   end
   
endtask : run_phase


task uvml_hrtbt_mon_c::pre_reset_phase(uvm_phase phase);
   
   super.pre_reset_phase(phase);
   phase_loop           (phase);
   
endtask : pre_reset_phase


task uvml_hrtbt_mon_c::reset_phase(uvm_phase phase);
   
   super.reset_phase(phase);
   phase_loop       (phase);
   
endtask : reset_phase


task uvml_hrtbt_mon_c::post_reset_phase(uvm_phase phase);
   
   super.post_reset_phase(phase);
   phase_loop            (phase);
   
endtask : post_reset_phase


task uvml_hrtbt_mon_c::pre_configure_phase(uvm_phase phase);
   
   super.pre_configure_phase(phase);
   phase_loop               (phase);
   
endtask : pre_configure_phase


task uvml_hrtbt_mon_c::configure_phase(uvm_phase phase);
   
   super.configure_phase(phase);
   phase_loop           (phase);
   
endtask : configure_phase


task uvml_hrtbt_mon_c::post_configure_phase(uvm_phase phase);
   
   super.post_configure_phase(phase);
   phase_loop                (phase);
   
endtask : post_configure_phase


task uvml_hrtbt_mon_c::pre_main_phase(uvm_phase phase);
   
   super.pre_main_phase(phase);
   phase_loop          (phase);
   
endtask : pre_main_phase


task uvml_hrtbt_mon_c::main_phase(uvm_phase phase);
   
   super.main_phase(phase);
   phase_loop      (phase);
   
endtask : main_phase


task uvml_hrtbt_mon_c::post_main_phase(uvm_phase phase);
   
   super.post_main_phase(phase);
   phase_loop           (phase);
   
endtask : post_main_phase


task uvml_hrtbt_mon_c::pre_shutdown_phase(uvm_phase phase);
   
   super.pre_shutdown_phase(phase);
   phase_loop              (phase);
   
endtask : pre_shutdown_phase


task uvml_hrtbt_mon_c::shutdown_phase(uvm_phase phase);
   
   super.shutdown_phase(phase);
   phase_loop          (phase);
   
endtask : shutdown_phase


task uvml_hrtbt_mon_c::post_shutdown_phase(uvm_phase phase);
   
   super.post_shutdown_phase(phase);
   phase_loop               (phase);
   
endtask : post_shutdown_phase


task uvml_hrtbt_mon_c::phase_loop(uvm_phase phase);

   if (enabled) begin
      reset();
      phase.raise_objection(this);
      eval_heartbeat();
      phase.drop_objection(this);
   end
   
endtask : phase_loop


task uvml_hrtbt_mon_c::eval_heartbeat();
   
   uvml_hrtbt_entry_struct  new_timestamps[$];
   realtime                 current_maturity;
   
   forever begin
      #(refresh_period * 1ns);
      new_timestamps.delete();
      
      // Copy timestamps, culling out those that have matured
      foreach (timestamps[ii]) begin
         current_maturity = (heartbeat_period * 1ns) + timestamps[ii].timestamp;
         if (current_maturity <= $realtime()) begin
            if (timestamps[ii].owner == null) begin
               `uvm_info("HRTBT", $sformatf("Removed component from heartbeat list: id (%0d)", timestamps[ii].id), UVM_DEBUG)
            end
            else begin
               `uvm_info("HRTBT", $sformatf("Removed component from heartbeat list: owner (%s), id (%0d)", timestamps[ii].owner.get_full_name(), timestamps[ii].id), UVM_DEBUG)
            end
         end
         else begin
           new_timestamps.push_back(timestamps[ii]);
         end
      end
      
      if (new_timestamps.size() == 0) begin
         `uvm_info("HRTBT", "Heartbeat count is 0. Dropping objection", UVM_NONE)
         break;
      end
      else begin
         timestamps.delete();
         foreach (new_timestamps[ii]) begin
            timestamps.push_back(new_timestamps[ii]);
         end
      end
   end
   
endtask : eval_heartbeat


function void uvml_hrtbt_mon_c::heartbeat(uvm_component owner, int id=0);
   
   if (id == 0) begin
      id = $random();
   end
   
   timestamps.push_back('{
      owner    : owner,
      id       : id,
      timestamp: $realtime()
   });
   
   if (owner == null) begin
      `uvm_info("HRTBT", $sformatf("Added/updated to heartbeat list: id (%0d)", id), UVM_DEBUG)
   end
   else begin
      `uvm_info("HRTBT", $sformatf("Added/updated to heartbeat list: owner (%s), id (%0d)", owner.get_full_name(), id), UVM_DEBUG)
   end
   
   observed_heartbeat = 1;
   
endfunction : heartbeat


function void uvml_hrtbt_mon_c::reset();
   
   timestamps.delete();
   `uvm_info("HRTBT", "Heartbeat monitor reset", UVM_DEBUG)
   
endfunction : reset


function string uvml_hrtbt_mon_c::print_comp_names();
  
  string         comp_names = "";
  uvm_component  unique_comps[uvm_component];
  
  foreach (timestamps[ii]) begin
     if (timestamps[ii].owner != null) begin
       unique_comps[timestamps[ii].owner] = timestamps[ii].owner;
    end
  end
  
  foreach (unique_comps[comp]) begin
    comp_names = {comp_names, "\n", comp.get_full_name()};
  end
  
  return comp_names;
  
endfunction : print_comp_names


`endif // __UVML_HRTBT_MON_SV__
