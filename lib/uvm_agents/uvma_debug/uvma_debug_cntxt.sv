// COPYRIGHT HEADER


`ifndef __UVMA_DEBUG_CNTXT_SV__
`define __UVMA_DEBUG_CNTXT_SV__


/**
 * Object encapsulating all state variables for all Debug agent
 * (uvma_debug_agent_c) components.
 */
class uvma_debug_cntxt_c extends uvm_object;
   
   // Handle to agent interface
   virtual uvma_debug_if  vif;
   
   // Integrals
   uvma_reset_state_enum  reset_state = UVMA_RESET_STATE_PRE_RESET;
   
   // Events
   uvm_event  sample_cfg_e;
   uvm_event  sample_cntxt_e;
   
   
   `uvm_object_utils_begin(uvma_debug_cntxt_c)
      `uvm_field_enum(uvma_reset_state_enum, reset_state, UVM_DEFAULT)
      
      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Builds events.
    */
   extern function new(string name="uvma_debug_cntxt");
   
   /**
    * TODO Describe uvma_debug_cntxt_c::reset()
    */
   extern function void reset();
   
endclass : uvma_debug_cntxt_c


`pragma protect begin


function uvma_debug_cntxt_c::new(string name="uvma_debug_cntxt");
   
   super.new(name);
   
   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");
   
endfunction : new


function void uvma_debug_cntxt_c::reset();
   
   // TODO Implement uvma_debug_cntxt_c::reset()
   
endfunction : reset


`pragma protect end


`endif // __UVMA_DEBUG_CNTXT_SV__
