// COPYRIGHT HEADER


`ifndef __UVME_CV32_BASE_VSEQ_SV__
`define __UVME_CV32_BASE_VSEQ_SV__


/**
 * Abstract object from which all other CV32 virtual sequences extend.
 * Does not generate any sequence items of its own. Subclasses must be run on
 * CV32 Virtual Sequencer (uvme_cv32_vsqr_c) instance.
 */
class uvme_cv32_base_vseq_c extends uvm_sequence#(
   .REQ(uvm_sequence_item),
   .RSP(uvm_sequence_item)
);
   
   // Environment handles
   uvme_cv32_cfg_c    cfg;
   uvme_cv32_cntxt_c  cntxt;
   
   
   `uvm_object_utils(uvme_cv32_base_vseq_c)
   `uvm_declare_p_sequencer(uvme_cv32_vsqr_c)
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32_base_vseq");
   
   /**
    * Retrieve cfg and cntxt handles from p_sequencer.
    */
   extern virtual task pre_start();
   
endclass : uvme_cv32_base_vseq_c


`pragma protect begin


function uvme_cv32_base_vseq_c::new(string name="uvme_cv32_base_vseq");
   
   super.new(name);
   
endfunction : new


task uvme_cv32_base_vseq_c::pre_start();
   
   cfg   = p_sequencer.cfg;
   cntxt = p_sequencer.cntxt;
   
endtask : pre_start


`pragma protect end


`endif // __UVME_CV32_BASE_VSEQ_SV__
