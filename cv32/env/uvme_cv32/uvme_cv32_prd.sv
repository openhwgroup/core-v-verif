// COPYRIGHT HEADER


`ifndef __UVME_CV32_PRD_SV__
`define __UVME_CV32_PRD_SV__


/**
 * Component implementing transaction-based software model of CV32 DUT.
 */
class uvme_cv32_prd_c extends uvm_component;
   
   // Objects
   uvme_cv32_cfg_c    cfg;
   uvme_cv32_cntxt_c  cntxt;
   
   // Input TLM
   uvm_analysis_export  #(uvma_debug_mon_trn_c)  debug_export;
   uvm_tlm_analysis_fifo#(uvma_debug_mon_trn_c)  debug_fifo;
   uvm_analysis_export  #(uvma_reset_mon_trn_c)  reset_export;
   uvm_tlm_analysis_fifo#(uvma_reset_mon_trn_c)  reset_fifo;
   
   // Output TLM
   // TODO Add TLM outputs to uvme_cv32_prd_c
   //      Ex: uvm_analysis_port#(uvma_packet_trn_c)  pkts_out_ap;
   
   
   `uvm_component_utils_begin(uvme_cv32_prd_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32_prd", uvm_component parent=null);
   
   /**
    * TODO Describe uvme_cv32_prd_c::build_phase()
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvme_cv32_prd_c::connect_phase()
    */
   extern virtual function void connect_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvme_cv32_prd_c::run_phase()
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvme_cv32_prd_c::process_debug()
    */
   extern task process_debug();
   
   /**
    * TODO Describe uvme_cv32_prd_c::process_reset()
    */
   extern task process_reset();
   
endclass : uvme_cv32_prd_c


`pragma protect begin


function uvme_cv32_prd_c::new(string name="uvme_cv32_prd", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvme_cv32_prd_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvme_cv32_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvme_cv32_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   // Build Input TLM objects
   debug_export = new("debug_export", this);
   debug_fifo   = new("debug_fifo"  , this);
   reset_export = new("reset_export", this);
   reset_fifo   = new("reset_fifo"  , this);
   
   // Build Output TLM objects
   // TODO Create Output TLM objects for uvme_cv32_prd_c
   //      Ex: pkts_out_ap = new("pkts_out_ap", this);
   
endfunction : build_phase


function void uvme_cv32_prd_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);
   
   // Connect TLM objects
   debug_export.connect(debug_fifo.analysis_export);
   reset_export.connect(reset_fifo.analysis_export);
   
endfunction: connect_phase


task uvme_cv32_prd_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   fork
      process_debug();
      process_reset();
   join_none
   
endtask: run_phase


task uvme_cv32_prd_c::process_debug();
   
   uvma_debug_mon_trn_c  debug_trn;
   
   forever begin
      debug_fifo.get(debug_trn);
      
      // TODO Implement uvme_cv32_prd_c::process_debug()
   end
   
endtask : process_debug


task uvme_cv32_prd_c::process_reset();
   
   uvma_reset_mon_trn_c  reset_trn;
   
   forever begin
      reset_fifo.get(reset_trn);
      
      // TODO Implement uvme_cv32_prd_c::process_reset()
   end
   
endtask : process_reset


`pragma protect end


`endif // __UVME_CV32_PRD_SV__
