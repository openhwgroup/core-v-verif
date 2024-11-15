// ----------------------------------------------------------------------------
//                                CEA - LETI
//    Reproduction and Communication of this document is strictly prohibited
//      unless specifically authorized in writing by CEA - LETI.
// ----------------------------------------------------------------------------
//                        LETI / DACLE / LISAN
// ----------------------------------------------------------------------------
//
//
//  File        : $filename : base_test_c.svh$
//
//  Description : Class that serve as a base for all test subclasses
//                Contains the build, the end_of_elaboration and the run phases
//
//  Copyright (C) 2019 CEA-Leti
//  Author      : $authorname : PERBOST Nicolas $ $authoremail : nicolas.perbost.fr $
//
//  Id          : $Id: 2c735a67005a24f8a4f452f5b14e327f35db875a $
//  Date        : $Date : Tue Mar 5 17:22:29 2019 +0100 $
//
// ----------------------------------------------------------------------------
class base_test_c extends uvm_test;
  `uvm_component_utils(base_test_c)

  dut_env env;
  uvm_table_printer printer;

  function new(string name, uvm_component parent);
      super.new(name, parent);
  endfunction: new

  function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      env = dut_env::type_id::create("ENV", this);
      printer = new( );
      printer.knobs.depth = 5;
  endfunction:build_phase

  task configure_phase(uvm_phase phase);
      super.configure_phase(phase);

      if ( !env.agent_config.randomize() ) begin
        `uvm_fatal("RANDOMIZE_FAILED", "Failed randomization of the bp_gen config")
      end
      `uvm_info("BP_WHICH", $sformatf("BP_MODE=%p", env.agent_config.aw_bp), UVM_LOW)
      env.aw_bp_vseq.which_bp = env.agent_config.aw_bp ;
      env.w_bp_vseq.which_bp  = env.agent_config.w_bp  ;
      env.b_bp_vseq.which_bp  = env.agent_config.b_bp  ;
      env.ar_bp_vseq.which_bp = env.agent_config.ar_bp ;
      env.r_bp_vseq.which_bp  = env.agent_config.r_bp  ;

  endtask : configure_phase

  virtual function void end_of_elaboration_phase(uvm_phase phase);
      `uvm_info(get_type_name( ), $sformatf("Printing the test topology :\n%s", this.sprint(printer)), UVM_LOW)
   //   factory.print();
  endfunction: end_of_elaboration_phase

  virtual task main_phase(uvm_phase phase);
    super.main_phase(phase);
    phase.raise_objection(this);
    #2000ns
    phase.drop_objection(this);
  endtask: main_phase

endclass: base_test_c
