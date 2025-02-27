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
//  Description : Class that serve as a base for all test subclasses
//                Contains the build, the end_of_elaboration and the run phases
//
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
