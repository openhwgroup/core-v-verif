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
// ----------------------------------------------------------------------------
//  Description : Parameterized driver for reset signal.
//                -> p_init_value  = value when reset is not active
//                -> p_init_assert = number of clocks to assert reset
//                -> p_post_reset_delay = number of clocks after reset
//                                        to terminate UVM reset phase
//                -> f_do_not_phase_jump = Flag to be set by user
//                    If the flag is set, the reset driver is immune to the phase
//                    jump (it does nothing in the reset_phase after the phase
//                    jump)
//
//                Normally, during the reset phase, the reset will be asserted,
//                the class will raise an objection during this time, the
//                reset will be de-asserted, and then the objection will
//                be dropped.
//
//                Using the flag disable_auto_reset_phase, we can force the
//                reset driver to ignore the reset phase. It is then up to
//                the user to manually assert and de-assert the reset using
//                the procedural calls : manual_assert_reset() and 
//                manual_de_assert_reset().
//
//                ->assert_reset: Is an event to force reset 
//                emit_assert_reset: Is an API to emit asser_reset 
//                -> num_reset: Is the number of reset to be asserted 
//                -> set_num_reset: Is an API to set the number of reset to be asserted 
//                -> get_reset_on_the_fly_done: Is an API to know when all the reset (== num_reset) are asserted 
//                Example from the test: 
//                connect phase: Set the number of reset to be asserted  
//                       env.reset_driver.set_num_reset(6);
//                main phase:
//                  --> Set the criteria to insert the reset, in this example number of transaction is used
//                  --> Assert an reset every nb_trans 
//                  nb_trans = $urandom_range(20, 60);
//                 // ------------------------
//                 // Assert reset  
//                 // ------------------------
//                 fork 
//                  phase.raise_objection(this, "Start reset asertion");
//                  forever begin
//                    
//                    vif.wait_n_clocks(1); 
//                    if(env.reset_driver.get_reset_on_the_fly_done == 1) begin
//
//                        `uvm_info("RESET ON THE FLY END", $sformatf("%0d(d), %0d(d)",env.scoreboard.get_req_counter, nb_trans ), UVM_DEBUG);    
//                        phase.drop_objection(this, "Finish reset assertion");
//                        break;
//                    
//                    end
//
//                    `uvm_info("RESET ON THE FLY", $sformatf("%0d(d), %0d(d)",env.scoreboard.get_req_counter, nb_trans ), UVM_DEBUG);
//                    
//                    if(env.scoreboard.get_req_counter() == nb_trans) begin
//
//                      phase.drop_objection(this, "Assert reset");
//                      env.reset_driver.emit_assert_reset();
//
//                    end
//                  end
//                 join_none
//                 
//
// ----------------------------------------------------------------------------

class dummy_txn extends uvm_sequence_item;

endclass : dummy_txn

class reset_counter_c extends uvm_object;
    `uvm_object_utils(reset_counter_c)

   function new (string name = "reset_counter_c");
     super.new(name);
   endfunction
   static int num_active_resets = 0;
endclass : reset_counter_c

class reset_driver_c #(              bit p_init_value = 1'b0, 
                        integer unsigned p_init_assert = 0, 
                        integer unsigned p_post_reset_delay = 0 ) extends uvm_driver #( dummy_txn, dummy_txn ) ;

    `uvm_component_param_utils( reset_driver_c #( p_init_value, p_init_assert, p_post_reset_delay ) )

    reset_counter_c m_reset_counter;

    protected bit m_do_not_phase_jump; // it is used for the power_on_reset 
    protected bit f_do_not_phase_jump; // flag to indicate that reset driver is only one time reset
    protected bit disable_auto_reset_phase;

    // -------------------------------------------------------------------------
    // When assert reset is triggered 
    // Phase jump to pre reset phase is performed
    // -------------------------------------------------------------------------
    protected event assert_reset;
    protected bit   reset_on_the_fly_done;

    protected int   reset_cnt;
    protected int   num_reset;
    // -------------------------------------------------------------------------
    // Virtual Interface
    // -------------------------------------------------------------------------
    virtual xrtl_reset_vif  #( p_init_value, p_init_assert, p_post_reset_delay ) m_v_reset_vif;

    function new( string name, uvm_component parent);
        super.new(name,parent);
        m_reset_counter = reset_counter_c::type_id::create("my_counter", this);
        m_do_not_phase_jump = 0;
        f_do_not_phase_jump = 0;
        disable_auto_reset_phase = 0;
        reset_cnt = 0;
        num_reset = 2; 
    endfunction : new

    function void build_phase( uvm_phase phase );
        super.build_phase( phase);

        if(!uvm_config_db #( virtual xrtl_reset_vif #( p_init_value, 
                                                      p_init_assert, 
                                                      p_post_reset_delay ) )::get(this, "", get_name(), m_v_reset_vif )) begin
            `uvm_fatal("BUILD_PHASE", $sformatf("Unable to get reset_vif for %s from configuration database", get_name() ) );
        end

    endfunction : build_phase

    function void connect_phase( uvm_phase phase );
        super.connect_phase( phase );

        m_v_reset_vif.hvl_obj = new( get_full_name( ) );

        `uvm_info( "RESET CONNECT", "Reset driver now connected", UVM_MEDIUM );

     endfunction : connect_phase

    virtual task reset_phase( uvm_phase phase );
        if ( (m_do_not_phase_jump == 0) && ( disable_auto_reset_phase == 0 ) ) begin
           phase.raise_objection( this, "Currently in reset");
           m_reset_counter.num_active_resets++;
           `uvm_info( "RESET START", $sformatf("RESET START (%0d active)", m_reset_counter.num_active_resets ), UVM_LOW );
           m_v_reset_vif.assert_reset( );
           @( m_v_reset_vif.hvl_obj.reset_deasserted );
           m_reset_counter.num_active_resets--;
           `uvm_info( "RESET DONE", $sformatf("RESET DONE (%0d active)", m_reset_counter.num_active_resets ), UVM_NONE );
           phase.drop_objection( this, "Reset de-asserted");
           if(f_do_not_phase_jump == 1) m_do_not_phase_jump = 1;
        end
    endtask : reset_phase

    // ------------------------------------------
    // MAIN PHASE 
    // ------------------------------------------
    virtual task main_phase(uvm_phase phase); 
  
      // --------------------------
      // Reset on the fly
      // --------------------------
      fork
       forever begin 
         if(num_reset == reset_cnt) begin
             reset_on_the_fly_done = 1;
             break;
         end
         @assert_reset;
         reset_cnt++;
         phase.get_objection().set_report_severity_id_override(UVM_WARNING, "OBJTN_CLEAR", UVM_INFO);
         phase.jump(uvm_pre_reset_phase::get());
       end
      join_none
    endtask: main_phase; 

    virtual task post_shutdown_phase( uvm_phase phase );
        m_v_reset_vif.set_post_shutdown_phase_started( );
        phase.raise_objection( this, "Started Post Shutdown");
        `uvm_info( "POST SHUTDOWN PHASE STARTED", "ENTERING POST SHUTDOWN", UVM_NONE );
        #1; // Allow time for any assertions to trigger
        phase.drop_objection( this, "Post Shutdown Completed");
    endtask : post_shutdown_phase

    // its a one time flag to be set at the begning 
    function void set_do_not_phase_jump_flag();
      f_do_not_phase_jump = 1;
    endfunction
    
    function void set_disable_auto_reset(bit disable_auto_reset_phase);
        this.disable_auto_reset_phase = disable_auto_reset_phase; // when this is '1' - the class does not automtically assert reset during the reset phase
        `uvm_info( "DISABLE_AUTO_RESET", $sformatf("AUTO_RESET DISABLE (%0b)", this.disable_auto_reset_phase ), UVM_NONE );
    endfunction : set_disable_auto_reset

    virtual task manual_assert_reset( );
       m_v_reset_vif.assert_reset( 1000000 );
       `uvm_info( "RESET_GEN", "MANUALLY ASSERTED RESET", UVM_NONE );
    endtask : manual_assert_reset

    virtual task manual_de_assert_reset( );
       m_v_reset_vif.assert_reset( 0 );
       `uvm_info( "RESET_GEN", "MANUALLY DE-ASSERTED RESET", UVM_NONE );
    endtask : manual_de_assert_reset

    // -----------------------------------------
    // API to force reset
    // -----------------------------------------
    task emit_assert_reset();
      ->assert_reset;
    endtask

    // ------------------------------------------------------
    // API to set the number of reset a user wants to insert
    // ------------------------------------------------------
    function void set_num_reset(int N);
       num_reset = N;
    endfunction: set_num_reset

    function int get_num_reset();
       get_num_reset = num_reset;
    endfunction: get_num_reset

    // ---------------------------------------------------------
    // API to tell a user, all reset(== num_reset) are inserted
    // ---------------------------------------------------------
    function bit get_reset_on_the_fly_done();
       get_reset_on_the_fly_done = reset_on_the_fly_done;
    endfunction: get_reset_on_the_fly_done
endclass : reset_driver_c

