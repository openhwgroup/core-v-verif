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
//  Description : 
//                The Pulse Gererator is a SystemVerilog UVM module which is used to configure and generate pulses. 
//                Pulse Generator can be configured to generate multiple pulses. A pulse can be a sysncronous pulse with respect 
//                to a clock or an asynchronous pulse. Timeunit of pico second is used to genarate an asynchronous pulse. 
//
// 
// ----------------------------------------------------------------------------

class dummy_txn extends uvm_sequence_item;

endclass : dummy_txn

class pulse_gen_driver extends uvm_driver #( dummy_txn, dummy_txn ) ;

    `uvm_component_utils( pulse_gen_driver )

    //---------------------------
    // Virtual Interface
    //---------------------------
    virtual pulse_if m_pulse_vif;

    //--------------------------------------------
    // handle to pulse configuration
    //--------------------------------------------
    pulse_gen_cfg    m_pulse_cfg; 


    event reset_asserted ;
    event reset_deasserted ;


    //--------------------------------------------
    // pulse count  
    //--------------------------------------------
    protected int              m_pulse_cnt;
    //--------------------------------------------
    // clock period: calculated in the first 
    // clock just after reset 
    //---------------------------------------------
    protected realtime             m_clk_period; 


    function new( string name, uvm_component parent);
        super.new(name,parent);
    endfunction : new

    //---------------------------------------------
    // Build Phase  
    //--------------------------------------------
    function void build_phase( uvm_phase phase );
        super.build_phase( phase);

        if(!uvm_config_db #( virtual pulse_if )::get(this, "", get_name(), m_pulse_vif )) begin
            `uvm_fatal("PULSE GEN DRIVER", $sformatf("Unable to get pulse_if for %s from configuration database", get_name() ) );
        end

    endfunction : build_phase
    // ------------------------------------------------------------------------
    // Pre reset phase
    // ------------------------------------------------------------------------ 
    virtual task pre_reset_phase(uvm_phase phase);
        -> reset_asserted;
        `uvm_info("PULSE GEN DRIVER", "Pre Reset stage complete.", UVM_DEBUG)
    endtask : pre_reset_phase


    // ------------------------------------------------------------------------
    // Reset phase
    // ------------------------------------------------------------------------
    virtual task reset_phase(uvm_phase phase);
        super.reset_phase(phase);

        // initialise to reset values 
        m_pulse_vif.m_pulse_out = 0;
        m_pulse_cnt = 0;
        `uvm_info("PULSE GEN DRIVER", "Reset stage complete.", UVM_DEBUG)
    endtask

    // ------------------------------------------------------------------------
    // Post reset phase
    // ------------------------------------------------------------------------  
    virtual task post_reset_phase(uvm_phase phase);

      -> reset_deasserted;
      `uvm_info("PULSE GEN DRIVER", "Post Reset stage complete.", UVM_DEBUG)
    endtask : post_reset_phase


    // -----------------------------------------------------------------------
    // Run Phase
    // -----------------------------------------------------------------------
    virtual task run_phase(uvm_phase phase);
       realtime   first_clock_edge;
       realtime   second_clock_edge;

       forever begin
         @(reset_deasserted);

         // ---------------------------------------------------------
         // Calculate the clock period 
         // this is used to calculate the phase shift 
         // ---------------------------------------------------------
         m_pulse_vif.wait_n_clocks(1);
         first_clock_edge = $realtime/1ps; // gives time always in ps
         m_pulse_vif.wait_n_clocks(1);
         second_clock_edge = $realtime/1ps;
      
         m_clk_period = second_clock_edge -first_clock_edge;

         `uvm_info("PULSE GEN DRIVER", $sformatf("Estimated clock period %0d(d) ps", m_clk_period), UVM_HIGH)

         fork
           if(m_pulse_cfg.m_pulse_enable)  begin 
             if( m_pulse_cfg.m_pulse_clock_based == 1) gen_synchronous_pulses();
             if( m_pulse_cfg.m_pulse_clock_based == 0) gen_asynchronous_pulses();
           end
         join_none
         @(reset_asserted);
         disable fork;
       end
    endtask: run_phase

    // ------------------------------------------
    // task to generate a synchronous pulse
    // ------------------------------------------
    virtual task gen_synchronous_pulses();

      realtime phase_shift_delay;

      // ---------------------------------------------------------
      // get the phase shift
      // ---------------------------------------------------------
      phase_shift_delay = m_pulse_cfg.m_pulse_phase_shift*m_clk_period/100;

      forever begin
        m_pulse_vif.m_pulse_out = 0;
        m_pulse_vif.wait_n_clocks(m_pulse_cfg.m_pulse_period);
        #(phase_shift_delay * 1ps);
        m_pulse_vif.m_pulse_out = 1;
        m_pulse_vif.wait_n_clocks(m_pulse_cfg.m_pulse_width);
        #(phase_shift_delay * 1ps);
        m_pulse_vif.m_pulse_out = 0;
        if(m_pulse_cfg.m_pulse_num == m_pulse_cnt+1) break; 
        m_pulse_cnt++; 
      end
    endtask

    // ------------------------------------------
    // task to generate an asynchronous pulse (in ps)
    // ------------------------------------------
    virtual task gen_asynchronous_pulses();

      forever begin
        m_pulse_vif.m_pulse_out = 0;
        #(m_pulse_cfg.m_pulse_period * 1ps);
        m_pulse_vif.m_pulse_out = 1;
        #(m_pulse_cfg.m_pulse_width * 1ps);
        m_pulse_vif.m_pulse_out = 0;
        if(m_pulse_cfg.m_pulse_num == m_pulse_cnt+1) break; 
        m_pulse_cnt++; 
      end
    endtask
endclass : pulse_gen_driver

