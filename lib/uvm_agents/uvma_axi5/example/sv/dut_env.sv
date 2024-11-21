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


class dut_env extends uvm_env;

  watchdog_c      m_wd;

  clock_driver_c  cc_clock_driver;
  clock_config_c  cc_clock_cfg;

  reset_driver_c #(1'b1,10,0) cc_reset_driver;

  uvma_axi_agent_c      master; 
  uvma_axi_agent_c      slave; 

  uvma_axi_cfg_c         master_cfg ;
  uvma_axi_cfg_c         slave_cfg ;

  uvma_axi_transaction_cfg_c if_item_cfg;





  bp_agent              aw_bp_agent ;
  bp_agent              w_bp_agent  ;
  bp_agent              b_bp_agent  ;
  bp_agent              ar_bp_agent ;
  bp_agent              r_bp_agent  ;

  bp_virtual_sequence   aw_bp_vseq ;
  bp_virtual_sequence   w_bp_vseq  ;
  bp_virtual_sequence   b_bp_vseq  ;
  bp_virtual_sequence   ar_bp_vseq ;
  bp_virtual_sequence   r_bp_vseq  ;

  dut_cfg_c  agent_config;

  `uvm_component_utils(dut_env)

  function new(string name, uvm_component parent);
      super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      m_wd = watchdog_c::type_id::create("m_wd",this);

      cc_clock_driver = clock_driver_c::type_id::create("cc_clock_driver", this );
      cc_clock_cfg    = clock_config_c::type_id::create("cc_clock_cfg", this );
      cc_clock_driver.m_clk_cfg = cc_clock_cfg;
      cc_reset_driver = reset_driver_c#( 1'b1,10,0 )::type_id::create("cc_reset_driver", this );

      aw_bp_agent = bp_agent::type_id::create( "aw_bp_agent" , this );
      w_bp_agent  = bp_agent::type_id::create( "w_bp_agent"  , this );
      b_bp_agent  = bp_agent::type_id::create( "b_bp_agent"  , this );
      ar_bp_agent = bp_agent::type_id::create( "ar_bp_agent" , this );
      r_bp_agent  = bp_agent::type_id::create( "r_bp_agent"  , this );

      aw_bp_vseq = bp_virtual_sequence::type_id::create( "aw_bp_sequence" , this);
      w_bp_vseq  = bp_virtual_sequence::type_id::create( "w_bp_sequence"  , this);
      b_bp_vseq  = bp_virtual_sequence::type_id::create( "b_bp_sequence"  , this);
      ar_bp_vseq = bp_virtual_sequence::type_id::create( "ar_bp_sequence" , this);
      r_bp_vseq  = bp_virtual_sequence::type_id::create( "r_bp_sequence"  , this);

      agent_config = dut_cfg_c::type_id::create("dut_cfg_c");

      master = axi_superset_agent_c::type_id::create("MASTER_AGENT",this);
      slave  = axi_superset_agent_c::type_id::create("SLAVE_AGENT",this);

      if_item_cfg = new("TB_TXN_CFG");
      if_item_cfg.set_id_width(16);
      if_item_cfg.set_addr_width(32);
      if_item_cfg.set_data_width(64);
      if_item_cfg.set_user_width(100);
      if_item_cfg.set_max_delay_cycles(5);

      master_cfg = axi_superset_config_c::type_id::create("MASTER_CFG", this);
      master_cfg.set_axi_version(AXI5);
      master_cfg.set_interface_name("AXI_SUPERSET_IF");
      master_cfg.set_is_master_side(1'b1);
      master_cfg.set_driver_idle_value_cfg(UNDEFINED);
      master_cfg.set_txn_config(if_item_cfg);
      master_cfg.set_is_reactive(1'b0);
      master_cfg.set_id_management_enable(1'b0);
      master_cfg.set_protocol_checker_enable(1'b1);
      master_cfg.set_covergroup_enable(1'b1);
      master_cfg.max_outstanding_write_trs = 256;
      master_cfg.max_outstanding_read_trs = 256;
      master.set_agent_config(master_cfg);

      slave_cfg = axi_superset_config_c::type_id::create("SLAVE_CFG", this);
      slave_cfg.set_axi_version(AXI5);
      slave_cfg.set_interface_name("AXI_SUPERSET_IF");
      slave_cfg.set_is_master_side(1'b0);
      slave_cfg.set_driver_idle_value_cfg(UNDEFINED);
      slave_cfg.set_txn_config(if_item_cfg);
      slave_cfg.set_is_reactive(1'b1);
      slave_cfg.set_id_management_enable(1'b0);
      slave_cfg.max_outstanding_write_trs = 256;
      slave_cfg.max_outstanding_read_trs = 256;
      slave_cfg.set_protocol_checker_enable(1'b0);
      slave_cfg.set_covergroup_enable(1'b0);
      slave.set_agent_config(slave_cfg);

      master.is_active = UVM_ACTIVE;
      slave.is_active  = UVM_ACTIVE;

      `uvm_info(get_full_name( ), "Build stage complete.", UVM_LOW)
  endfunction: build_phase

  function void connect_phase(uvm_phase phase);
      cc_clock_cfg.randomize()   with {m_starting_signal_level == 0; m_clock_frequency == 1000; m_duty_cycle == 50;};

      aw_bp_vseq.bp_sqr = aw_bp_agent.m_sequencer ;
      w_bp_vseq.bp_sqr  = w_bp_agent.m_sequencer  ;
      b_bp_vseq.bp_sqr  = b_bp_agent.m_sequencer  ;
      ar_bp_vseq.bp_sqr = ar_bp_agent.m_sequencer ;
      r_bp_vseq.bp_sqr  = r_bp_agent.m_sequencer  ;

      `uvm_info(get_full_name( ), "Connect phase complete.", UVM_LOW)
  endfunction: connect_phase

  // at end_of_elaboration, print topology and factory state to verify
  function void end_of_elaboration_phase(uvm_phase phase);
      uvm_top.print_topology();
  endfunction

endclass: dut_env
