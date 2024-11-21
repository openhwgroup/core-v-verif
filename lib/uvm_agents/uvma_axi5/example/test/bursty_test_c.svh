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
//  Description : This class creates, configures and start a test with
//                the bursty_sequence_c class
//
//
// ----------------------------------------------------------------------------
class bursty_test_c extends base_test_c;
  `uvm_component_utils(bursty_test_c)

  uvma_axi_master_sequence_c        master_seq[5];
  uvma_axi_master_write_sequence_c  master_write_seq[5];
  uvma_axi_master_read_sequence_c   master_read_seq[5];
  uvma_axi_master_excl_sequence_c   master_excl_seq[5];

  uvma_axi_slv_seq_c  slave_seq;

  //---------------------------
  // Factory
  //---------------------------
  function new(string name, uvm_component parent);
      super.new(name, parent);
  endfunction: new

  //---------------------------
  // Build phase
  //---------------------------
  function void build_phase(uvm_phase phase);
      super.build_phase(phase);
  endfunction: build_phase

  //---------------------------
  // Run phase
  //---------------------------
  virtual task main_phase(uvm_phase phase);
      int num_seq = 1;

      fork
        env.aw_bp_vseq.start(null);
        env.w_bp_vseq.start(null);
        env.b_bp_vseq.start(null);
        env.ar_bp_vseq.start(null);
        env.r_bp_vseq.start(null);
        slave_seq.start(env.slave.vsequencer);
      join_none

      phase.raise_objection(this);

      for ( int i = 0 ; i < num_seq ; i ++) begin
        // FIXME : passing the argument via the create doesn't work. Need to
        // pass via the function new.
        master_seq[i]       = uvma_axi_master_sequence_c::type_id::create( $sformatf("master_seq_%0d", i));
        master_write_seq[i] = uvma_axi_master_write_sequence_c::type_id::create( $sformatf("master_write_seq_%0d", i));
        master_read_seq[i]  = uvma_axi_master_read_sequence_c::type_id::create( $sformatf("master_read_seq_%0d", i));
        master_excl_seq[i]  = uvma_axi_master_excl_sequence_c::type_id::create( $sformatf("master_excl_seq_%0d", i));
        master_seq[i].set_num_txn( (i+1)*300 );
        master_write_seq[i].set_num_txn( (i+1)*300 );
        master_read_seq[i].set_num_txn( (i+1)*300 );
        master_excl_seq[i].set_num_txn( (i+1)*300 );

        master_seq[i]       = new( $sformatf("master_seq_%0d"       , i), (i + 1)*300 );
        master_write_seq[i] = new( $sformatf("master_write_seq_%0d" , i), (i + 1)*300 );
        master_read_seq[i]  = new( $sformatf("master_read_seq_%0d"  , i), (i + 1)*300 );
        master_excl_seq[i]  = new( $sformatf("master_excl_seq_%0d"  , i), (i + 1)*10 );
        //
        slave_seq = uvma_axi_slv_seq_c::type_id::create("slave_seq");
      end

      fork begin
        for ( int i = 0 ; i < num_seq ; i ++) begin
          fork
            automatic int j = i;
            master_seq[j].start(env.master.vsequencer);
            master_write_seq[j].start(env.master.vsequencer);
            master_read_seq[j].start(env.master.vsequencer);
            // master_excl_seq[j].start(env.master.m_sequencer);
          join_none
        end
        wait fork;
      end join
      // wait fork;

      phase.drop_objection(this);
      env.aw_bp_vseq.bp_sqr.stop_sequences();
      env.w_bp_vseq.bp_sqr.stop_sequences();
      env.b_bp_vseq.bp_sqr.stop_sequences();
      env.ar_bp_vseq.bp_sqr.stop_sequences();
      env.r_bp_vseq.bp_sqr.stop_sequences();
      env.slave.vsequencer.stop_sequences();

      `uvm_info("TEST", "Sequence proto is ending", UVM_DEBUG)

      super.main_phase(phase);
  endtask: main_phase

endclass: bursty_test_c
