//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
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



`ifndef __UVMT_CV32E40S_FIRMWARE_TEST_SV__
`define __UVMT_CV32E40S_FIRMWARE_TEST_SV__


/**
 *  CV32E40S "firmware" test.
 *  This class relies on a pre-existing "firmware" file written in C and/or
 *  RISC-V assembly code.  This class will invoke the riscv-gcc-toolchain to
 *  translate the firmware into a "hexfile" that is read into the CV32E40S
 *  instruction memory in the testbench module.
 *
 *  This class doesn't care what the firmware does, it mearly compiles it.
 *
 */
class uvmt_cv32e40s_firmware_test_c extends uvmt_cv32e40s_base_test_c;

   constraint env_cfg_cons {
      env_cfg.enabled         == 1;
      env_cfg.is_active       == UVM_ACTIVE;
      env_cfg.trn_log_enabled == 1;
   }

   constraint test_type_cons {
     test_cfg.tpt == PREEXISTING_SELFCHECKING;
   }


   `uvm_component_utils(uvmt_cv32e40s_firmware_test_c)

   /**
    */
   extern function new(string name="uvmt_cv32e40s_firmware_test", uvm_component parent=null);

   /**
    * Runs reset_vseq.
    */
   extern virtual task reset_phase(uvm_phase phase);

   /**
    * Loads the test program (the "firmware") into memory.
    */
   extern virtual task configure_phase(uvm_phase phase);

   /**
    *  Enable program execution, wait for completion.
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
   * Start random debug sequencer
   */
    extern virtual task random_debug();

    extern virtual task reset_debug();

    extern virtual task bootset_debug();
   /**
    *  Start the interrupt sequencer to apply random interrupts during test
    */
   extern virtual task irq_noise();

   /**
    *  Start the clic interrupt sequencer to apply random clic interrupts during test
    */
   extern virtual task clic_noise();

   /**
    *  Start the wfe wakeup sequencer to apply random wfe events during test
    */
   extern virtual task wfe_wu_noise();

   /**
    *  Start the nmi timeout watchdog to terminate tests a certain number of
    *  instructions after an nmi
    */
   extern virtual task nmi_timeout();

   /**
    *  Start the irq single-step timeout watchdog to terminate tests after
    *  a certain number of irqs and single step instructions has occurred
    */
   extern virtual task irq_single_step_timeout();

endclass : uvmt_cv32e40s_firmware_test_c


function uvmt_cv32e40s_firmware_test_c::new(string name="uvmt_cv32e40s_firmware_test", uvm_component parent=null);

   super.new(name, parent);
   `uvm_info("TEST", "This is the FIRMWARE TEST", UVM_NONE)

endfunction : new


task uvmt_cv32e40s_firmware_test_c::reset_phase(uvm_phase phase);
   super.reset_phase(phase);

endtask : reset_phase


task uvmt_cv32e40s_firmware_test_c::configure_phase(uvm_phase phase);

   super.configure_phase(phase);

endtask : configure_phase


task uvmt_cv32e40s_firmware_test_c::run_phase(uvm_phase phase);

   // start_clk() and watchdog_timer() are called in the base_test
   super.run_phase(phase);

   if ($test$plusargs("gen_random_debug")) begin
    fork
      random_debug();
    join_none
   end

   if ($test$plusargs("gen_irq_noise")) begin
    fork
      clic_noise();
      irq_noise();
    join_none
   end

   if ($test$plusargs("gen_wfe_wu_noise")) begin
     fork
       wfe_wu_noise();
     join_none
   end

   if ($test$plusargs("reset_debug")) begin
    fork
      reset_debug();
    join_none
   end
   if ($test$plusargs("debug_boot_set")) begin
    fork
      bootset_debug();
    join_none
   end

   if (env.cfg.nmi_timeout_instr > 0) begin
     fork
       nmi_timeout();
     join_none
   end

   if (env.cfg.irq_single_step_threshold > 0) begin
     fork
       irq_single_step_timeout();
     join_none
   end

   phase.raise_objection(this);
   @(posedge env_cntxt.clknrst_cntxt.vif.reset_n);
   repeat (33) @(posedge env_cntxt.clknrst_cntxt.vif.clk);
   `uvm_info("TEST", "Started RUN", UVM_NONE)
   // The firmware is expected to write exit status and pass/fail indication to the Virtual Peripheral
   wait (
          (vp_status_vif.exit_valid    == 1'b1) ||
          (vp_status_vif.tests_failed  == 1'b1) ||
          (vp_status_vif.tests_passed  == 1'b1)
        );
   repeat (100) @(posedge env_cntxt.clknrst_cntxt.vif.clk);
   //TODO: exit_value will not be valid - need to add a latch in the vp_status_vif
   `uvm_info("TEST", $sformatf("Finished RUN: exit status is %0h", vp_status_vif.exit_value), UVM_NONE)
   phase.drop_objection(this);

endtask : run_phase

task uvmt_cv32e40s_firmware_test_c::reset_debug();
    uvme_cv32e40s_random_debug_reset_c debug_vseq;
    debug_vseq = uvme_cv32e40s_random_debug_reset_c::type_id::create("random_debug_reset_vseqr");
    `uvm_info("TEST", "Applying debug_req_i at reset", UVM_NONE);
    @(negedge env_cntxt.clknrst_cntxt.vif.reset_n);

    void'(debug_vseq.randomize());
    debug_vseq.start(vsequencer);

endtask

task uvmt_cv32e40s_firmware_test_c::bootset_debug();
    uvme_cv32e40s_random_debug_bootset_c debug_vseq;
    debug_vseq = uvme_cv32e40s_random_debug_bootset_c::type_id::create("random_debug_bootset_vseqr");
    `uvm_info("TEST", "Applying single cycle debug_req after reset", UVM_NONE);
    @(negedge env_cntxt.clknrst_cntxt.vif.reset_n);

    // Delay debug_req_i by up to 35 cycles.Should hit BOOT_SET
    repeat($urandom_range(35,1)) @(posedge env_cntxt.clknrst_cntxt.vif.clk);

    void'(debug_vseq.randomize());
    debug_vseq.start(vsequencer);

endtask

task uvmt_cv32e40s_firmware_test_c::random_debug();
    uvme_cv32e40s_random_debug_c debug_vseq;
    `uvm_info("TEST", "Starting random debug in thread UVM test", UVM_NONE);

    repeat (100) @(env_cntxt.debug_cntxt.vif.mon_cb);

    debug_vseq = uvme_cv32e40s_random_debug_c::type_id::create("random_debug_vseqr");

    void'(debug_vseq.randomize());
    debug_vseq.start(vsequencer);
endtask : random_debug

task uvmt_cv32e40s_firmware_test_c::irq_noise();
  uvme_cv32e40s_interrupt_noise_c interrupt_noise_vseq;
  `uvm_info("TEST", "Starting IRQ Noise thread in UVM test", UVM_NONE);

  interrupt_noise_vseq = uvme_cv32e40s_interrupt_noise_c::type_id::create("interrupt_noise_vseqr");

  assert(interrupt_noise_vseq.randomize() with {
    reserved_irq_mask == 32'h0;
  });
  interrupt_noise_vseq.start(vsequencer);
endtask : irq_noise

task uvmt_cv32e40s_firmware_test_c::clic_noise();
  uvme_cv32e40s_clic_noise_c clic_noise_vseq;
  `uvm_info("TEST", "Starting CLIC Noise thread in UVM test", UVM_NONE);

  clic_noise_vseq = uvme_cv32e40s_clic_noise_c::type_id::create("clic_noise_vseqr");

  assert(clic_noise_vseq.randomize() with { });
  clic_noise_vseq.start(vsequencer);

endtask : clic_noise

task uvmt_cv32e40s_firmware_test_c::wfe_wu_noise();
  uvme_cv32e40s_wu_wfe_noise_vseq_c wfe_wu_noise_vseq;
  `uvm_info("TEST", "Starting WFE Wake-up noise thread in UVM test", UVM_NONE);

  wfe_wu_noise_vseq = uvme_cv32e40s_wu_wfe_noise_vseq_c::type_id::create("wfe_wu_noise_vseqr");

  assert(wfe_wu_noise_vseq.randomize() with { });
  wfe_wu_noise_vseq.start(vsequencer);

endtask : wfe_wu_noise

task uvmt_cv32e40s_firmware_test_c::nmi_timeout();
  uvme_cv32e40s_nmi_timeout_vseq_c nmi_timeout_vseq;
  `uvm_info("TEST", "Starting NMI timeout watchdog in UVM test", UVM_NONE);

  nmi_timeout_vseq = uvme_cv32e40s_nmi_timeout_vseq_c::type_id::create("nmi_timout_vseqr");

  assert(nmi_timeout_vseq.randomize() with {});
  nmi_timeout_vseq.start(vsequencer);
endtask : nmi_timeout

task uvmt_cv32e40s_firmware_test_c::irq_single_step_timeout();
  uvme_cv32e40s_irq_ss_timeout_vseq_c irq_ss_timeout_vseq;
  `uvm_info("TEST", "Starting IRQ/Single step timeout watchdog in UVM test", UVM_NONE);

  irq_ss_timeout_vseq = uvme_cv32e40s_irq_ss_timeout_vseq_c::type_id::create("irq_ss_timout_vseqr");

  assert(irq_ss_timeout_vseq.randomize() with {});
  irq_ss_timeout_vseq.start(vsequencer);
endtask : irq_single_step_timeout

`endif // __UVMT_CV32E40S_FIRMWARE_TEST_SV__
