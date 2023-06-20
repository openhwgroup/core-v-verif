//
// Copyright 2023 OpenHW Group
// Copyright 2023 Dolphin Design
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

`ifndef __UVMT_CV32E40P_RISCOF_FIRMWARE_TEST_SV__
`define __UVMT_CV32E40P_RISCOF_FIRMWARE_TEST_SV__

/**
 *  CV32E40P "RISCOF firmware" test.
 *  This test is similar to other uvmt firmware test but this is
 *  specifically for riscof compliance test suite simulations.
 *  This class relies on a pre-existing "firmware" file written in C and/or
 *  RISC-V assembly code, in this case coming from riscof test suite.
 *  This class will invoke the riscv-gcc-toolchain to translate
 *  the firmware into a "hexfile" that is read into the CV32E40P
 *  instruction memory in the testbench module.
 *
 *  At the end of the test the test implements function write_riscof_signature()
 *  to dump the signature from CV32E40P RTL for comparison with riscof ref
 *  model
 *
 *  This class doesn't care what the firmware does, it mearly loads the
 *  compiled elf to memory for starts simulation on CV32E40P RTL.
 *
 */
class uvmt_cv32e40p_riscof_firmware_test_c extends uvmt_cv32e40p_base_test_c;

   localparam RISCOF_SIGNATURE_HEADER = 32'h6f5ca309;
   localparam RISCOF_TEST_BOOT_ADDRESS = 32'h80000000;
   localparam RISCOF_TEST_SIG_LOCATION_OFFSET = 32'h03FF1000; // Fixed addr offset wrt BOOT_ADDRESS defined in linker file for riscof sim to store test signature start addr

    constraint env_cfg_cons {
       env_cfg.enabled         == 1;
       env_cfg.is_active       == UVM_ACTIVE;
       env_cfg.trn_log_enabled == 0;
       env_cfg.clknrst_cfg.trn_log_enabled           == 0;
       env_cfg.interrupt_cfg.trn_log_enabled         == 0;
       env_cfg.debug_cfg.trn_log_enabled             == 0;
       env_cfg.obi_memory_instr_cfg.trn_log_enabled  == 0;
       env_cfg.obi_memory_data_cfg.trn_log_enabled   == 0;
       env_cfg.rvfi_cfg.trn_log_enabled              == 0;

    }
    `uvm_component_utils_begin(uvmt_cv32e40p_riscof_firmware_test_c)
    `uvm_object_utils_end

    constraint test_type_cons {
      test_cfg.tpt == PREEXISTING_SELFCHECKING;
    }

    extern function new(string name="uvmt_cv32e40p_riscof_firmware_test", uvm_component parent=null);

    extern function void build_phase(uvm_phase phase);
 
    /**
    * Runs reset_vseq.
    */
    extern virtual task reset_phase(uvm_phase phase);

    /**
     * Loads the test program (the "firmware") into memory.
     */
    extern virtual task configure_phase(uvm_phase phase);

    /**
    * post_randomize
    */
    extern function void post_randomize();

    /**
     *  Enable program execution, wait for completion.
     */
    extern virtual task run_phase(uvm_phase phase);

    extern function void write_riscof_signature();

    //Function to create empty signature file to avoid issues with
    //riscof report generation with tests which exit with timeout/fatal
    //and exit without dumping signature
    extern function void write_riscof_empty_signature();


endclass : uvmt_cv32e40p_riscof_firmware_test_c

function uvmt_cv32e40p_riscof_firmware_test_c::new(string name="uvmt_cv32e40p_riscof_firmware_test", uvm_component parent=null);

    super.new(name, parent);
    `uvm_info("TEST", "This is the RISCOF FIRMWARE TEST", UVM_NONE)

endfunction : new

function void uvmt_cv32e40p_riscof_firmware_test_c::build_phase(uvm_phase phase);

    super.build_phase(phase);

    `uvm_info("TEST", $sformatf("Randomize from TEST class"), UVM_NONE)
    if (!this.randomize()) begin
      `uvm_fatal("TEST", "Failed to randomize test");
    end
   
    env_cfg.boot_addr = RISCOF_TEST_BOOT_ADDRESS; //Defined inside riscof linker file
    test_cfg.watchdog_timeout = 10_000_000; // reduce timeout

endfunction : build_phase

task uvmt_cv32e40p_riscof_firmware_test_c::reset_phase(uvm_phase phase);
    super.reset_phase(phase);

endtask : reset_phase


task uvmt_cv32e40p_riscof_firmware_test_c::configure_phase(uvm_phase phase);

    super.configure_phase(phase);

    //Create Initial DUT Signature file
    write_riscof_empty_signature();

endtask : configure_phase

function void uvmt_cv32e40p_riscof_firmware_test_c::post_randomize();

    `uvm_info("TEST", "Post Randomize function ", UVM_NONE)

endfunction : post_randomize


task uvmt_cv32e40p_riscof_firmware_test_c::run_phase(uvm_phase phase);

    super.run_phase(phase);

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
    `uvm_info("TEST", $sformatf("Finished RUN: exit status is %0h", vp_status_vif.exit_value), UVM_NONE)

    //Create Signature for DUT sim
    write_riscof_signature();

    phase.drop_objection(this);

endtask : run_phase

function void uvmt_cv32e40p_riscof_firmware_test_c::write_riscof_signature();
    bit[31:0]     mem_read;
    int           sig_fd;
    string        sig_file;
    bit[31:0]     signature_start_address;
    bit[31:0]     signature_end_address;
    bit[31:0]     sig_i;
    int           i;
    bit[31:0]     test_sig_begin_addr;
    bit[31:0]     test_sig_end_addr;

    //Get the Signature begin and end addresses by reading the mailbox address defined in linker file
    test_sig_begin_addr = RISCOF_TEST_BOOT_ADDRESS + RISCOF_TEST_SIG_LOCATION_OFFSET;
    test_sig_end_addr = RISCOF_TEST_BOOT_ADDRESS + RISCOF_TEST_SIG_LOCATION_OFFSET + 4;

    //Read the signature start and end addresses from memory
    mem_read[7:0] = env_cntxt.mem.read(test_sig_begin_addr+0);
    mem_read[15:8] = env_cntxt.mem.read(test_sig_begin_addr+1);
    mem_read[23:16] = env_cntxt.mem.read(test_sig_begin_addr+2);
    mem_read[31:24] = env_cntxt.mem.read(test_sig_begin_addr+3);
    signature_start_address = mem_read;

    mem_read[7:0] = env_cntxt.mem.read(test_sig_end_addr+0);
    mem_read[15:8] = env_cntxt.mem.read(test_sig_end_addr+1);
    mem_read[23:16] = env_cntxt.mem.read(test_sig_end_addr+2);
    mem_read[31:24] = env_cntxt.mem.read(test_sig_end_addr+3);
    signature_end_address = mem_read;
    `uvm_info("TEST", $sformatf("riscv_arch_test signature_start_address = %0h", signature_start_address), UVM_LOW)
    `uvm_info("TEST", $sformatf("riscv-arch_test signature_end_address = %0h", signature_end_address), UVM_LOW)


    if ($value$plusargs("signature=%s", sig_file)) begin
        sig_fd = $fopen(sig_file, "w");
    end
    else begin
        sig_file = "DUT-cv32e40p.signature";
        sig_fd = $fopen(sig_file, "w");
    end
    if (sig_fd == 0) `uvm_fatal("TEST", $sformatf("Could not open file %s for writing", sig_file));
     
    `uvm_info("RISCOF_SIG_WRITE", "Dumping Riscof signature", UVM_NONE)

    //Dump signature in the output DUT signature file
    for (sig_i=signature_start_address; sig_i<signature_end_address; sig_i += 4) begin
        mem_read[7:0] = env_cntxt.mem.read(sig_i+0);
        mem_read[15:8] = env_cntxt.mem.read(sig_i+1);
        mem_read[23:16] = env_cntxt.mem.read(sig_i+2);
        mem_read[31:24] = env_cntxt.mem.read(sig_i+3);

        $fdisplay(sig_fd, "%x", mem_read);
    end

endfunction : write_riscof_signature

function void uvmt_cv32e40p_riscof_firmware_test_c::write_riscof_empty_signature();
    bit[31:0]   sig_value;
    int         sig_fd;
    string      sig_file;
    bit[31:0]   sig_i;

    if ($value$plusargs("signature=%s", sig_file)) begin
        sig_fd = $fopen(sig_file, "w");
    end
    else begin
        sig_file = "DUT-cv32e40p.signature";
        sig_fd = $fopen(sig_file, "w");
    end
    if (sig_fd == 0) `uvm_fatal("TEST", $sformatf("Could not open file %s for writing", sig_file));

    `uvm_info("RISCOF_SIG_WRITE", "Initialize Riscof signature", UVM_NONE)

    sig_value = RISCOF_SIGNATURE_HEADER;
    $fdisplay(sig_fd, "%x", sig_value);

endfunction : write_riscof_empty_signature

`endif // __UVMT_CV32E40P_RISCOF_FIRMWARE_TEST_SV__
