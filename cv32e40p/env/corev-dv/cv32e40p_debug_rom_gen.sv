//Copyright 2020 Silicon Labs, Inc.
  
//This file, and derivatives thereof are licensed under the
//Solderpad License, Version 2.0 (the "License");
//Use of this file means you agree to the terms and conditions
//of the license and are in full compliance with the License.
//You may obtain a copy of the License at
//  
//    https://solderpad.org/licenses/SHL-2.0/
//  
//Unless required by applicable law or agreed to in writing, software
//and hardware implementations thereof
//distributed under the License is distributed on an "AS IS" BASIS,
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//See the License for the specific language governing permissions and
//limitations under the License.
//
//
class cv32e40p_debug_rom_gen extends riscv_debug_rom_gen;
    string debug_dret[$];
    cv32e40p_instr_gen_config cfg_corev;

    `uvm_object_utils(cv32e40p_debug_rom_gen)

    function new (string name = "");
        super.new(name);
    endfunction

    virtual function void gen_program();
        string sub_program_name[$] = {};
        privileged_reg_t status = MSTATUS;

        if(!uvm_config_db#(cv32e40p_instr_gen_config)::get(null,get_full_name(),"cv32e40p_instr_cfg", cfg_corev)) begin
          `uvm_fatal(get_full_name(), "Cannot get cv32e40p_instr_gen_config")
        end

        // CORE-V Addition
        // Insert section info so linker can place
        // debug code at the correct adress        
        instr_stream.push_back(".section .debugger, \"ax\"");

        // Randomly add a WFI at start of ddebug rom
        // This will be treaed as a NOP always, but added here to close instructon
        // combination coverage (i.e. ebreak->wfi)
        if (!cfg.no_wfi) begin
            randcase
                1:  debug_main.push_back("wfi");
                4: begin /* insert nothing */ end
            endcase
        end

        // The following is directly copied from riscv_debug_rom_gen.sv
        // Changes: 
        // - Altering the stack push/pop to use custom debugger stack            
        if (!cfg.gen_debug_section) begin
            // If the debug section should not be generated, we just populate it
            // with a dret instruction.
            debug_main = {dret};
            gen_section($sformatf("%0sdebug_rom", hart_prefix(hart)), debug_main);
        end else begin
            // Check the debugger stack pointer to check for a null pointer in cfg.dp
            // and initialize
            debug_main.push_back($sformatf("bne x%0d, zero, dp_init_done", cfg_corev.dp));
            debug_main.push_back($sformatf("la  x%0d, debugger_stack_end", cfg_corev.dp));
            debug_main.push_back($sformatf("dp_init_done:"));

            if (cfg.enable_ebreak_in_debug_rom) begin
                gen_ebreak_header();
            end
            // Need to save off GPRs to avoid modifying program flow
            push_gpr_to_debugger_stack(cfg_corev, debug_main);

            // Need to save off FPRs incase f-extension instructions are used to avoid modifying program flow
            if(cfg.enable_floating_point && !cfg.enable_fp_in_x_regs) begin
                push_fpr_to_debugger_stack(cfg_corev, debug_main, status);
            end
            // Signal that the core entered debug rom only if the rom is actually
            // being filled with random instructions to prevent stress tests from
            // having to execute unnecessary push/pop of GPRs on the stack ever
            // time a debug request is sent
            gen_signature_handshake(debug_main, CORE_STATUS, IN_DEBUG_MODE);
            if (cfg_corev.setup_debug_trigger_on_addr_match) begin
                // Setup tdata1 and tdata2 for trigger breakpoint
                if (!cfg.enable_debug_single_step)
                  gen_dbg_trigger_setup_with_addr_match(1); //use_dscratch0=1, num of trigger iterations > 1 allowed
                else
                  gen_dbg_trigger_setup_with_addr_match(0); //use_dscratch0=0, num of trigger iterations = 1
            end
            if (cfg.enable_ebreak_in_debug_rom) begin
                // send dpc and dcsr to testbench, as this handshake will be
                // executed twice due to the ebreak loop, there should be no change
                // in their values as by the Debug Mode Spec Ch. 4.1.8
                gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DCSR));
                gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DPC));
            end
            if (cfg.set_dcsr_ebreak) begin
                // We want to set dcsr.ebreak(m/s/u) to 1'b1, depending on what modes
                // are available.
                // TODO(udinator) - randomize the dcsr.ebreak setup
                gen_dcsr_ebreak();
            end
            if (cfg.enable_debug_single_step) begin
                if ((cfg_corev.debug_trigger_before_single_step & cfg_corev.setup_debug_trigger_on_addr_match) ||
                    (cfg_corev.debug_ebreak_before_single_step & cfg_corev.set_dcsr_ebreak))
                  gen_single_step_logic_if_trigger_ebreak();
                else
                  gen_single_step_logic();
            end
            gen_dpc_update();
            // write DCSR to the testbench for any analysis
            gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DCSR));
            if (cfg.enable_ebreak_in_debug_rom || cfg.set_dcsr_ebreak) begin
                gen_increment_ebreak_counter();
            end
            format_section(debug_main);
            gen_sub_program(hart, sub_program[hart], sub_program_name,
                            cfg.num_debug_sub_program, 1'b1, "debug_sub");
            main_program[hart] = cv32e40p_instr_sequence::type_id::create("debug_program");
            main_program[hart].instr_cnt = cfg.debug_program_instr_cnt;            
            main_program[hart].is_debug_program = 1;
            main_program[hart].cfg = cfg;
            `DV_CHECK_RANDOMIZE_FATAL(main_program[hart])
            main_program[hart].gen_instr(.is_main_program(1'b1), .no_branch(cfg.no_branch_jump));
            gen_callstack(main_program[hart], sub_program[hart], sub_program_name,
                            cfg.num_debug_sub_program);
            main_program[hart].post_process_instr();
            main_program[hart].generate_instr_stream(.no_label(1'b1));
            insert_sub_program(sub_program[hart], debug_main);
            debug_main = {debug_main, main_program[hart].instr_string_list};
            

            // Create the ebreak end
            if (cfg.enable_ebreak_in_debug_rom) begin
                gen_ebreak_footer();
            end            

            //pop FPRs for f-extension instructions
            if(cfg.enable_floating_point && !cfg.enable_fp_in_x_regs) begin
                pop_fpr_from_debugger_stack(cfg_corev, debug_end, status);
            end

            pop_gpr_from_debugger_stack(cfg_corev, debug_end);
            if (cfg.enable_ebreak_in_debug_rom) begin
                gen_restore_ebreak_scratch_reg();
            end

            // Create the debug_dret section
            //pop_gpr_from_debugger_stack(cfg_corev, debug_dret);
            //debug_dret = {debug_dret, dret};

            //format_section(debug_end);
            gen_section($sformatf("%0sdebug_rom", hart_prefix(hart)), debug_main);

            // Randomly add a WFI at end of debug rom
            // This will be treaed as a NOP always, but added here to close instructon
            // combination coverage (i.e. ebreak->wfi)
            if (!cfg.no_wfi) begin
                randcase
                    1:  debug_end.push_back("wfi");
                    4: begin /* insert nothing */ end
                endcase
            end

            debug_end = {debug_end, dret};            

            gen_section($sformatf("%0sdebug_end", hart_prefix(hart)), debug_end);            
        end
        gen_debug_exception_handler();
    endfunction : gen_program

    virtual function void gen_debug_exception_handler();
        // Insert section info so linker can place
        // debug exception code at the correct adress
        instr_stream.push_back(".section .debugger_exception, \"ax\"");
        super.gen_debug_exception_handler();

        // Inser section info to place remaining code in the 
        // original section
        instr_stream.push_back(".section text");
    endfunction : gen_debug_exception_handler

    // Function: gen_dbg_trigger_setup_with_addr_match
    // Inputs int use_dscratch0, dscratch0 is used to store number of
    // iterations and overlaps its usage for single step routine as well
    // So this input is to differentiate code generation for different
    // scenrios with or without single step overlap in the tests
    //
    // Description: Setup trigger breakpoint setup with instruction address
    // match. Uses random config item trigger_addr_offset to set trigger
    // address adding this random offset to depc value
    // Use config trigger_iterations with use_dscratch0=1 to setup trigger
    // multiple times in a single test.
    virtual function void gen_dbg_trigger_setup_with_addr_match(int use_dscratch0=0);

        if(use_dscratch0) begin
          str = {$sformatf("csrw 0x%0x, x%0d", DSCRATCH1, cfg.scratch_reg),
                 // Only un-set tdata1.execute if it is 1 and the iterations counter
                 // is at 0 (has finished expected iterations)
                 $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, TDATA1),
                 $sformatf("andi x%0d, x%0d, 4", cfg.scratch_reg, cfg.scratch_reg),
                 // If tdata1.execute is 0, set to 1 and set the counter
                 $sformatf("beqz x%0d, 1f", cfg.scratch_reg),
                 // Check DCSR.cause, if cause was trigger-module, continue
                 // else dont change trigger configuration
                 $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DCSR),
                 $sformatf("slli x%0d, x%0d, 0x17", cfg.scratch_reg, cfg.scratch_reg),
                 $sformatf("srli x%0d, x%0d, 0x1d", cfg.scratch_reg, cfg.scratch_reg),
                 $sformatf("li x%0d, 0x2", cfg.gpr[0]),
                 $sformatf("bne x%0d, x%0d, 3f", cfg.scratch_reg, cfg.gpr[0]),

                 $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH0),
                 // if the counter is greater than 0, decrement and continue further trigger iterations
                 $sformatf("bgtz x%0d, 2f", cfg.scratch_reg),
                 $sformatf("csrc 0x%0x, 0x4", TDATA1),
                 //Set TDATA2 = 0xffff_ffff as a hint for sw to skip any
                 //subsequent debug rom entry from re-enabling trigger execute
                 $sformatf("li x%0d, 0xffffffff", cfg.scratch_reg),
                 $sformatf("csrw 0x%0x, x%0d", TDATA2, cfg.scratch_reg),
                 $sformatf("beqz x0, 3f"),
                 // Set tdata1.execute, set tdata2 and the num_iterations counter, if
                 // TDATA2 != 0xffff_ffff
                 $sformatf("1: csrr x%0d, 0x%0x", cfg.scratch_reg, TDATA2),
                 $sformatf("li x%0d, 0xffffffff", cfg.gpr[0]),
                 $sformatf("beq x%0d, x%0d, 3f", cfg.scratch_reg, cfg.gpr[0]),
                 $sformatf("csrs 0x%0x, 0x4", TDATA1),
                 $sformatf("csrr  x%0d, 0x%0x", cfg.scratch_reg, DPC),
                 $sformatf("addi  x%0d, x%0d, %0d", cfg.scratch_reg, cfg.scratch_reg, cfg_corev.trigger_addr_offset),
                 $sformatf("csrw 0x%0x, x%0d", TDATA2, cfg.scratch_reg),
                 $sformatf("li x%0d, %0d", cfg.scratch_reg, cfg_corev.trigger_iterations),
                 $sformatf("csrw 0x%0x, x%0d", DSCRATCH0, cfg.scratch_reg),
                 $sformatf("beqz x0, 3f"),
                 // Decrement dscratch counter and set tdata2
                 $sformatf("2: csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH0),
                 $sformatf("addi x%0d, x%0d, -1", cfg.scratch_reg, cfg.scratch_reg),
                 $sformatf("csrw 0x%0x, x%0d", DSCRATCH0, cfg.scratch_reg),
                 $sformatf("csrr  x%0d, 0x%0x", cfg.scratch_reg, DPC),
                 $sformatf("addi  x%0d, x%0d, %0d", cfg.scratch_reg, cfg.scratch_reg, cfg_corev.trigger_addr_offset),
                 $sformatf("csrw 0x%0x, x%0d", TDATA2, cfg.scratch_reg),
                 // Restore scratch_reg value from dscratch1
                 $sformatf("3: csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH1)};
        end
        else begin
          str = {$sformatf("csrw 0x%0x, x%0d", DSCRATCH1, cfg.scratch_reg),
                 // Only un-set tdata1.execute if it is 1 and the iterations counter
                 // is at 0 (has finished expected iterations)
                 $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, TDATA1),
                 $sformatf("andi x%0d, x%0d, 4", cfg.scratch_reg, cfg.scratch_reg),
                 // If tdata1.execute is 0, set to 1 else clear
                 $sformatf("beqz x%0d, 1f", cfg.scratch_reg),
                 // Check DCSR.cause, if cause was trigger-module, continue
                 // else dont change trigger configuration
                 $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DCSR),
                 $sformatf("slli x%0d, x%0d, 0x17", cfg.scratch_reg, cfg.scratch_reg),
                 $sformatf("srli x%0d, x%0d, 0x1d", cfg.scratch_reg, cfg.scratch_reg),
                 $sformatf("li x%0d, 0x2", cfg.gpr[0]),
                 $sformatf("bne x%0d, x%0d, 3f", cfg.scratch_reg, cfg.gpr[0]),

                 $sformatf("csrc 0x%0x, 0x4", TDATA1),
                 //Set TDATA2 = 0xffff_ffff as a hint for sw to skip any
                 //subsequent debug rom entry from re-enabling trigger execute
                 $sformatf("li x%0d, 0xffffffff", cfg.scratch_reg),
                 $sformatf("csrw 0x%0x, x%0d", TDATA2, cfg.scratch_reg),
                 $sformatf("beqz x0, 3f"),
                 // Set tdata1.execute, set tdata2, if
                 // TDATA2 != 0xffff_ffff
                 $sformatf("1: csrr x%0d, 0x%0x", cfg.scratch_reg, TDATA2),
                 $sformatf("li x%0d, 0xffffffff", cfg.gpr[0]),
                 $sformatf("beq x%0d, x%0d, 3f", cfg.scratch_reg, cfg.gpr[0]),
                 $sformatf("csrs 0x%0x, 0x4", TDATA1),
                 $sformatf("csrr  x%0d, 0x%0x", cfg.scratch_reg, DPC),
                 $sformatf("addi  x%0d, x%0d, %0d", cfg.scratch_reg, cfg.scratch_reg, cfg_corev.trigger_addr_offset),
                 $sformatf("csrw 0x%0x, x%0d", TDATA2, cfg.scratch_reg),
                 $sformatf("beqz x0, 3f"),
                 // Restore scratch_reg value from dscratch1
                 $sformatf("3: csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH1)};
        end
        debug_main = {debug_main, str};

    endfunction

    // Function: gen_single_step_logic_if_trigger_ebreak
    // Description: The logic in this function is to setup single stepping,
    // after 1 debug trigger or debug ebreak is triggered.
    // This covers cases with trigger/ebreak and single step
    // Debug entry cause Trigger/Ebreak -> Single Step Enable
    virtual function void gen_single_step_logic_if_trigger_ebreak();
      str = {$sformatf("csrw 0x%0x, x%0d", DSCRATCH1, cfg.scratch_reg),
             // Only un-set dcsr.step if it is 1 and the iterations counter
             // is at 0 (has finished iterating)
             $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DCSR),
             $sformatf("andi x%0d, x%0d, 4", cfg.scratch_reg, cfg.scratch_reg),
             // If dcsr.step is 0, set to 1 and set the counter, if
             // trigger was the debug entry cause
             $sformatf("beqz x%0d, 1f", cfg.scratch_reg),
             // Check DCSR.cause, if cause was step, continue
             // else dont change step configuration
             $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DCSR),
             $sformatf("slli x%0d, x%0d, 0x17", cfg.scratch_reg, cfg.scratch_reg),
             $sformatf("srli x%0d, x%0d, 0x1d", cfg.scratch_reg, cfg.scratch_reg),
             $sformatf("li x%0d, 0x4", cfg.gpr[0]),
             $sformatf("bne x%0d, x%0d, 3f", cfg.scratch_reg, cfg.gpr[0]),

             $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH0),
             // if the counter is greater than 0, decrement and continue single stepping
             $sformatf("bgtz x%0d, 2f", cfg.scratch_reg),
             $sformatf("csrc 0x%0x, 0x4", DCSR),
             //Set DSCRATCH0 = 0xffff_ffff as a hint for sw to skip any
             //subsequent debug rom entry from re-enabling step
             $sformatf("li x%0d, 0xffffffff", cfg.scratch_reg),
             $sformatf("csrw 0x%0x, x%0d", DSCRATCH0, cfg.scratch_reg),
             $sformatf("beqz x0, 3f"),
             // Check DCSR.cause, if cause was trigger-module breakpoint or ebreak, set dcsr.step
             // else dont change configuration
             $sformatf("1: csrr x%0d, 0x%0x", cfg.scratch_reg, DCSR),
             $sformatf("slli x%0d, x%0d, 0x17", cfg.scratch_reg, cfg.scratch_reg),
             $sformatf("srli x%0d, x%0d, 0x1d", cfg.scratch_reg, cfg.scratch_reg),
             $sformatf("li x%0d, 0x1", cfg.gpr[0]),
             $sformatf("beq x%0d, x%0d, 11f", cfg.scratch_reg, cfg.gpr[0]),
             $sformatf("li x%0d, 0x2", cfg.gpr[0]),
             $sformatf("beq x%0d, x%0d, 11f", cfg.scratch_reg, cfg.gpr[0]),
             $sformatf("beqz x0, 3f"),
             // Set dcsr.step and the num_iterations counter, if
             // DSCRATCH0 != 0xffff_ffff
             $sformatf("11: csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH0),
             $sformatf("li x%0d, 0xffffffff", cfg.gpr[0]),
             $sformatf("beq x%0d, x%0d, 3f", cfg.scratch_reg, cfg.gpr[0]),
             $sformatf("csrs 0x%0x, 0x4", DCSR),
             $sformatf("li x%0d, %0d", cfg.scratch_reg, cfg.single_step_iterations),
             $sformatf("csrw 0x%0x, x%0d", DSCRATCH0, cfg.scratch_reg),
             $sformatf("beqz x0, 3f"),
             // Decrement dscratch counter
             $sformatf("2: csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH0),
             $sformatf("addi x%0d, x%0d, -1", cfg.scratch_reg, cfg.scratch_reg),
             $sformatf("csrw 0x%0x, x%0d", DSCRATCH0, cfg.scratch_reg),
             // Restore scratch_reg value from dscratch1
             $sformatf("3: csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH1)
      };
      debug_main = {debug_main, str};
      // write dpc to testbench
      gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DPC));
      // write out the counter to the testbench
      gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DSCRATCH0));
    endfunction

endclass : cv32e40p_debug_rom_gen

