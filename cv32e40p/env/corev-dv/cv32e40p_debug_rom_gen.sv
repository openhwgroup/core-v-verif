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

    // Directed instruction ratio, occurance per 1000 instructions
    int unsigned             directed_instr_stream_ratio_for_debug_prog[string];

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
            // workaround to handle issue if debug entry during test_done by preventing load instr uses xreg with print_port value
            rand_xreg_after_push_gpr_to_debugger_stack(cfg_corev, debug_main);

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
            init_dbg_rom_str_reserved_gpr();

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
            if(cfg_corev.insert_rand_directed_instr_stream_in_debug_program) begin
              get_directed_instr_stream_for_debug_program();
              generate_directed_instr_stream_for_debug_program(.hart(hart),
                                                               .label(main_program[hart].label_name),
                                                               .original_instr_cnt(main_program[hart].instr_cnt),
                                                               .min_insert_cnt(1),
                                                               .instr_stream(main_program[hart].directed_instr));
            end
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

        // In CV32E40P there is no way to know the Instruction address
        // that caused the debug exception entry.
        // In these tests, this scenario is simply handled with assumptions:
        //    - The random illegal exception in debug program is generated
        //      as part of random instructions
        //    - And debug stack pointer is not used in any other random
        //      instruction in debug program
        //  With these 2 assumptions to ensure smooth continuity of rest of
        //  the test program, we simply jump to "debug_end" section to exit
        //  the debug rom properly.

        if (cfg.gen_debug_section) begin
          str = {$sformatf("la x%0d, debug_end", cfg.scratch_reg),
                 $sformatf("jalr x0, x%0d, 0", cfg.scratch_reg),
                 "dret"};
          gen_section($sformatf("%0sdebug_exception", hart_prefix(hart)), str);
        end else begin
          super.gen_debug_exception_handler();
        end

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

    // Override base class gen_dpc_update()
    // Check dcsr.cause, for ebreak as debug entry cause.
    // With RV32X enabled, check for ebreak instr on the last instr of hwloop
    // If true, then
    // (a) Set DPC to first instr of hwloop body if LPCOUNTx >= 2
    // (b) Decrement the LPCOUNTx if LPCOUNTx >= 1
    // Else
    // By Default for all other cases increment DPC by 4
    // as ebreak will set set dpc to its own address, which will cause an
    // infinite loop.
    virtual function void gen_dpc_update();
      str = {$sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DCSR),
             $sformatf("slli x%0d, x%0d, 0x17", cfg.scratch_reg, cfg.scratch_reg),
             $sformatf("srli x%0d, x%0d, 0x1d", cfg.scratch_reg, cfg.scratch_reg),
             $sformatf("li x%0d, 0x1", cfg.gpr[0]),
             $sformatf("bne x%0d, x%0d, 8f", cfg.scratch_reg, cfg.gpr[0])};
      debug_main = {debug_main, str};

      if (riscv_instr_pkg::RV32X inside {riscv_instr_pkg::supported_isa}) begin
        str = {
               `COMMON_EXCEPTION_XEPC_HANDLING_CODE_WITH_HWLOOP_CHECK(cfg.gpr[0], cfg.scratch_reg, DPC)
               };
        debug_main = {debug_main, str};
        str = {"8: nop"};
        debug_main = {debug_main, str};
      end else begin
        increment_csr(DPC, 4, debug_main);
        str = {"8: nop"};
        debug_main = {debug_main, str};
      end
    endfunction

    // Function to initialize GPR reserved for stores
    virtual function void init_dbg_rom_str_reserved_gpr();
      string reg_name;
      bit [31:0] reg_val;

      // Initialize reserved registers for store instr
      if (!cfg_corev.no_load_store) begin
        reg_name = cfg_corev.str_rs1.name();
        reg_val = 32'h88000000; // FIXME : Remove hardcoded value to allow configuration based on linker
        str = {$sformatf("li %0s, 0x%0x", reg_name.tolower(), reg_val)};
        debug_main = {debug_main, str};

        reg_name = cfg_corev.str_rs3.name();
        reg_val = $urandom_range(0,255); // FIXME : include negative also
        str = {$sformatf("li %0s, 0x%0x", reg_name.tolower(), reg_val)};
        debug_main = {debug_main, str};
      end
    endfunction

    // Generate directed instruction stream in debug program based on the ratio setting
    virtual function void generate_directed_instr_stream_for_debug_program(input int hart,
                                                                           input string label,
                                                                           input int unsigned original_instr_cnt,
                                                                           input int unsigned min_insert_cnt = 0,
                                                                           input bit kernel_mode = 0,
                                                                           output riscv_instr_stream instr_stream[]);
      uvm_object object_h;
      riscv_rand_instr_stream new_instr_stream;
      int unsigned instr_insert_cnt;
      int unsigned idx;
      uvm_coreservice_t coreservice = uvm_coreservice_t::get();
      uvm_factory factory = coreservice.get_factory();
      if(cfg.no_directed_instr) return;
      foreach(directed_instr_stream_ratio_for_debug_prog[instr_stream_name]) begin
        instr_insert_cnt = original_instr_cnt * directed_instr_stream_ratio_for_debug_prog[instr_stream_name] / 1000;
        if(instr_insert_cnt <= min_insert_cnt) begin
          instr_insert_cnt = min_insert_cnt;
        end
        `ifdef DSIM
          // Temporarily skip loop instruction for dsim as it cannot support dynamic array
          // randomization
          if (uvm_is_match("*loop*", instr_stream_name)) begin
            `uvm_info(`gfn, $sformatf("%0s is skipped", instr_stream_name), UVM_LOW)
            continue;
          end
        `endif
        `uvm_info(get_full_name(), $sformatf("Insert directed instr stream %0s %0d/%0d times",
                                   instr_stream_name, instr_insert_cnt, original_instr_cnt), UVM_LOW)
        for(int i = 0; i < instr_insert_cnt; i++) begin
          string name = $sformatf("%0s_%0d", instr_stream_name, i);
          object_h = factory.create_object_by_name(instr_stream_name, get_full_name(), name);
          if(object_h == null) begin
            `uvm_fatal(get_full_name(), $sformatf("Cannot create instr stream %0s", name))
          end
          if($cast(new_instr_stream, object_h)) begin
            new_instr_stream.cfg = cfg;
            new_instr_stream.hart = hart;
            new_instr_stream.label = $sformatf("%0s_%0d", label, idx);
            new_instr_stream.kernel_mode = kernel_mode;
            `DV_CHECK_RANDOMIZE_FATAL(new_instr_stream)
            instr_stream = {instr_stream, new_instr_stream};
          end else begin
            `uvm_fatal(get_full_name(), $sformatf("Cannot cast instr stream %0s", name))
          end
          idx++;
        end
      end
      instr_stream.shuffle();
    endfunction

    virtual function void add_directed_instr_stream_in_debug_program(string name, int unsigned ratio);
      directed_instr_stream_ratio_for_debug_prog[name] = ratio;
      `uvm_info(`gfn, $sformatf("Adding directed instruction stream for debug program:%0s ratio:%0d/1000", name, ratio),
                UVM_LOW)
    endfunction

    // Similar to get_directed_instr_stream is asm_program
    // Use this plusarg cfg along with "test_rand_directed_instr_stream_num" and
    // "rand_directed_instr_*" to select 1 single directed_instr_stream randomly
    // and insert in the generated instruction stream.
    virtual function void get_directed_instr_stream_for_debug_program();
      string args, val;
      string stream_name_opts, stream_freq_opts;
      string stream_name;
      int stream_freq;
      string opts[$];
      int dir_stream_id = 0;

      if(cfg_corev.insert_rand_directed_instr_stream_in_debug_program) begin
        //test_rand_directed_instr_stream_num specify the total num of rand_* streams to select from
        dir_stream_id = $urandom_range(0,cfg_corev.test_rand_directed_instr_stream_num-1);
        //Specify rand_directed_instr_0="" to rand_directed_instr_n="" as streams to randomize
        args = $sformatf("rand_directed_instr_%0d=", dir_stream_id);
        stream_name_opts = $sformatf("rand_stream_name_%0d=", dir_stream_id);
        stream_freq_opts = $sformatf("rand_stream_freq_%0d=", dir_stream_id);
        `uvm_info("cv32e40p_debug_rom_gen", $sformatf("Randomly selected dir_stream_id : %0d", dir_stream_id), UVM_NONE)
        if ($value$plusargs({args,"%0s"}, val)) begin
          uvm_split_string(val, ",", opts);
          if (opts.size() != 2) begin
            `uvm_fatal(`gfn, $sformatf(
              "Incorrect directed instruction format : %0s, expect: name,ratio", val))
          end else begin
            add_directed_instr_stream_in_debug_program(opts[0], opts[1].atoi());
          end
        end else if ($value$plusargs({stream_name_opts,"%0s"}, stream_name) &&
                     $value$plusargs({stream_freq_opts,"%0d"}, stream_freq)) begin
          add_directed_instr_stream_in_debug_program(stream_name, stream_freq);
        end
      end

    endfunction

endclass : cv32e40p_debug_rom_gen

