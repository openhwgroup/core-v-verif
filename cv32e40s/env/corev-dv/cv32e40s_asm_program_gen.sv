/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
 * Copyright 2020 OpenHW Group
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//-----------------------------------------------------------------------------------------
// CV32E40S CORE-V assembly program generator - extension of the RISC-V assembly program generator.
//
// Overrides gen_program_header() and gen_test_done() and other riscv-dv functions.
//-----------------------------------------------------------------------------------------

class cv32e40s_asm_program_gen extends corev_asm_program_gen;

  `uvm_object_utils(cv32e40s_asm_program_gen)


  function new (string name = "");
    super.new(name);
  endfunction


  virtual function void gen_program_header();
    string instr[];
    cv32e40s_instr_gen_config corev_cfg;
    `DV_CHECK_FATAL($cast(corev_cfg, cfg), "Could not cast cfg into corev_cfg")

    super.gen_program_header();

    case ({corev_cfg.enable_dummy, corev_cfg.enable_hint})
      2'b00: begin
        // Not enabled
      end
      2'b01: begin
        instr = {
          $sformatf("lui x%0d, 0x0", cfg.gpr[0]),
          $sformatf("ori x%0d, x%0d, 0x4", cfg.gpr[0], cfg.gpr[0]),
          $sformatf("csrrs x0, 0xbf0, x%0d", cfg.gpr[0])
        };
        gen_section(get_label("enable_hint_instr", hart), instr);
      end
      2'b10: begin
        instr = {
          $sformatf("lui x%0d, 0xf0", cfg.gpr[0]),
          $sformatf("ori x%0d, x%0d, 0x2", cfg.gpr[0], cfg.gpr[0]),
          $sformatf("csrrs x0, 0xbf0, x%0d", cfg.gpr[0])
        };
        gen_section(get_label("enable_dummy_instr", hart), instr);
      end
      2'b11: begin
        instr = {
          $sformatf("lui x%0d, 0xf0", cfg.gpr[0]),
          $sformatf("ori x%0d, x%0d, 0x6", cfg.gpr[0], cfg.gpr[0]),
          $sformatf("csrrs x0, 0xbf0, x%0d", cfg.gpr[0])
        };
        gen_section(get_label("enable_dummy_hint_instr", hart), instr);
      end
    endcase

    case ({corev_cfg.disable_pc_hardening, corev_cfg.disable_data_independent_timing})
      2'b00: begin
        // Nothing disabled
      end
      2'b01: begin
        instr = {
          $sformatf("lui x%0d, 0", cfg.gpr[0]),
          $sformatf("ori x%0d, x%0d, 0x1", cfg.gpr[0], cfg.gpr[0]),
          $sformatf("csrrc x0, 0xbf0, x%0d", cfg.gpr[0])
        };
        gen_section(get_label("disable_pc_hardening_data_ind_timing", hart), instr);
      end
      2'b10: begin
        instr = {
          $sformatf("lui x%0d, 0", cfg.gpr[0]),
          $sformatf("ori x%0d, x%0d, 0x8", cfg.gpr[0], cfg.gpr[0]),
          $sformatf("csrrc x0, 0xbf0, x%0d", cfg.gpr[0])
        };
        gen_section(get_label("disable_pc_hardening_data_ind_timing", hart), instr);
      end
      2'b11: begin
        instr = {
          $sformatf("lui x%0d, 0", cfg.gpr[0]),
          $sformatf("ori x%0d, x%0d, 0x9", cfg.gpr[0], cfg.gpr[0]),
          $sformatf("csrrc x0, 0xbf0, x%0d", cfg.gpr[0])
        };
        gen_section(get_label("disable_pc_hardening_data_ind_timing", hart), instr);
      end
    endcase

  endfunction : gen_program_header


  virtual function void trap_vector_init(int hart);
    string instr[];
    privileged_reg_t trap_vec_reg;
    privileged_reg_t tvt_vec_reg;
    string tvec_name;
    foreach(riscv_instr_pkg::supported_privileged_mode[i]) begin
      case(riscv_instr_pkg::supported_privileged_mode[i])
        MACHINE_MODE:    begin
          trap_vec_reg = MTVEC;
          tvt_vec_reg  = MTVT;
        end
        SUPERVISOR_MODE: trap_vec_reg = STVEC;
        USER_MODE:       trap_vec_reg = UTVEC;
        default: `uvm_info(`gfn, $sformatf("Unsupported privileged_mode %0s",
                           riscv_instr_pkg::supported_privileged_mode[i]), UVM_LOW)
      endcase
      // Skip utvec init if trap delegation to u_mode is not supported
      if ((riscv_instr_pkg::supported_privileged_mode[i] == USER_MODE) &&
          !riscv_instr_pkg::support_umode_trap) continue;
      if (riscv_instr_pkg::supported_privileged_mode[i] < cfg.init_privileged_mode) continue;
      tvec_name = trap_vec_reg.name();
      // for the vectored mode, mtvec_handler is not the actual symbol for the trap handler
      // in our implementation. This ensures that we load the intended mtvec addreses instead
      // of where the mtvec address 0 jumps to.
      if (tvec_name.tolower == "mtvec") begin
        instr = {instr, $sformatf("la x%0d, __vector_start", cfg.gpr[0])};
      end else begin
        instr = {instr, $sformatf("la x%0d, %0s%0s_handler",
                                  cfg.gpr[0], hart_prefix(hart), tvec_name.tolower())};
      end
      if (SATP_MODE != BARE && riscv_instr_pkg::supported_privileged_mode[i] != MACHINE_MODE) begin
        // For supervisor and user mode, use virtual address instead of physical address.
        // Virtual address starts from address 0x0, here only the lower 20 bits are kept
        // as virtual address offset.
        instr = {instr,
                 $sformatf("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 20),
                 $sformatf("srli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 20)};
      end
      instr = {instr, $sformatf("ori x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], cfg.mtvec_mode)};
      instr = {instr, $sformatf("csrw 0x%0x, x%0d # %0s",
                                 trap_vec_reg, cfg.gpr[0], trap_vec_reg.name())};

      if (cfg.mtvec_mode == riscv_instr_pkg::CLIC) begin
        instr = {instr,
                 $sformatf(".global __mtvt_table"),
                 $sformatf("la x%0d, __mtvt_table", cfg.gpr[0]),
                 $sformatf("csrw 0x%0x, x%0d # %0s", tvt_vec_reg, cfg.gpr[0], tvt_vec_reg.name())
        };

      end
    end
    gen_section(get_label("trap_vec_init", hart), instr);
  endfunction : trap_vector_init


  virtual function void gen_illegal_instr_handler(int hart);
    string instr[$];
    string load_instr = (XLEN == 32) ? "lw" : "ld";
    gen_signature_handshake(instr, CORE_STATUS, ILLEGAL_INSTR_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    instr = {instr,
            // Get the stack pointer from the scratch register
            $sformatf("csrrw x%0d, 0x%0x, x%0d", cfg.sp, MSCRATCH, cfg.sp),
            $sformatf("%0s x%0d, %0d(x%0d)", load_instr, cfg.gpr[1], 0 * (XLEN/8), cfg.sp),
            // if zero, jump to end
            $sformatf("beq x%0d, x%0d, non_pma_handler_illegal_instr", cfg.gpr[1], 0),
            // else get the other (potential) pc_value from stack
            $sformatf("%0s x%0d, %0d(x%0d)", load_instr, cfg.gpr[0], 1 * (XLEN/8), cfg.sp),
            // check if these are equal (nonzero implied from check above)
            $sformatf("bne x%0d, x%0d, non_pma_handler_illegal_instr", cfg.gpr[1], cfg.gpr[0]),
            $sformatf("csrw 0x%0x, x%0d", MEPC, cfg.gpr[1]),
            $sformatf("la x%0d, pop_gpr_illegal_instr_handler", cfg.gpr[0]),
            $sformatf("jalr x%0d, x%0d", 0, cfg.gpr[0]),

            // original handler code start
            $sformatf("non_pma_handler_illegal_instr: csrr  x%0d, 0x%0x", cfg.gpr[0], MEPC),

            $sformatf("lw  x%0d, 0(x%0d)", cfg.gpr[1], cfg.gpr[0]),
            $sformatf("andi x%0d, x%0d, 0x3", cfg.gpr[1], cfg.gpr[1]),
            $sformatf("addi x%0d, zero, 0x3", cfg.gpr[2]),
            $sformatf("bne x%1d, x%0d, 1f", cfg.gpr[1], cfg.gpr[2]),
            $sformatf("addi  x%0d, x%0d, 2", cfg.gpr[0], cfg.gpr[0]),
            $sformatf("1: addi  x%0d, x%0d, 2", cfg.gpr[0], cfg.gpr[0]),

            $sformatf("csrw  0x%0x, x%0d", MEPC, cfg.gpr[0]),
            // original handler code end

            $sformatf("pop_gpr_illegal_instr_handler:"),
            // Swap back stack pointer to restore condition prior to handler
            $sformatf("csrrw x%0d, 0x%0x, x%0d", cfg.sp, MSCRATCH, cfg.sp)
    };

    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr.push_back("mret");
    gen_section(get_label("illegal_instr_handler", hart), instr);
  endfunction


  virtual function void gen_instr_fault_handler(int hart);
    string instr[$];
    string load_instr = (XLEN == 32) ? "lw" : "ld";
    gen_signature_handshake(instr, CORE_STATUS, INSTR_FAULT_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    if (cfg.pmp_cfg.enable_pmp_exception_handler) begin
      cfg.pmp_cfg.gen_pmp_exception_routine({cfg.gpr, cfg.scratch_reg, cfg.pmp_reg},
                                            INSTRUCTION_ACCESS_FAULT,
                                            instr);
    end
    instr = {instr,
            // Get the stack pointer from the scratch register
            $sformatf("csrrw x%0d, 0x%0x, x%0d", cfg.sp, MSCRATCH, cfg.sp),
            $sformatf("%0s x%0d, %0d(x%0d)", load_instr, cfg.gpr[1], 0 * (XLEN/8), cfg.sp),
            // if zero, jump to end
            $sformatf("beq x%0d, x%0d, non_pma_handler_instr_fault", cfg.gpr[1], 0),
            // else get the other (potential) pc_value from stack
            $sformatf("%0s x%0d, %0d(x%0d)", load_instr, cfg.gpr[0], 1 * (XLEN/8), cfg.sp),
            // check if these are equal (nonzero implied from check above)
            $sformatf("bne x%0d, x%0d, non_pma_handler_instr_fault", cfg.gpr[1], cfg.gpr[0]),
            $sformatf("csrw 0x%0x, x%0d", MEPC, cfg.gpr[1]),
            $sformatf("la x%0d, pop_gpr_instr_fault_handler", cfg.gpr[0]),
            $sformatf("jalr x%0d, x%0d", 0, cfg.gpr[0]),

            // Do not increment MEPC in case of an instruction bus fault, retry
            // the instruction fetch, as errors are random
            $sformatf("non_pma_handler_instr_fault:"),

            $sformatf("pop_gpr_instr_fault_handler:"),
            // Swap back stack pointer to restore condition prior to handler
            $sformatf("csrrw x%0d, 0x%0x, x%0d", cfg.sp, MSCRATCH, cfg.sp)
    };
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr.push_back("mret");
    gen_section(get_label("instr_fault_handler", hart), instr);
  endfunction


  // TODO: handshake correct csr based on delegation
  virtual function void gen_load_fault_handler(int hart);
    string instr[$];
    gen_signature_handshake(instr, CORE_STATUS, LOAD_FAULT_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    if (cfg.pmp_cfg.enable_pmp_exception_handler) begin
      cfg.pmp_cfg.gen_pmp_exception_routine({cfg.gpr, cfg.scratch_reg, cfg.pmp_reg},
                                            LOAD_ACCESS_FAULT,
                                            instr);
    end
    // Increase mepc by 4
    instr = { instr,
              $sformatf("csrrw x%0d, 0x%0x, x%0d", cfg.gpr[0], MEPC, cfg.gpr[0]),
              $sformatf("addi x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], (XLEN/8)),
              $sformatf("csrrw x%0d, 0x%0x, x%0d", cfg.gpr[0], MEPC, cfg.gpr[0])
    };
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr.push_back("mret");
    gen_section(get_label("load_fault_handler", hart), instr);
  endfunction


  // TODO: handshake correct csr based on delegation
  virtual function void gen_store_fault_handler(int hart);
    string instr[$];
    gen_signature_handshake(instr, CORE_STATUS, STORE_FAULT_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    if (cfg.pmp_cfg.enable_pmp_exception_handler) begin
      cfg.pmp_cfg.gen_pmp_exception_routine({cfg.gpr, cfg.scratch_reg, cfg.pmp_reg},
                                            STORE_AMO_ACCESS_FAULT,
                                            instr);
    end
    instr = { instr,
              $sformatf("csrrw x%0d, 0x%0x, x%0d", cfg.gpr[0], MEPC, cfg.gpr[0]),
              $sformatf("addi x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], (XLEN/8)),
              $sformatf("csrrw x%0d, 0x%0x, x%0d", cfg.gpr[0], MEPC, cfg.gpr[0])
    };
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr.push_back("mret");
    gen_section(get_label("store_fault_handler", hart), instr);
  endfunction


  virtual function void gen_interrupt_vector_table(int              hart,
                                                   string           mode,
                                                   privileged_reg_t status,
                                                   privileged_reg_t cause,
                                                   privileged_reg_t ie,
                                                   privileged_reg_t ip,
                                                   privileged_reg_t scratch,
                                                   ref string       instr[$]);
    // In vector mode, the BASE address is shared between interrupt 0 and exception handling.
    // When vectored interrupts are enabled, interrupt cause 0, which corresponds to user-mode
    // software interrupts, are vectored to the same location as synchronous exceptions. This
    // ambiguity does not arise in practice, since user-mode software interrupts are either
    // disabled or delegated
    cv32e40s_instr_gen_config corev_cfg;
    `DV_CHECK_FATAL($cast(corev_cfg, cfg), "Could not cast cfg into corev_cfg")

    instr = {instr, ".option push",
                    ".option norvc",
                    $sformatf("j %0s%0smode_exception_handler", hart_prefix(hart), mode)};
    // Redirect the interrupt to the corresponding interrupt handler
    for (int i = 1; i < max_interrupt_vector_num; i++) begin
      if (i == 15) begin
        instr.push_back($sformatf("jal x0, nmi_handler"));
      end else begin
        instr.push_back($sformatf("jal x0,  %0s%0smode_intr_vector_%0d", hart_prefix(hart), mode, i));
      end
    end
    if (!cfg.disable_compressed_instr) begin
      instr = {instr, ".option pop"};
    end else begin
      instr = {instr, ".option pop", ".option norvc"};
    end
    for (int i = 1; i < max_interrupt_vector_num; i++) begin
      string intr_handler[$];

      if (corev_cfg.use_fast_intr_handler[i]) begin
        // Emit fast interrupt handler since cv32e40s has hardware interrupt ack
        // If WFIs allow, randomly insert wfi as well
        if (!cfg.no_wfi) begin
            randcase
                2:  intr_handler.push_back("wfi");
                4: begin /* insert nothing */ end
            endcase
        end
        intr_handler.push_back("mret");
      end
      else begin
        // Standard full-stack-save interrupt handler
        push_gpr_to_kernel_stack(status, scratch, cfg.mstatus_mprv, cfg.sp, cfg.tp, intr_handler);
        gen_signature_handshake(.instr(intr_handler), .signature_type(CORE_STATUS),
                                .core_status(HANDLING_IRQ));
        intr_handler = {intr_handler,
                        $sformatf("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], cause, cause.name()),
                        // Terminate the test if xCause[31] != 0 (indicating exception)
                        $sformatf("srli x%0d, x%0d, 0x%0x", cfg.gpr[0], cfg.gpr[0], XLEN-1),
                        $sformatf("beqz x%0d, 1f", cfg.gpr[0])};
        gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(status));
        gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(cause));
        gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(ie));
        gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(ip));
        // Jump to commmon interrupt handling routine
        intr_handler = {intr_handler,
                        $sformatf("j %0s%0smode_intr_handler", hart_prefix(hart), mode),
                        $sformatf("1: la x%0d, test_done", cfg.scratch_reg),
                        $sformatf("jalr x%0d, 0", cfg.scratch_reg)};
      end

      gen_section(get_label($sformatf("%0smode_intr_vector_%0d", mode, i), hart), intr_handler);
    end
  endfunction : gen_interrupt_vector_table


  // Setup EPC before entering target privileged mode
  virtual function void setup_epc(int hart);
    string instr[$];
    string mode_name;
    instr = {$sformatf("la x%0d, %0sinit", cfg.gpr[0], hart_prefix(hart))};
    if(cfg.virtual_addr_translation_on) begin
      // For supervisor and user mode, use virtual address instead of physical address.
      // Virtual address starts from address 0x0, here only the lower 12 bits are kept
      // as virtual address offset.
      instr = {instr,
               $sformatf("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 12),
               $sformatf("srli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 12)};
    end
    mode_name = cfg.init_privileged_mode.name();
    instr.push_back($sformatf("csrw mepc, x%0d", cfg.gpr[0]));
    gen_section(get_label("mepc_setup", hart), instr);
  endfunction


  // Interrupt handler routine
  // Override from risc-dv:
  // 1. Remove MIP read, since interrupts are auto-cleared, mip will not track through the ISS
  //    to GPR properly with autoclear
  virtual function void gen_interrupt_handler_section(privileged_mode_t mode, int hart);
    string mode_prefix;
    string ls_unit;
    privileged_reg_t cause, status, ip, ie, scratch;
    string interrupt_handler_instr[$];

    ls_unit = (XLEN == 32) ? "w" : "d";
    if (mode < cfg.init_privileged_mode) return;
    if (mode == USER_MODE && !riscv_instr_pkg::support_umode_trap) return;
    case(mode)
      MACHINE_MODE: begin
        mode_prefix = "m";
        status = MSTATUS;
        cause = MCAUSE;
        ip = MIP;
        ie = MIE;
        scratch = MSCRATCH;
      end
      SUPERVISOR_MODE: begin
        mode_prefix = "s";
        status = SSTATUS;
        cause = SCAUSE;
        ip = SIP;
        ie = SIE;
        scratch = SSCRATCH;
      end
      USER_MODE: begin
        mode_prefix = "u";
        status = USTATUS;
        cause = UCAUSE;
        ip = UIP;
        ie = UIE;
        scratch = USCRATCH;
      end
      default: `uvm_fatal(get_full_name(), $sformatf("Unsupported mode: %0s", mode.name()))
    endcase

    // If nested interrupts are enabled, set xSTATUS.xIE in the interrupt handler
    // to re-enable interrupt handling capabilities
    if (cfg.enable_nested_interrupt) begin
      string store_instr = (XLEN == 32) ? "sw" : "sd";

      // kernel stack point is already in sp, mscratch already has stored stack pointer
      interrupt_handler_instr.push_back($sformatf("1: addi x%0d, x%0d, -%0d", cfg.sp, cfg.sp, 4 * (XLEN/8)));

      // Push MIE, MEPC and MSTATUS to stack
      interrupt_handler_instr.push_back($sformatf("csrr x%0d, mie", cfg.gpr[0]));
      interrupt_handler_instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, cfg.gpr[0], 1 * (XLEN/8), cfg.sp));
      interrupt_handler_instr.push_back($sformatf("csrr x%0d, mepc", cfg.gpr[0]));
      interrupt_handler_instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, cfg.gpr[0], 2 * (XLEN/8), cfg.sp));
      interrupt_handler_instr.push_back($sformatf("csrr x%0d, mstatus", cfg.gpr[0]));
      interrupt_handler_instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, cfg.gpr[0], 3 * (XLEN/8), cfg.sp));
      interrupt_handler_instr.push_back($sformatf("csrr x%0d, mscratch", cfg.gpr[0]));
      interrupt_handler_instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, cfg.gpr[0], 4 * (XLEN/8), cfg.sp));

      // Move SP to TP and restore TP
      interrupt_handler_instr.push_back($sformatf("add x%0d, x%0d, zero", cfg.tp, cfg.sp));
      interrupt_handler_instr.push_back($sformatf("csrrw x%0d, mscratch, x%0d", cfg.sp, cfg.sp));

      // Re-enable interrupts
      case (status)
        MSTATUS: begin
          interrupt_handler_instr.push_back($sformatf("csrsi 0x%0x, 0x%0x", status, 8));
        end
        SSTATUS: begin
          interrupt_handler_instr.push_back($sformatf("csrsi 0x%0x, 0x%0x", status, 2));
        end
        USTATUS: begin
          interrupt_handler_instr.push_back($sformatf("csrsi 0x%0x, 0x%0x", status, 1));
        end
        default: `uvm_fatal(`gfn, $sformatf("Unsupported status %0s", status))
      endcase
    end

    // Read back interrupt related privileged CSR
    // The value of these CSR are checked by comparing with spike simulation result.
    if (cfg.mtvec_mode == DIRECT) begin
      interrupt_handler_instr = {
        interrupt_handler_instr,
        $sformatf("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], cause, cause.name()),
        $sformatf("slli x%0d, x%0d, 1 # shift out interrupt bit", cfg.gpr[0], cfg.gpr[0]),
        $sformatf("srli x%0d, x%0d, 3 # shift back down 3 bits to disregard lower two bits of the nmi cause", cfg.gpr[0], cfg.gpr[0]),
        $sformatf("addi x%0d, zero, 0x100 # Add reference (all valid nmis, 1024,1025,1026,1027 >> 2)", cfg.gpr[1]),
        $sformatf("beq x%0d, x%1d, nmi_handler", cfg.gpr[0], cfg.gpr[1])
      };
    end

    interrupt_handler_instr = {
           interrupt_handler_instr,
           $sformatf("csrr  x%0d, 0x%0x # %0s;", cfg.gpr[0], status, status.name()),
           $sformatf("csrr  x%0d, 0x%0x # %0s;", cfg.gpr[0], ie, ie.name())
    };
    gen_plic_section(interrupt_handler_instr);

    if (cfg.enable_nested_interrupt) begin
      string load_instr = (XLEN == 32) ? "lw" : "ld";

      // If in nested interrupts, the restoration of all GPRs and interrupt registers from stack
      // are considered a critical section
      // Re-disable interrupts
      case (status)
        MSTATUS: begin
          interrupt_handler_instr.push_back($sformatf("csrci 0x%0x, 0x%0x", status, 8));
        end
        SSTATUS: begin
          interrupt_handler_instr.push_back($sformatf("csrci 0x%0x, 0x%0x", status, 2));
        end
        USTATUS: begin
          interrupt_handler_instr.push_back($sformatf("csrci 0x%0x, 0x%0x", status, 1));
        end
        default: `uvm_fatal(`gfn, $sformatf("Unsupported status %0s", status))
      endcase

      // Save SP to scratch and move TP to SP
      interrupt_handler_instr.push_back($sformatf("csrrw x%0d, mscratch, x%0d", cfg.sp, cfg.sp));
      interrupt_handler_instr.push_back($sformatf("add x%0d, x%0d, zero", cfg.sp, cfg.tp));

      interrupt_handler_instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, cfg.gpr[0], 1 * (XLEN/8), cfg.sp));
      interrupt_handler_instr.push_back($sformatf("csrw mie, x%0d", cfg.gpr[0]));
      interrupt_handler_instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, cfg.gpr[0], 2 * (XLEN/8), cfg.sp));
      interrupt_handler_instr.push_back($sformatf("csrw mepc, x%0d", cfg.gpr[0]));
      interrupt_handler_instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, cfg.gpr[0], 3 * (XLEN/8), cfg.sp));
      interrupt_handler_instr.push_back($sformatf("csrw mstatus, x%0d", cfg.gpr[0]));
      interrupt_handler_instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, cfg.gpr[0], 4 * (XLEN/8), cfg.sp));
      interrupt_handler_instr.push_back($sformatf("csrw mscratch, x%0d", cfg.gpr[0]));

      interrupt_handler_instr.push_back($sformatf("addi x%0d, x%0d, %0d", cfg.sp, cfg.sp, 4 * (XLEN/8)));
    end

    // Restore user mode GPR value from kernel stack before return
    pop_gpr_from_kernel_stack(status, scratch, cfg.mstatus_mprv,
                              cfg.sp, cfg.tp, interrupt_handler_instr);
                                      // Emit fast interrupt handler since cv32e40s has hardware interrupt ack

    interrupt_handler_instr = {interrupt_handler_instr,
                               $sformatf("%0sret;", mode_prefix)
    };
    if (SATP_MODE != BARE) begin
      // The interrupt handler will use one 4KB page
      instr_stream.push_back(".align 12");
    end else begin
      instr_stream.push_back(".align 2");
    end
    gen_section(get_label($sformatf("%0smode_intr_handler", mode_prefix), hart),
                interrupt_handler_instr);

    gen_nmi_handler_section(hart);

  endfunction : gen_interrupt_handler_section


  // Override gen_stack_section to add debugger stack generation section
  // Implmeneted as a post-step to super.gen_stack_section()
  virtual function void gen_stack_section(int hart);
    super.gen_stack_section(hart);

    if (SATP_MODE != BARE) begin
      instr_stream.push_back(".align 12");
    end else begin
      instr_stream.push_back(".align 2");
    end
    instr_stream.push_back(get_label("debugger_stack_start:", hart));
    instr_stream.push_back($sformatf(".rept %0d", cfg.stack_len - 1));
    instr_stream.push_back($sformatf(".%0dbyte 0x0", XLEN/8));
    instr_stream.push_back(".endr");
    instr_stream.push_back(get_label("debugger_stack_end:", hart));
    instr_stream.push_back($sformatf(".%0dbyte 0x0", XLEN/8));

  endfunction : gen_stack_section


  // Override of init_gpr to remove cfg.dp from initiailization if a debug section is generated
  virtual function void init_gpr();
    string str;
    bit [DATA_WIDTH-1:0] reg_val;
    cv32e40s_instr_gen_config cfg_corev;

    `DV_CHECK($cast(cfg_corev, cfg))
    // Init general purpose registers with random values
    for(int i = 0; i < NUM_GPR; i++) begin
      if (i inside {cfg.sp, cfg.tp}) continue;
      if (cfg.gen_debug_section && (i inside {cfg_corev.dp})) continue;

      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(reg_val,
        reg_val dist {
          'h0                         :/ 1,
          'h8000_0000                 :/ 1,
          ['h1         : 'hF]         :/ 1,
          ['h10        : 'hEFFF_FFFF] :/ 1,
          ['hF000_0000 : 'hFFFF_FFFF] :/ 1
        };)
      str = $sformatf("%0sli x%0d, 0x%0x", indent, i, reg_val);
      instr_stream.push_back(str);
    end
  endfunction


  // generate NMI handler.
  // will be placed at a fixed address in memory, set in linker file
  virtual function void gen_nmi_handler_section(int hart);
    string nmi_handler_instr[$];

    // Insert section info so linker can place
    // debug code at the correct adress
    // We do not want a specific region for the handler code
    // in case of direct mode interrupts, as its location is
    // dynamically allocated
    if (cfg.mtvec_mode == DIRECT) begin
      instr_stream.push_back(".section .nmi, \"ax\"");
    end

    // read relevant csr's
    nmi_handler_instr.push_back($sformatf("csrr x%0d, mepc", cfg.gpr[0]));
    nmi_handler_instr.push_back($sformatf("csrr x%0d, mcause", cfg.gpr[0]));
    nmi_handler_instr.push_back($sformatf("csrr x%0d, mtval", cfg.gpr[0]));
    nmi_handler_instr.push_back($sformatf("csrr x%0d, mie", cfg.gpr[0]));

    nmi_handler_instr.push_back($sformatf("la x%0d, test_done", cfg.scratch_reg));
    nmi_handler_instr.push_back($sformatf("jr x%0d", cfg.scratch_reg));

    gen_section(get_label($sformatf("nmi_handler"), hart),
                nmi_handler_instr);
  endfunction : gen_nmi_handler_section


  virtual function void gen_section(string label, string instr[$]);
    string str;

    if(label == "mtvec_handler" && cfg.mtvec_mode == VECTORED) begin
      str = ".section .mtvec_handler, \"ax\"";
      instr_stream.push_back(str);
      str = format_string($sformatf("%0s:", label), LABEL_STR_LEN);
      instr_stream.push_back(str);
    end else if(label != "") begin
      str = format_string($sformatf("%0s:", label), LABEL_STR_LEN);
      instr_stream.push_back(str);
    end

    foreach(instr[i]) begin
      str = {indent, instr[i]};
      instr_stream.push_back(str);
      if (i == instr.size() - 1) begin
        str = ".section .text";
        instr_stream.push_back("");
        instr_stream.push_back(str);
      end
    end

    instr_stream.push_back("");
  endfunction : gen_section


  virtual function void gen_init_section(int hart);
    string  instrs[];
    string  label;

    super.gen_init_section(hart);

    // After the "init" section, bus errors can safely occur without havoc
    label = get_label("obi_err_goahead", hart);
    instrs = {
      $sformatf("li x%0d, 0x%08x", cfg.gpr[0], CV_VP_OBI_ERR_AWAIT_GOAHEAD_BASE),
      $sformatf("sw x0, 0(x%0d)", cfg.gpr[0])
    };
    gen_section(label, instrs);
  endfunction


endclass : cv32e40s_asm_program_gen
