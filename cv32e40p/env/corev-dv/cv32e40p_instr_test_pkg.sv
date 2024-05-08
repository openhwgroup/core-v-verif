/*
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

`include "cv32e40p_instr_pkg.sv"

package cv32e40p_instr_test_pkg;

  parameter int HWLOOP_LABEL_STR_LEN = 32;

  import uvm_pkg::*;
  import riscv_instr_pkg::*;
  import cv32e40p_instr_pkg::*;
  import riscv_instr_test_pkg::*;
  import riscv_signature_pkg::*;
  import corev_instr_test_pkg::*;


  // MACRO for Common Exception Handling/Debug_Rom code for xEPC CSR management
  // Including hwloop CSR management. (Used only with XPULP ISA support)
  //
  // Common handler code to ensure all handlers use same code.
  // Description:
  // Check for expection (ecall/ebreak/illegal) on the last hwloop body instr
  // If true, then
  // (a) Set xEPC to first instr of hwloop body if LPCOUNTx >= 2
  // (b) Decrement the LPCOUNTx if LPCOUNTx >= 1
  // Else
  // By Default for all other cases increment xEPC by 4
  `define COMMON_EXCEPTION_XEPC_HANDLING_CODE_WITH_HWLOOP_CHECK(SCRATCH_REG0,SCRATCH_REG1,XEPC) \
      /* Check LPCOUNT1 >= 1 */ \
      $sformatf("csrr x%0d, 0x%0x", ``SCRATCH_REG0, LPCOUNT1), \
      $sformatf("li x%0d, 1", ``SCRATCH_REG1), \
      $sformatf("bge x%0d, x%0d, 1f", ``SCRATCH_REG0, ``SCRATCH_REG1), \
      /* Check LPCOUNT0 >= 1 */ \
      $sformatf("2: csrr x%0d, 0x%0x", ``SCRATCH_REG0, LPCOUNT0), \
      $sformatf("li x%0d, 1", ``SCRATCH_REG1), \
      $sformatf("bge x%0d, x%0d, 3f", ``SCRATCH_REG0, ``SCRATCH_REG1), \
      /* Since both LPCOUNT0 & LPCOUNT1 equals 0 */ \
      /* Nothing needs to be done for HWLOOPs and its CSRs */ \
      $sformatf("beqz x0, 4f"), \
      /* HWLOOP1 Handling */ \
      /* Check for ILLEGAL being the LAST HWLOOP Body instr */ \
      $sformatf("1: csrr  x%0d, 0x%0x", ``SCRATCH_REG0, ``XEPC), \
      $sformatf("csrr  x%0d, 0x%0x", ``SCRATCH_REG1, LPEND1), \
      $sformatf("addi x%0d, x%0d, -4", ``SCRATCH_REG1, ``SCRATCH_REG1), \
      $sformatf("bne x%0d, x%0d, 2b", ``SCRATCH_REG0, ``SCRATCH_REG1), \
      /* Else, If equal this means the illegal instr was the last */ \
      /* hwloop body instr, thus we handle the HWLOOP manually here */ \
      /* First decrement lpcount CSR manually as CSR not updated in HW */ \
      $sformatf("csrr x%0d, 0x%0x", ``SCRATCH_REG1, LPCOUNT1), \
      $sformatf("addi x%0d, x%0d, -1", ``SCRATCH_REG1, ``SCRATCH_REG1), \
      $sformatf("cv.count 1, x%0d", ``SCRATCH_REG1), \
      /* Check if the current LPCOUNT1 value == 0, if so, then xEPC=xEPC+4 */ \
      $sformatf("csrr x%0d, 0x%0x", ``SCRATCH_REG1, LPCOUNT1), \
      $sformatf("beqz x%0d, 4f", ``SCRATCH_REG1), \
      /* Else LPCOUNT1 still >=1 and thus next, */ \
      /* Set the next xEPC to LPSTART1 for next HWLOOP iteration */ \
      $sformatf("csrr  x%0d, 0x%0x", ``SCRATCH_REG0, LPSTART1), \
      $sformatf("beqz x0, 5f"), \
      /* HWLOOP0 Handling */ \
      /* Check for ILLEGAL being the LAST HWLOOP Body instr */ \
      $sformatf("3: csrr  x%0d, 0x%0x", ``SCRATCH_REG0, ``XEPC), \
      $sformatf("csrr  x%0d, 0x%0x", ``SCRATCH_REG1, LPEND0), \
      $sformatf("addi x%0d, x%0d, -4", ``SCRATCH_REG1, ``SCRATCH_REG1), \
      $sformatf("bne x%0d, x%0d, 4f", ``SCRATCH_REG0, ``SCRATCH_REG1), \
      /* Else, If equal this means the illegal instr was the last */ \
      /* hwloop body instr, thus we handle the HWLOOP manually here */ \
      /* First decrement lpcount CSR manually as CSR not updated in HW */ \
      $sformatf("csrr x%0d, 0x%0x", ``SCRATCH_REG1, LPCOUNT0), \
      $sformatf("addi x%0d, x%0d, -1", ``SCRATCH_REG1, ``SCRATCH_REG1), \
      $sformatf("cv.count 0, x%0d", ``SCRATCH_REG1), \
      /* Check if the current LPCOUNT0 value == 0, if so, then xEPC=xEPC+4 */ \
      $sformatf("csrr x%0d, 0x%0x", ``SCRATCH_REG1, LPCOUNT0), \
      $sformatf("beqz x%0d, 4f", ``SCRATCH_REG1), \
      /* Else LPCOUNT0 still >=1 and thus next, */ \
      /* Set the next xEPC to LPSTART0 for next HWLOOP iteration */ \
      $sformatf("csrr  x%0d, 0x%0x", ``SCRATCH_REG0, LPSTART0), \
      $sformatf("beqz x0, 5f"), \
      /* Default increment for xEPC by 4 */ \
      $sformatf("4: csrr  x%0d, 0x%0x", ``SCRATCH_REG0, ``XEPC), \
      $sformatf("addi  x%0d, x%0d, 4", ``SCRATCH_REG0, ``SCRATCH_REG0), \
      /* Write xEPC */ \
      $sformatf("5: csrw  0x%0x, x%0d", ``XEPC, ``SCRATCH_REG0)


  `include "cv32e40p_instr_gen_config.sv"
  // Instruction streams specific to CV32E40P
  // `include "instr_lib/cv32e40p_load_store_instr_lib.sv"
  `include "instr_lib/cv32e40p_base_instr_lib.sv"
  `include "instr_lib/cv32e40p_pulp_instr_lib.sv"
  `include "instr_lib/cv32e40p_pulp_hwloop_instr_lib.sv"
  `include "instr_lib/cv32e40p_float_instr_lib.sv"
  `include "instr_lib/cv32e40p_instr_for_func_cvg_lib.sv" // directed streams to improve functional coverage holes in v2

  // RISCV-DV class override definitions
  `include "cv32e40p_rand_instr_stream.sv"
  `include "cv32e40p_illegal_instr.sv"
  `include "cv32e40p_instr_sequence.sv"
  `include "cv32e40p_compressed_instr.sv"
  `include "cv32e40p_privil_reg.sv"
  `include "cv32e40p_debug_rom_gen.sv"
  `include "cv32e40p_asm_program_gen.sv"
  `include "cv32e40p_instr_base_test.sv"

  // Push general purpose register to the debugger stack
  function automatic void push_gpr_to_debugger_stack(cv32e40p_instr_gen_config cfg_corev,
                                                     ref string instr[$]);
    string        store_instr = (XLEN == 32) ? "sw" : "sd";
    bit           done_store_mscratch = 1'b0;
    int unsigned  total_gpr = 32;
    // Reserve space from debugger stack to save all 32 GPR except for x0 + MSCRATCH
    instr.push_back($sformatf("1: addi x%0d, x%0d, -%0d", cfg_corev.dp, cfg_corev.dp, 32 * (XLEN/8)));
    // Push all GPRs to debugger stack
    for(int i = 1; i < total_gpr; i++) begin
      if (i == cfg_corev.dp) continue;
      if (i == cfg_corev.sp) continue;
      if (i == cfg_corev.tp) continue;
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, i, (i-1) * (XLEN/8), cfg_corev.dp));
      if (!done_store_mscratch) begin
        // Read and Push MSCRATCH to debugger stack
        instr.push_back($sformatf("csrrw x%0d, 0x340, x%0d # MSCRATCH", i, i));
        instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, i, (total_gpr-1) * (XLEN/8), cfg_corev.dp));
        done_store_mscratch = 1;
      end
    end
  endfunction : push_gpr_to_debugger_stack

  // Push floating point registers to the debugger stack
  function automatic void push_fpr_to_debugger_stack(cv32e40p_instr_gen_config cfg_corev,
                                                     ref string instr[$],
                                                     privileged_reg_t status);
    string store_instr;

    randcase
      1: store_instr = (FLEN == 32) ? "fsw" : "fsd";
      (cfg_corev.dp == 2): store_instr = (FLEN == 32) ? "c.fswsp" : "fsd";
    endcase

    //Check if mstatus.FS != 3 ,i.e., Not "Dirty" state
    instr.push_back($sformatf("csrr x%0d, 0x%0x # %0s", cfg_corev.gpr[0], status, status.name()));
    instr.push_back($sformatf("srli x%0d, x%0d, 13", cfg_corev.gpr[0], cfg_corev.gpr[0]));
    instr.push_back($sformatf("andi x%0d, x%0d, 0x3", cfg_corev.gpr[0], cfg_corev.gpr[0]));  //Check MSTATUS.FS bit
    instr.push_back($sformatf("li x%0d, 0x%0x", cfg_corev.gpr[1], 3));
    instr.push_back($sformatf("bne x%0d, x%0d, 2f", cfg_corev.gpr[0], cfg_corev.gpr[1])); // MSTATUS.FS!=3 do not push

    // Reserve space from kernel stack to save all 32 FPR + FCSR + MSTATUS
    instr.push_back($sformatf("1: addi x%0d, x%0d, -%0d", cfg_corev.dp, cfg_corev.dp, 33 * (XLEN/8)));
    // Push all FPRs to kernel stack
    for(int i = 0; i < 32; i++) begin
      instr.push_back($sformatf("%0s  f%0d, %0d(x%0d)", store_instr, i, i * (FLEN/8), cfg_corev.dp));
    end

    store_instr = (XLEN == 32) ? "sw" : "sd";

    // Push FCSR to kernel stack
    instr.push_back($sformatf("fscsr x%0d, x0", cfg_corev.gpr[0])); // Read and Clear FCSR
    instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, cfg_corev.gpr[0], 32 * (XLEN/8),  cfg_corev.dp));

    // Reserve space from kernel stack to save MSTATUS.FS
    instr.push_back($sformatf("addi x%0d, x%0d, -%0d",  cfg_corev.dp,  cfg_corev.dp, 1 * (XLEN/8)));

    // Push MSTATUS.FS to kernel stack
    instr.push_back($sformatf("csrr x%0d, 0x%0x # %0s", cfg_corev.gpr[0], status, status.name()));
    instr.push_back($sformatf("srli x%0d, x%0d, 13", cfg_corev.gpr[0], cfg_corev.gpr[0]));
    instr.push_back($sformatf("andi x%0d, x%0d, 0x3", cfg_corev.gpr[0], cfg_corev.gpr[0]));
    instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, cfg_corev.gpr[0], 0,  cfg_corev.dp));

    //Set the MSTATUS.FS status to Clean
    instr.push_back($sformatf("li x%0d, 0x%0x", cfg_corev.gpr[0], 1));  //Set FS from 3->2 Clean, clear bit 13
    instr.push_back($sformatf("slli x%0d, x%0d, 13", cfg_corev.gpr[0], cfg_corev.gpr[0]));
    instr.push_back($sformatf("csrrc x0, 0x%0x, x%0d # %0s", status, cfg_corev.gpr[0], status.name()));

    instr.push_back($sformatf("j 3f"));

    instr.push_back($sformatf("2: nop")); //BNE 2f Target

    // Reserve space from kernel stack to save MSTATUS.FS
    instr.push_back($sformatf("addi x%0d, x%0d, -%0d",  cfg_corev.dp,  cfg_corev.dp, 1 * (XLEN/8)));

    // Push MSTATUS.FS to kernel stack
    instr.push_back($sformatf("csrr x%0d, 0x%0x # %0s", cfg_corev.gpr[0], status, status.name()));
    instr.push_back($sformatf("srli x%0d, x%0d, 13", cfg_corev.gpr[0], cfg_corev.gpr[0]));
    instr.push_back($sformatf("andi x%0d, x%0d, 0x3", cfg_corev.gpr[0], cfg_corev.gpr[0]));
    instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, cfg_corev.gpr[0], 0,  cfg_corev.dp));

    instr.push_back($sformatf("3: nop")); //Jump 3f Target

    //Check if mstatus.FS != 0 ,i.e., Not "All Off" state
    instr.push_back($sformatf("csrr x%0d, 0x%0x # %0s", cfg_corev.gpr[0], status, status.name()));
    instr.push_back($sformatf("srli x%0d, x%0d, 13", cfg_corev.gpr[0], cfg_corev.gpr[0]));
    instr.push_back($sformatf("andi x%0d, x%0d, 0x3", cfg_corev.gpr[0], cfg_corev.gpr[0]));  //Check MSTATUS.FS bit
    instr.push_back($sformatf("bnez x%0d, 4f", cfg_corev.gpr[0])); // check MSTATUS.FS!=0

    // if MSTATUS.FS==0 set MSTATUS.FS to Initial
    instr.push_back($sformatf("li x%0d, 0x%0x", cfg_corev.gpr[0], 1));  //Change FS from 0 to 1, i.e., Initial
    instr.push_back($sformatf("slli x%0d, x%0d, 13", cfg_corev.gpr[0], cfg_corev.gpr[0]));
    instr.push_back($sformatf("csrrs x0, 0x%0x, x%0d # %0s", status, cfg_corev.gpr[0], status.name()));

    instr.push_back($sformatf("4: nop")); //BNE 4f Target


  endfunction : push_fpr_to_debugger_stack

  // Pop general purpose register from debugger stack
  function automatic void pop_gpr_from_debugger_stack(cv32e40p_instr_gen_config cfg_corev,
                                                      ref string instr[$]);
    string        load_instr = (XLEN == 32) ? "lw" : "ld";
    bit           done_load_mscratch = 1'b0;
    int unsigned  total_gpr = 32;
    // Pop user mode GPRs from kernel stack
    for(int i = 1; i < total_gpr; i++) begin
      if (i == cfg_corev.dp) continue;
      if (i == cfg_corev.sp) continue;
      if (i == cfg_corev.tp) continue;
      if (!done_load_mscratch) begin
        // Pop and Write MSCRATCH from debugger stack
        instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, i, (total_gpr-1) * (XLEN/8), cfg_corev.dp));
        instr.push_back($sformatf("csrrw x%0d, 0x340, x%0d # MSCRATCH", i, i));
        done_load_mscratch = 1;
      end
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, i, (i-1) * (XLEN/8), cfg_corev.dp));
    end
    // Restore debugger stack pointer
    instr.push_back($sformatf("addi x%0d, x%0d, %0d", cfg_corev.dp, cfg_corev.dp, 31 * (XLEN/8)));
  endfunction : pop_gpr_from_debugger_stack

  // Pop floating point register from debugger stack
  function automatic void pop_fpr_from_debugger_stack(cv32e40p_instr_gen_config cfg_corev,
                                                      ref string instr[$],
                                                      privileged_reg_t status);
    string load_instr;

    load_instr = (XLEN == 32) ? "lw" : "ld";

    // Pop MSTATUS.FS from kernel stack
    instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, cfg_corev.gpr[0], 0, cfg_corev.dp));
    // Restore MSTATUS.FS
    instr.push_back($sformatf("li x%0d, 0x%0x", cfg_corev.gpr[1], 3));  //Clear FS
    instr.push_back($sformatf("slli x%0d, x%0d, 13", cfg_corev.gpr[1], cfg_corev.gpr[1]));
    instr.push_back($sformatf("csrrc x0, 0x%0x, x%0d # %0s", status, cfg_corev.gpr[1], status.name()));
    instr.push_back($sformatf("slli x%0d, x%0d, 13", cfg_corev.gpr[1], cfg_corev.gpr[0]));
    instr.push_back($sformatf("csrrs x0, 0x%0x, x%0d # %0s", status, cfg_corev.gpr[1], status.name()));

    // Restore kernel stack pointer
    instr.push_back($sformatf("addi x%0d, x%0d, %0d", cfg_corev.dp, cfg_corev.dp, 1 * (XLEN/8)));

    instr.push_back($sformatf("li x%0d, 0x%0x", cfg_corev.gpr[1], 3));
    instr.push_back($sformatf("bne x%0d, x%0d, 2f", cfg_corev.gpr[0], cfg_corev.gpr[1])); // MSTATUS.FS!=3 do not pop FPR

    randcase
      1: load_instr = (FLEN == 32) ? "flw" : "fld";
      (cfg_corev.dp == 2): load_instr = (FLEN == 32) ? "c.flwsp" : "fld";
    endcase

    // Pop FPRs from kernel stack
    for(int i = 0; i < 32; i++) begin
      instr.push_back($sformatf("%0s  f%0d, %0d(x%0d)", load_instr, i, i * (FLEN/8), cfg_corev.dp));
    end

    load_instr = (XLEN == 32) ? "lw" : "ld";

    // Pop FCSR from kernel stack
    instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, cfg_corev.gpr[1], 32 * (XLEN/8), cfg_corev.dp));
    instr.push_back($sformatf("fscsr x%0d", cfg_corev.gpr[1])); // Restore FCSR

    // Restore debugger stack pointer
    instr.push_back($sformatf("addi x%0d, x%0d, %0d", cfg_corev.dp, cfg_corev.dp, 33 * (XLEN/8)));

    instr.push_back($sformatf("2: nop")); //BNE 2f Target

  endfunction : pop_fpr_from_debugger_stack

  //Function: check_str_pattern_match
  //Description: Search for a string pattern withing a given string
  //Inputs:
  //    - check_str   - Main string to be searched for pattern within
  //    - pattern_str - Sub-String "pattern" to search within main string
  //Output :
  //    - Return 1 if pattern found, else return 0
  function automatic bit check_str_pattern_match(string check_str, string pattern_str);
    int     str_len;
    int     pattern_str_len;
    bit     match_val;

    match_val = 0;
    str_len = check_str.len();
    pattern_str_len = pattern_str.len();

    if(pattern_str_len < str_len) begin
      for(int j = 0;j < str_len-pattern_str_len+1; j++) begin
        if(check_str.substr(j,j+pattern_str_len -1) == pattern_str) begin
          match_val = 1;  //set indicates str pattern found
          break;
        end
      end
    end
    return match_val;

  endfunction

  // Push general purpose register to stack, this is needed before trap handling
  // Push fpr to stack if rv32f exists
  function automatic void push_regfile_to_kernel_stack(privileged_reg_t status,
                                                       privileged_reg_t scratch,
                                                       bit mprv,
                                                       riscv_reg_t sp,
                                                       riscv_reg_t tp,
                                                       ref string instr[$],
                                                       cv32e40p_instr_gen_config cfg_corev);
    string store_instr = (XLEN == 32) ? "sw" : "sd";
    if (scratch inside {implemented_csr}) begin
      // Use kernal stack for handling exceptions
      // Save the user mode stack pointer to the scratch register
      instr.push_back($sformatf("csrrw x%0d, 0x%0x, x%0d", sp, scratch, sp));
      // Move TP to SP
      instr.push_back($sformatf("add x%0d, x%0d, zero", sp, tp));
    end
    // If MPRV is set and MPP is S/U mode, it means the address translation and memory protection
    // for load/store instruction is the same as the mode indicated by MPP. In this case, we
    // need to use the virtual address to access the kernel stack.
    if((status == MSTATUS) && (SATP_MODE != BARE)) begin
      // We temporarily use tp to check mstatus to avoid changing other GPR. The value of sp has
      // been saved to xScratch and can be restored later.
      if(mprv) begin
        instr.push_back($sformatf("csrr x%0d, 0x%0x // MSTATUS", tp, status));
        instr.push_back($sformatf("srli x%0d, x%0d, 11", tp, tp));  // Move MPP to bit 0
        instr.push_back($sformatf("andi x%0d, x%0d, 0x3", tp, tp)); // keep the MPP bits
        // Check if MPP equals to M-mode('b11)
        instr.push_back($sformatf("xori x%0d, x%0d, 0x3", tp, tp));
        instr.push_back($sformatf("bnez x%0d, 1f", tp));      // Use physical address for kernel SP
        // Use virtual address for stack pointer
        instr.push_back($sformatf("slli x%0d, x%0d, %0d", sp, sp, XLEN - MAX_USED_VADDR_BITS));
        instr.push_back($sformatf("srli x%0d, x%0d, %0d", sp, sp, XLEN - MAX_USED_VADDR_BITS));
      end
    end
    // Reserve space from kernel stack to save all 32 GPR except for x0
    instr.push_back($sformatf("1: addi x%0d, x%0d, -%0d", sp, sp, 31 * (XLEN/8)));
    // Push all GPRs to kernel stack
    for(int i = 1; i < 32; i++) begin
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, i, (i-1) * (XLEN/8), sp));
    end

    if(cfg_corev.enable_floating_point && !cfg_corev.enable_fp_in_x_regs) begin
      randcase
        1: store_instr = (FLEN == 32) ? "fsw" : "fsd";
        (sp == 2): store_instr = (FLEN == 32) ? "c.fswsp" : "fsd";
      endcase

      //Check if mstatus.FS != 3 ,i.e., Not "Dirty" state
      instr.push_back($sformatf("csrr x%0d, 0x%0x # %0s", cfg_corev.gpr[0], status, status.name()));
      instr.push_back($sformatf("srli x%0d, x%0d, 13", cfg_corev.gpr[0], cfg_corev.gpr[0]));
      instr.push_back($sformatf("andi x%0d, x%0d, 0x3", cfg_corev.gpr[0], cfg_corev.gpr[0]));  //Check MSTATUS.FS bit
      instr.push_back($sformatf("li x%0d, 0x%0x", cfg_corev.gpr[1], 3));
      if (cfg_corev.enable_nested_interrupt) begin
        // fixme: refer workaround_1
        instr.push_back($sformatf("# bne x%0d, x%0d, 2f # workaround for mstatus.FS during nested irq", cfg_corev.gpr[0], cfg_corev.gpr[1])); // MSTATUS.FS!=3 do not push
      end
      else begin
        instr.push_back($sformatf("bne x%0d, x%0d, 2f", cfg_corev.gpr[0], cfg_corev.gpr[1])); // MSTATUS.FS!=3 do not push
      end

      // Reserve space from kernel stack to save all 32 FPR + FCSR
      instr.push_back($sformatf("addi x%0d, x%0d, -%0d", sp, sp, 33 * (XLEN/8)));
      // Push all FPRs to kernel stack
      for(int i = 0; i < 32; i++) begin
        instr.push_back($sformatf("%0s  f%0d, %0d(x%0d)", store_instr, i, i * (XLEN/8), sp));
      end

      store_instr = (XLEN == 32) ? "sw" : "sd";

      // Push FCSR to kernel stack
      instr.push_back($sformatf("fscsr x%0d, x0", cfg_corev.gpr[0])); // Read and Clear FCSR
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, cfg_corev.gpr[0], 32 * (XLEN/8), sp));

      // Reserve space from kernel stack to save MSTATUS.FS
      instr.push_back($sformatf("addi x%0d, x%0d, -%0d", sp, sp, 1 * (XLEN/8)));

      // Push MSTATUS.FS to kernel stack
      instr.push_back($sformatf("csrr x%0d, 0x%0x # %0s", cfg_corev.gpr[0], status, status.name()));
      instr.push_back($sformatf("srli x%0d, x%0d, 13", cfg_corev.gpr[0], cfg_corev.gpr[0]));
      instr.push_back($sformatf("andi x%0d, x%0d, 0x3", cfg_corev.gpr[0], cfg_corev.gpr[0]));
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, cfg_corev.gpr[0], 0, sp));

      //Set the MSTATUS.FS status to Clean
      instr.push_back($sformatf("li x%0d, 0x%0x", cfg_corev.gpr[0], 1));  //Set FS from 3->2 Clean, clear bit 13
      instr.push_back($sformatf("slli x%0d, x%0d, 13", cfg_corev.gpr[0], cfg_corev.gpr[0]));
      instr.push_back($sformatf("csrrc x0, 0x%0x, x%0d # %0s", status, cfg_corev.gpr[0], status.name()));

      instr.push_back($sformatf("j 3f"));

      instr.push_back($sformatf("2: nop")); //BNE 2f Target

      // Reserve space from kernel stack to save MSTATUS.FS
      instr.push_back($sformatf("addi x%0d, x%0d, -%0d", sp, sp, 1 * (XLEN/8)));

      // Push MSTATUS.FS to kernel stack
      instr.push_back($sformatf("csrr x%0d, 0x%0x # %0s", cfg_corev.gpr[0], status, status.name()));
      instr.push_back($sformatf("srli x%0d, x%0d, 13", cfg_corev.gpr[0], cfg_corev.gpr[0]));
      instr.push_back($sformatf("andi x%0d, x%0d, 0x3", cfg_corev.gpr[0], cfg_corev.gpr[0]));
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, cfg_corev.gpr[0], 0, sp));

      instr.push_back($sformatf("3: nop")); //Jump 3f Target

      //Check if mstatus.FS != 0 ,i.e., Not "All Off" state
      instr.push_back($sformatf("csrr x%0d, 0x%0x # %0s", cfg_corev.gpr[0], status, status.name()));
      instr.push_back($sformatf("srli x%0d, x%0d, 13", cfg_corev.gpr[0], cfg_corev.gpr[0]));
      instr.push_back($sformatf("andi x%0d, x%0d, 0x3", cfg_corev.gpr[0], cfg_corev.gpr[0]));  //Check MSTATUS.FS bit
      instr.push_back($sformatf("bnez x%0d, 4f", cfg_corev.gpr[0])); // check MSTATUS.FS!=0

      // if MSTATUS.FS==0 set MSTATUS.FS to Initial
      instr.push_back($sformatf("li x%0d, 0x%0x", cfg_corev.gpr[0], 1));  //Change FS from 0 to 1, i.e., Initial
      instr.push_back($sformatf("slli x%0d, x%0d, 13", cfg_corev.gpr[0], cfg_corev.gpr[0]));
      instr.push_back($sformatf("csrrs x0, 0x%0x, x%0d # %0s", status, cfg_corev.gpr[0], status.name()));

      instr.push_back($sformatf("4: nop")); //BNE 4f Target

    end

  endfunction

  // Pop general purpose register from stack + FPR + FCSR
  function automatic void pop_regfile_from_kernel_stack(privileged_reg_t status,
                                                        privileged_reg_t scratch,
                                                        bit mprv,
                                                        riscv_reg_t sp,
                                                        riscv_reg_t tp,
                                                        ref string instr[$],
                                                        cv32e40p_instr_gen_config cfg_corev);


    string load_instr;

    if(cfg_corev.enable_floating_point && !cfg_corev.enable_fp_in_x_regs) begin
      load_instr = (XLEN == 32) ? "lw" : "ld";

      // Pop MSTATUS.FS from kernel stack
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, cfg_corev.gpr[0], 0, sp));

      // Restore MSTATUS.FS
      if (cfg_corev.enable_nested_interrupt) begin
        // fixme: refer workaround_1
        // do not clear FS
      end
      else begin
        instr.push_back($sformatf("li x%0d, 0x%0x", cfg_corev.gpr[1], 3));  //Clear FS
        instr.push_back($sformatf("slli x%0d, x%0d, 13", cfg_corev.gpr[1], cfg_corev.gpr[1]));
        instr.push_back($sformatf("csrrc x0, 0x%0x, x%0d # %0s", status, cfg_corev.gpr[1], status.name()));
        instr.push_back($sformatf("slli x%0d, x%0d, 13", cfg_corev.gpr[1], cfg_corev.gpr[0]));
        instr.push_back($sformatf("csrrs x0, 0x%0x, x%0d # %0s", status, cfg_corev.gpr[1], status.name()));
      end

      // Restore kernel stack pointer
      instr.push_back($sformatf("addi x%0d, x%0d, %0d", sp, sp, 1 * (XLEN/8)));

      instr.push_back($sformatf("li x%0d, 0x%0x", cfg_corev.gpr[1], 3));
      if (cfg_corev.enable_nested_interrupt) begin
        // fixme: refer workaround_1
        instr.push_back($sformatf("# bne x%0d, x%0d, 2f # workaround for mstatus.FS during nested irq", cfg_corev.gpr[0], cfg_corev.gpr[1])); // MSTATUS.FS!=3 do not pop FPR
      end
      else begin
        instr.push_back($sformatf("bne x%0d, x%0d, 2f", cfg_corev.gpr[0], cfg_corev.gpr[1])); // MSTATUS.FS!=3 do not pop FPR
      end

      randcase
        1: load_instr = (FLEN == 32) ? "flw" : "fld";
        (sp == 2): load_instr = (FLEN == 32) ? "c.flwsp" : "fld";
      endcase

      // Pop FPRs from kernel stack
      for(int i = 0; i < 32; i++) begin
        instr.push_back($sformatf("%0s  f%0d, %0d(x%0d)", load_instr, i, i * (FLEN/8), sp));
      end

      load_instr = (XLEN == 32) ? "lw" : "ld";

      // Pop FCSR from kernel stack
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, cfg_corev.gpr[1], 32 * (XLEN/8), sp));
      instr.push_back($sformatf("fscsr x%0d", cfg_corev.gpr[1])); // Restore FCSR

      // Restore kernel stack pointer
      instr.push_back($sformatf("addi x%0d, x%0d, %0d", sp, sp, 33 * (XLEN/8)));

      instr.push_back($sformatf("2: nop")); //BNE 2f Target

    end

    // fixme: the irq handling logic flow need to be rework to consider nested irq scenario for fpu csr such as FS.  
    // workaround_1 for MSTATUS.FS during nested irq by assuming FS always DIRTY prior irq handling.
    if (cfg_corev.enable_nested_interrupt) begin
      // always set FS to DIRTY prior mret
      instr.push_back($sformatf("li x%0d, 0x3             # workaround for mstatus.FS during nested irq", cfg_corev.gpr[1]));
      instr.push_back($sformatf("slli x%0d, x%0d, 13      # workaround for mstatus.FS during nested irq", cfg_corev.gpr[1], cfg_corev.gpr[1]));
      instr.push_back($sformatf("csrrs x0, mstatus, x%0d  # workaround for mstatus.FS during nested irq", cfg_corev.gpr[1]));
    end

    load_instr = (XLEN == 32) ? "lw" : "ld";
    // Pop user mode GPRs from kernel stack
    for(int i = 1; i < 32; i++) begin
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, i, (i-1) * (XLEN/8), sp));
    end
    // Restore kernel stack pointer
    instr.push_back($sformatf("addi x%0d, x%0d, %0d", sp, sp, 31 * (XLEN/8)));
    if (scratch inside {implemented_csr}) begin
      // Move SP to TP
      instr.push_back($sformatf("add x%0d, x%0d, zero", tp, sp));
      // Restore user mode stack pointer
      instr.push_back($sformatf("csrrw x%0d, 0x%0x, x%0d", sp, scratch, sp));
    end
  endfunction

endpackage : cv32e40p_instr_test_pkg;
