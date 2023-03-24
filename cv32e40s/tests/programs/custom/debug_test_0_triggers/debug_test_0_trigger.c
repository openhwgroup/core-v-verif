// Copyright 2023 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License");
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Author: Halfdan Bechmann - halfdan.bechmann@silabs.com                     //
//                                                                            //
// Debug 0 Triggers Test                                                      //
//                                                                            //
// Requires: DBG_NUM_TRIG == 0                                                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>
#include "corev_uvmt.h"

#define FAIL    1
#define SUCCESS 0

#define DEBUG_REQ_CONTROL_REG *(volatile int *) CV_VP_DEBUG_CONTROL_BASE

#define DEBUG_SEL_IDLE 0
#define DEBUG_SEL_REGTEST 4
#define DEBUG_SEL_ENTER_USERMODE 5
#define DEBUG_SEL_ENTER_MACHINEMODE 6

#define DEBUG_STATUS_NOT_ENTERED  0
#define DEBUG_STATUS_ENTERED_OK   1
#define DEBUG_STATUS_ENTERED_FAIL 2

#define PRIV_LVL_USER_MODE    0
#define PRIV_LVL_MACHINE_MODE 1

                                // Place in debugger section
void _debugger_start(void)           __attribute__((section(".debugger"), naked));
void _debug_handler(void)            __attribute__((section(".debugger")));
int  _debug_mode_register_test(void) __attribute__((section(".debugger")));

void _debugger_exception_start(void) __attribute__((section(".debugger_exception"), naked));

void handle_illegal_insn(void)       __attribute__((naked));
extern void end_handler_incr_mepc(void);

volatile uint32_t num_triggers;

volatile int debug_sel;
volatile int debug_break_loop;
volatile int debug_entry_status;

volatile uint32_t illegal_insn_status;
volatile uint32_t debug_exception_status;

/*
 * handle_illegal_insn
 *
 * Illegal Instruction Handler
 *
 * Sets the illegal_insn_status variable to 1 when an illegal instruction traps
 *
 */
void handle_illegal_insn (void) {
  __asm__ volatile (R"(
    la   t0,     illegal_insn_status
    li   t1,     1
    sw   t1,     0(t0)
    call end_handler_incr_mepc
  )" ::: "t0", "t1", "memory");
}


/*
 * _debugger_exception_start
 *
 * Debug exception handler
 *
 * Handles exceptions that occur in debug mode, generally seen as irrecoverable event
 * But used in this test to check register access. Sets debug_exception_status and
 * returns to address saved in the debug scratch register (dscratch).
 */
void _debugger_exception_start(void) {
  __asm__ volatile (R"(
           cm.push {ra, s0-s2}, -16

           la   s1,     debug_exception_status
           li   s0,     1
           sw   s0,     0(s1)

           cm.pop {ra, s0-s2}, 16
           csrr t6, dscratch
           jr t6
      )" ::: "t6");
}

/*
 * debugger_start
 *
 * Debug handler wrapper
 *
 * Saves registers, calls debug handler and then restores the registers again.
 *
 */
void _debugger_start(void) {
  __asm__ volatile (R"(
    # Store return address and saved registers

      sw a0, -4(sp)
      sw a1, -8(sp)
      sw a2, -12(sp)
      sw a3, -16(sp)
      sw a4, -20(sp)
      sw a5, -24(sp)
      sw a6, -28(sp)
      sw a7, -32(sp)
      sw t0, -36(sp)
      sw t1, -40(sp)
      sw t2, -44(sp)
      sw t3, -48(sp)
      sw t4, -52(sp)
      sw t5, -56(sp)
      sw t6, -60(sp)
      addi sp, sp, -64

      cm.push {ra, s0-s11}, -64

    # Execute _debug_handler() function
      call ra, _debug_handler

    # Restore return address and saved registers
      cm.pop {ra, s0-s11}, 64

      addi sp, sp, 64
      lw a0, -4(sp)
      lw a1, -8(sp)
      lw a2, -12(sp)
      lw a3, -16(sp)
      lw a4, -20(sp)
      lw a5, -24(sp)
      lw a6, -28(sp)
      lw a7, -32(sp)
      lw t0, -36(sp)
      lw t1, -40(sp)
      lw t2, -44(sp)
      lw t3, -48(sp)
      lw t4, -52(sp)
      lw t5, -56(sp)
      lw t6, -60(sp)

    # Exit debug mode
      dret
  )");
}

/*
 * _debug_handler
 *
 * Debug Handler
 *
 * Handles all actions needed in debug mode.
 *
 */
void _debug_handler (void) {

  printf("  Entered debug\n");

  debug_entry_status = DEBUG_STATUS_ENTERED_OK;

  switch (debug_sel) {

    case DEBUG_SEL_REGTEST:
      _debug_mode_register_test();
    break;

    case DEBUG_SEL_ENTER_USERMODE:
      printf("-- User Mode --\n");
      __asm__ volatile ("csrci dcsr, 0x3");
      break;

    case DEBUG_SEL_ENTER_MACHINEMODE:
      printf("-- Machine Mode --\n");
      __asm__ volatile ("csrsi dcsr, 0x3");
      break;

  }

  __asm__ volatile (R"(
        # Increment dpc to skip matched instruction
           csrr s0, dpc
           lb   s1, 0(s0)
           li   s2, 0x3
           and  s1, s1, s2
           bne  s1, s2, 1f
           addi s0, s0, 0x2
         1:addi s0, s0, 0x2
           csrw dpc, s0
      )" ::: "s0", "s1", "s2");

  return;
}


/*
 * execute_debug_command
 *
 * Sends commands debug handler
 *
 * Needed to execute commands that require to run with debug privelege
 *
 */
void execute_debug_command (uint32_t dbg_cmd) {
  // Disable trigger after use
  debug_sel = dbg_cmd;

  debug_entry_status = DEBUG_STATUS_NOT_ENTERED;
  // Assert debug req
  DEBUG_REQ_CONTROL_REG = (CV_VP_DEBUG_CONTROL_DBG_REQ(0x1)        |
                           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1)       |
                           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x8) |
                           CV_VP_DEBUG_CONTROL_START_DELAY(0xc8));
  // Wait for debug entry
  while (debug_entry_status == DEBUG_STATUS_NOT_ENTERED);
}

/*
 * _debug_mode_register_test
 *
 * Debug mode register access test
 *
 * Checks that registers that should not exist cause a trap in debug mode
 *
 */
int _debug_mode_register_test(void) {
  printf("    _debug_mode_register_test():\n");

  // TSELECT - Read/write valid value (in debug mode), check that it traps
  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrr  s0, tselect
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrwi tselect, 0x0
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  // TDATA1 - Read/write valid value (in debug mode), check that it traps
  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrr  s0, tdata1
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrwi tdata1, 0x0
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  // TDATA2 - Read/Write valid value (in debug mode), check that it traps
  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrr  s0, tdata2
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrwi tdata2, 0x0
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  // TINFO - Read/Write valid value (in debug mode), check that it traps
  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrr  s0, tinfo
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrwi tinfo, 0x0
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  // TCONTROL - Read/Write valid value (in debug mode), check that it traps
  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrr  s0, tcontrol
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrwi tcontrol, 0x0
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  // Context Registers - Access Checks (in debug mode)
  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrwi mcontext, 0x0
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrwi mscontext, 0x0
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrwi hcontext, 0x0
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  debug_exception_status = 0;
  __asm__ volatile (R"(la   s0, 1f
                       csrw dscratch, s0
                       csrwi scontext, 0x0
                     1:nop)" ::: "s0");
  if (!debug_exception_status) return FAIL;

  return SUCCESS;
}


/*
 * test_register_access
 *
 * Register access test
 *
 * Checks that registers that should not exist
 * cause a trap in machine mode and user mode
 */
int test_register_access(void) {

  printf("\n\n\n --- Testing register access ---\n\n");

  printf("  Checking register access from debug mode\n");
  debug_sel = DEBUG_SEL_REGTEST;
  debug_entry_status = DEBUG_STATUS_NOT_ENTERED;
  DEBUG_REQ_CONTROL_REG = (CV_VP_DEBUG_CONTROL_DBG_REQ(0x1)        |
                           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1)       |
                           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x8) |
                           CV_VP_DEBUG_CONTROL_START_DELAY(0xc8));
  // Wait for debug entry
  while (debug_entry_status == DEBUG_STATUS_NOT_ENTERED);
  if (debug_entry_status == DEBUG_STATUS_ENTERED_FAIL) return FAIL;
  debug_entry_status = DEBUG_STATUS_NOT_ENTERED;

  printf("\n  Checking register access from Machine mode\n");

  // TSELECT - Read/write valid value (in machine mode), check that it traps
  illegal_insn_status = 0;
  __asm__ volatile ("csrr  s0, tselect" ::: "s0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi tselect, 0x0");
  if (!illegal_insn_status) return FAIL;

  // TDATA1 - Read/write valid value (in machine mode), check that it traps
  illegal_insn_status = 0;
  __asm__ volatile ("csrr  s0, tdata1" ::: "s0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi tdata1, 0x0");
  if (!illegal_insn_status) return FAIL;

  // TDATA2 - Read/Write valid value (in machine mode), check that it traps
  illegal_insn_status = 0;
  __asm__ volatile ("csrr  s0, tdata2" ::: "s0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi tdata2, 0x0");
  if (!illegal_insn_status) return FAIL;

  // TINFO - Read/Write valid value (in machine mode), check that it traps
  illegal_insn_status = 0;
  __asm__ volatile ("csrr  s0, tinfo" ::: "s0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi tinfo, 0x0");
  if (!illegal_insn_status) return FAIL;

  // TCONTROL - Read/Write valid value (in machine mode), check that it traps
  illegal_insn_status = 0;
  __asm__ volatile ("csrr  s0, tcontrol" ::: "s0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi tcontrol, 0x0");
  if (!illegal_insn_status) return FAIL;

  // Context Registers - Access Checks (in machine mode)
  illegal_insn_status = 0;
  __asm__ volatile ("csrwi mcontext, 0x0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi mscontext, 0x0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi hcontext, 0x0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi scontext, 0x0");
  if (!illegal_insn_status) return FAIL;

  execute_debug_command(DEBUG_SEL_ENTER_USERMODE);

  // TSELECT - Read/write valid value (in u-mode), check that it traps
  illegal_insn_status = 0;
  __asm__ volatile ("csrr  s0, tselect" ::: "s0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi tselect, 0x0");
  if (!illegal_insn_status) return FAIL;

  // TDATA1 - Read/write valid value (in u-mode), check that it traps
  illegal_insn_status = 0;
  __asm__ volatile ("csrr  s0, tdata1" ::: "s0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi tdata1, 0x0");
  if (!illegal_insn_status) return FAIL;


  // TDATA2 - Read/Write valid value (in u-mode), check that it traps
  illegal_insn_status = 0;
  __asm__ volatile ("csrr  s0, tdata2" ::: "s0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi tdata2, 0x0");
  if (!illegal_insn_status) return FAIL;

  // TINFO - Read/Write valid value (in u-mode), check that it traps
  illegal_insn_status = 0;
  __asm__ volatile ("csrr  s0, tinfo" ::: "s0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi tinfo, 0x0");
  if (!illegal_insn_status) return FAIL;

  // TCONTROL - Read/Write valid value (in u-mode), check that it traps
  illegal_insn_status = 0;
  __asm__ volatile ("csrr  s0, tcontrol" ::: "s0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi tcontrol, 0x0");
  if (!illegal_insn_status) return FAIL;

  // Context Registers - Access Checks (in user mode)
  illegal_insn_status = 0;
  __asm__ volatile ("csrwi mcontext, 0x0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi mscontext, 0x0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi hcontext, 0x0");
  if (!illegal_insn_status) return FAIL;

  illegal_insn_status = 0;
  __asm__ volatile ("csrwi scontext, 0x0");
  if (!illegal_insn_status) return FAIL;

  execute_debug_command(DEBUG_SEL_ENTER_MACHINEMODE);

  return SUCCESS;
}

/*
 * pmp_setup
 *
 * PMP setup function
 *
 * Allows access to full memory map from user mode
 */
void pmp_setup(void) {
  __asm__ volatile (R"(li    t0, 0xFFFFFFFF
                       csrw  pmpaddr0, t0
                       csrwi pmpcfg0, ((1 << 3) | (7 << 0))
                       )" ::: "t0");
}


/*
 * main
 *
 * Test Entry point
 *
 */
int main(int argc, char *argv[])
{
  pmp_setup();

  if (test_register_access()) {
    printf("Register access test failed\n");
    return FAIL;
  }

  printf("Finished \n");
  return SUCCESS;
}

