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
// Debug Trigger Test                                                         //
//                                                                            //
// Requires: DBG_NUM_TRIG > 0                                                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdint.h>
#include "corev_uvmt.h"

#define FAIL    1
#define SUCCESS 0

//#define DEBUG_PRINT 1

#define DEBUG_REQ_CONTROL_REG *(volatile int *) CV_VP_DEBUG_CONTROL_BASE

#define DEBUG_SEL_IDLE 0
#define DEBUG_SEL_DISABLE_TRIGGER 1
#define DEBUG_SEL_SETUP_TRIGGER 2
#define DEBUG_SEL_CLEAR_TDATA2 3
#define DEBUG_SEL_REGTEST 4
#define DEBUG_SEL_ENTER_USERMODE 5
#define DEBUG_SEL_ENTER_MACHINEMODE 6

#define DEBUG_STATUS_NOT_ENTERED  0
#define DEBUG_STATUS_ENTERED_OK   1
#define DEBUG_STATUS_ENTERED_FAIL 2

#define PRIV_LVL_USER_MODE    0
#define PRIV_LVL_MACHINE_MODE 1

#define DEBUG_LOOPBREAK_NONE    0
#define DEBUG_LOOPBREAK_TDATA1  1
#define DEBUG_LOOPBREAK_TDATA2  2
#define DEBUG_LOOPBREAK_DPCINCR 3

#define TRIGGER_NONE              0
#define TRIGGER_LOAD_BYTE         1
#define TRIGGER_LOAD_HALFWORD     2
#define TRIGGER_LOAD_WORD         3
#define TRIGGER_STORE_BYTE        4
#define TRIGGER_STORE_HALFWORD    5
#define TRIGGER_STORE_WORD        6
#define TRIGGER_EXECUTE           7
#define TRIGGER_EXCEPTION_ILLEGAL 8
#define TRIGGER_EXCEPTION_EBREAK  9

#define EXCEPTION_CODE_ILLEGAL_INSTRUCTION 2
#define EXCEPTION_CODE_BREAKPOINT          3
#define EXCEPTION_CODE_RESERVED           10


extern void end_handler_incr_mepc(void);

void _debugger_start(void)           __attribute__((section(".debugger"))) __attribute__((naked));
void _debug_handler(void)            __attribute__((section(".debugger")));
void _debug_mode_register_test(void) __attribute__((section(".debugger")));
void execute_test_high_addr(void)    __attribute__((section(".debugger_exception")))__attribute__ ((noinline));
void load_store_test_high_addr(void) __attribute__((section(".debugger_exception")))__attribute__ ((noinline));
void handle_illegal_insn(void)       __attribute__ ((naked));

void execute_test_constructor(void)    __attribute__ ((constructor)) __attribute__ ((noinline));
void load_store_test_constructor(void) __attribute__ ((constructor)) __attribute__ ((noinline));

volatile void trigger_code_nop(void)             __attribute__((optimize("O0"))) __attribute__((naked));
volatile void trigger_code_ebreak(void)          __attribute__((optimize("O0"))) __attribute__((naked));
volatile void trigger_code_cebreak(void)         __attribute__((optimize("O0"))) __attribute__((naked));
volatile void trigger_code_branch_insn(void)     __attribute__((optimize("O0"))) __attribute__((naked));
volatile void trigger_code_illegal_insn(void)    __attribute__((optimize("O0"))) __attribute__((naked));
volatile void trigger_code_multicycle_insn(void) __attribute__((optimize("O0"))) __attribute__((naked));

int test_execute_trigger(int);
int test_load_trigger(int);
int test_store_trigger(int);
int test_exception_trigger(int);

volatile uint32_t tdata1_next;
volatile uint32_t tdata2_next;
volatile uint32_t tdata2_next_offset;

volatile int      trigger_type;
volatile uint32_t trigger_address;
volatile uint32_t trigger_sel;
volatile uint32_t num_triggers;

volatile int debug_sel;
volatile int debug_break_loop;
volatile int debug_entry_status;

volatile uint32_t illegal_insn_status;

volatile uint8_t  some_data_bytes[4]     = {0xC0, 0xFF, 0xEB, 0xEE};
volatile uint16_t some_data_halfwords[2] = {0xDEAD, 0xBEEF};
volatile uint32_t some_data_word         = 0xC0DECAFE;

/*
 * execute_test_constructor
 *
 * Executes nop.
 *
 * Defined as constructor to be placed before main in memory
 * used for its low address in execute LESS comparisons
 */
void execute_test_constructor(void) {
  __asm__ volatile ("nop");
}

/*
 * execute_test_high_addr
 *
 * Executes nop.
 *
 * Placed in debugger_exception section and used for
 * its high address in execute test GEQ comparisons
 *
 */
void execute_test_high_addr(void) {
  __asm__ volatile ("nop");
}

/*
 * load_store_test_constructor
 *
 * Uncompressed nop, to be used as variable after construction phase.
 *
 * Defined as constructor to be placed before main in memory
 * used for its low address in load/store LESS comparisons
 */
void load_store_test_constructor(void) {
  __asm__ volatile (R"(.option push
                       .option norvc
                       nop
                       .option pop)");
}
/*
 * load_store_test_high_addr
 *
 * To be used as variable.
 *
 * Placed in debugger_exception section and used for
 * its high address in load/store test GEQ comparisons
 */
void load_store_test_high_addr(void) {
  __asm__ volatile (".word(0xDEADBEEF)");
}

/*
 * handle_illegal_insn
 *
 * Sets illegal_insn_status.
 *
 * Simple handler used to check illegal intructuction trap
 */
void handle_illegal_insn (void) {
  __asm__ volatile (R"(
    la   t0,     illegal_insn_status
    li   t1,     1
    sw   t1,     0(t0)
    call end_handler_incr_mepc
  )");
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
      addi sp, sp, -32

      cm.push {ra, s0-s11}, -64

    # Execute _debug_handler() function
      call ra, _debug_handler

    # Restore return address and saved registers
      cm.pop {ra, s0-s11}, 64

      addi sp, sp, 32
      lw a0, -4(sp)
      lw a1, -8(sp)
      lw a2, -12(sp)
      lw a3, -16(sp)
      lw a4, -20(sp)
      lw a5, -24(sp)
      lw a6, -28(sp)
      lw a7, -32(sp)

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

#ifdef DEBUG_PRINT
  printf("  Entered debug\n");
#endif

  debug_entry_status = DEBUG_STATUS_ENTERED_OK;

  switch (debug_sel) {

    case DEBUG_SEL_DISABLE_TRIGGER:
      switch (trigger_type) {
        case TRIGGER_LOAD_BYTE:
        case TRIGGER_LOAD_HALFWORD:
        case TRIGGER_LOAD_WORD:
          __asm__ volatile ("csrci tdata1, (1 << 0)"); // Clear load bit
#ifdef DEBUG_PRINT
          printf("    Disabling trigger by clearing TDATA1->LOAD\n");
#endif
          break;
        case TRIGGER_STORE_BYTE:
        case TRIGGER_STORE_HALFWORD:
        case TRIGGER_STORE_WORD:
          __asm__ volatile ("csrci tdata1, (1 << 1)"); // Clear load bit
#ifdef DEBUG_PRINT
          printf("    Disabling trigger by clearing TDATA1->STORE\n");
#endif
          break;
        case TRIGGER_EXECUTE:
          __asm__ volatile ("csrci tdata1, (1 << 2)"); // Clear execute bit
#ifdef DEBUG_PRINT
          printf("    Disabling trigger by clearing TDATA1->EXECUTE\n");
#endif
          break;
      }
    break;

    case DEBUG_SEL_SETUP_TRIGGER:
      // Load tdata config csrs
#ifdef DEBUG_PRINT
      printf("    Setting up triggers\n      csr_write: tdata1 = 0x%08lx\n      csr_write: tdata2 = 0x%08lx (0x%lx + 0x%lx)\n",
             tdata1_next, tdata2_next, trigger_address, tdata2_next_offset);
#endif
      __asm__ volatile (R"(la   s1,     tdata1_next
                           lw   s0,     0(s1)
                           csrw tdata1, s0
                           la   s1,     tdata2_next
                           lw   s0,     0(s1)
                           csrw tdata2, s0)" ::: "s0", "s1");
    break;

    case DEBUG_SEL_CLEAR_TDATA2:
      __asm__ volatile ("csrwi tdata2, 0x0");
#ifdef DEBUG_PRINT
      printf("    Disabling trigger by clearing TDATA2\n");
#endif
    break;

    case DEBUG_SEL_REGTEST:
      _debug_mode_register_test();
    break;

    case DEBUG_SEL_ENTER_USERMODE:
#ifdef DEBUG_PRINT
      printf("-- User Mode --\n");
#endif
      __asm__ volatile ("csrci dcsr, 0x3");
      break;

    case DEBUG_SEL_ENTER_MACHINEMODE:
#ifdef DEBUG_PRINT
      printf("-- Machine Mode --\n");
#endif
      __asm__ volatile ("csrsi dcsr, 0x3");
      break;

  }

  switch (debug_break_loop) {
    case DEBUG_LOOPBREAK_NONE:
      break;
    case DEBUG_LOOPBREAK_TDATA1:
      debug_sel = DEBUG_SEL_DISABLE_TRIGGER;
      break;
    case DEBUG_LOOPBREAK_TDATA2:
      // Avoid re-triggering when returning to dpc
      debug_sel = DEBUG_SEL_CLEAR_TDATA2;
      break;
    case DEBUG_LOOPBREAK_DPCINCR:
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
#ifdef DEBUG_PRINT
      printf("    Incrementing dpc\n");
#endif
      break;
  }
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
 * trigger_code_nop
 *
 * Function for testing execute triggers.
 *
 * These functions need at least two intructions as the first can be skipped with a dpc inrement
 *
 */
volatile void trigger_code_nop() {
  __asm__ volatile (R"(nop
                       nop
                       ret)");
}

/*
 * trigger_code_*
 *
 * Functions with different first instructions for testing execte triggers.
 *
 * These functions are used to check that different types of instructions are preempted
 * correctly with "before"-timing during trigger match
 *
 */
volatile void trigger_code_ebreak() {
  __asm__ volatile (R"(.4byte 0x00100073 # ebreak
                       nop
                       ret)");
}
volatile void trigger_code_cebreak() {
  __asm__ volatile (R"(c.ebreak
                       nop
                       ret)");
}
volatile void trigger_code_branch_insn() {
  __asm__ volatile (R"(beq t0, t0, trigger_code_ebreak
                       nop
                       ret)");
}
volatile void trigger_code_illegal_insn() {
  __asm__ volatile (R"(dret
                       nop
                       ret)");
}
volatile void trigger_code_multicycle_insn() {
  __asm__ volatile (R"(mulhsu t0, t0, t1
                       nop
                       ret)");
}

/*
 * trigger_test
 *
 * Test function that configures and tests triggers
 *
 * Configures triggers based on input and global variables,
 * runs test and checks if the result is expected.
 *
 */
int trigger_test (int setup, int expect_trigger_match, uint32_t tdata2_arg) {

#ifdef DEBUG_PRINT
  printf ("\ntrigger_test():\n");
#endif

  tdata2_next        = tdata2_arg + tdata2_next_offset;
  trigger_address    = tdata2_arg;
  debug_entry_status = DEBUG_STATUS_NOT_ENTERED;

  if (setup) {
    debug_sel = DEBUG_SEL_SETUP_TRIGGER;

    // Assert debug req
    DEBUG_REQ_CONTROL_REG = (CV_VP_DEBUG_CONTROL_DBG_REQ(0x1)        |
                             CV_VP_DEBUG_CONTROL_REQ_MODE(0x1)       |
                             CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x8) |
                             CV_VP_DEBUG_CONTROL_START_DELAY(0xc8));
    // Wait for debug entry
    while (debug_entry_status == DEBUG_STATUS_NOT_ENTERED);
    debug_entry_status = DEBUG_STATUS_NOT_ENTERED;
  }

  debug_sel = DEBUG_SEL_IDLE;

  if (trigger_type == TRIGGER_LOAD_BYTE) {
    __asm__ volatile (R"(lw s4, trigger_address
                         lb s3, 0(s4)          )" ::: "s3", "s4");
  }
  if (trigger_type == TRIGGER_LOAD_HALFWORD) {
    __asm__ volatile (R"(lw s4, trigger_address
                         lh s3, 0(s4)          )" ::: "s3", "s4");
  }
  if (trigger_type == TRIGGER_LOAD_WORD) {
    __asm__ volatile (R"(lw s4, trigger_address
                         lw s3, 0(s4)          )" ::: "s3", "s4");
  }
  if (trigger_type == TRIGGER_STORE_BYTE) {
    __asm__ volatile (R"(lw s4, trigger_address
                         sb s3, 0(s4)          )" ::: "s3", "s4");
  }
  if (trigger_type == TRIGGER_STORE_HALFWORD) {
    __asm__ volatile (R"(lw s4, trigger_address
                         sh s3, 0(s4)          )" ::: "s3", "s4");
  }
  if (trigger_type == TRIGGER_STORE_WORD) {
    __asm__ volatile (R"(lw s4, trigger_address
                         sw s3, 0(s4)          )" ::: "s3", "s4");
  }
  if (trigger_type == TRIGGER_EXECUTE) {
    __asm__ volatile (R"(lw   s4, trigger_address
                         jalr ra, s4             )" ::: "ra", "s4"); // Jump to triggered address
  }
  if (trigger_type == TRIGGER_EXCEPTION_ILLEGAL) {
    __asm__ volatile ("csrwi mcontext, 0x0");
  }
  if (trigger_type == TRIGGER_EXCEPTION_EBREAK) {
    __asm__ volatile ("ebreak");
  }

  if (debug_entry_status == expect_trigger_match) {
#ifdef DEBUG_PRINT
    printf ("  Debug entry status: %d (expected: %d)\n\n",
            debug_entry_status,   expect_trigger_match);
#endif
    return SUCCESS;
  } else {
    printf ("  FAIL: Debug entry did not match expectation: %d (expected: %d)\n\n",
            debug_entry_status,   expect_trigger_match);
    return FAIL;
  }
}

/*
 * test_execute_trigger
 *
 * Execute trigger test
 *
 * Tests execute triggers with a range of configurations.
 *
 */
int test_execute_trigger (int priv_lvl) {
  int retval = 0;
  tdata2_next_offset = 0;

  if (priv_lvl == PRIV_LVL_USER_MODE) {
    printf("\n\n\n --- Testing execute triggers (in user mode) ---\n\n");
    execute_debug_command(DEBUG_SEL_ENTER_USERMODE);

  } else if (priv_lvl == PRIV_LVL_MACHINE_MODE) {
    printf("\n\n\n --- Testing execute triggers (in machine mode) ---\n\n");
    execute_debug_command(DEBUG_SEL_ENTER_MACHINEMODE);
  }

  // Set up trigger
  tdata1_next = (6 << 28 | // TYPE = 6
                 1 << 12 | // ACTION = Enter debug mode
                 0 << 7  | // MATCH = EQ
                 1 << 6  | // M = Match in machine mode
                 1 << 3  | // U = Match in user mode
                 1 << 2 ); // EXECUTE = Match on instruction address

  trigger_type     = TRIGGER_EXECUTE;
  debug_break_loop = DEBUG_LOOPBREAK_TDATA2;

  // Check that executing trigger_code function does not trigger when it is not set up
  retval += trigger_test(0, 0, (uint32_t) &trigger_code_nop);

  // Check that clearing tdata2 prevents re-triggering upon return
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_nop);

  // Check that executing trigger_code function does not trigger when it is disabled in tdata1
  retval += trigger_test(0, 0, (uint32_t) &trigger_code_nop);

  // Check that executing various instructions at the triggered address causes debug entry
  // and make sure it is not executed before entering debug
  debug_break_loop = DEBUG_LOOPBREAK_DPCINCR;
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_nop);
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_ebreak);
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_cebreak);
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_branch_insn);
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_illegal_insn);
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_multicycle_insn);



  // Trigger on current privilege mode only //

  // Set up trigger
  tdata1_next = (6 << 28 | // TYPE = 6
                 1 << 12 | // ACTION = Enter debug mode
                 0 << 7  | // MATCH = EQ
                 1 << 2 ); // EXECUTE = Match on instruction address

  if (priv_lvl == PRIV_LVL_MACHINE_MODE) {
    tdata1_next |= (1 << 6); // M = Match in machine mode
  } else if (priv_lvl == PRIV_LVL_USER_MODE){
    tdata1_next |= (1 << 3); // M = Match in user mode
  }
  trigger_type     = TRIGGER_EXECUTE;
  debug_break_loop = DEBUG_LOOPBREAK_TDATA2;

  // Check that clearing tdata2 prevents re-triggering upon return
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_nop);

  // Check that executing various instructions at the triggered address causes debug entry
  // and make sure it is not executed before entering debug
  debug_break_loop = DEBUG_LOOPBREAK_DPCINCR;
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_nop);
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_ebreak);
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_cebreak);
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_branch_insn);
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_illegal_insn);
  retval += trigger_test(1, 1, (uint32_t) &trigger_code_multicycle_insn);

  tdata1_next |= 2 << 7; // Set MATCH = 2 (GEQ)
  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  // Executing from start of debug memory to avoid triggering on instructions executed in the the test flow (like debug handler)
  retval += trigger_test(1, 1, (uint32_t) &execute_test_high_addr);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 1, (uint32_t) &execute_test_high_addr);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &execute_test_high_addr);

  tdata1_next |=  3 << 7; // Set MATCH = 3 (LESS)
  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  // Executing from constructor as it is known to have a lower address than other functions
  tdata2_next_offset = 0;
  retval += trigger_test(1, 0, (uint32_t) &execute_test_constructor);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &execute_test_constructor);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 1, (uint32_t) &execute_test_constructor);

  // Test with only oposite privilege mode enabled, expect no matches //

  // Set up trigger
  tdata1_next = (6 << 28 | // TYPE = 6
                 1 << 12 | // ACTION = Enter debug mode
                 0 << 7  | // MATCH = EQ
                 1 << 6  | // M = Match in machine mode
                 1 << 3  | // U = Match in user mode
                 1 << 2 ); // EXECUTE = Match on instruction address

  if (priv_lvl == PRIV_LVL_MACHINE_MODE) {
    tdata1_next &= ~(1 << 6); // M = Don't match in machine mode
  } else if (priv_lvl == PRIV_LVL_USER_MODE){
    tdata1_next &= ~(1 << 3); // U = Don't match in user mode
  }

  // Check that executing trigger address does not trigger in wrong mode
  debug_break_loop = DEBUG_LOOPBREAK_DPCINCR;
  retval += trigger_test(1, 0, (uint32_t) &trigger_code_nop);

  tdata1_next |= 2 << 7; // Set MATCH = 2 (GEQ)
  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  // Executing from start of debug memory to avoid triggering on instructions executed in the the test flow (like debug handler)
  tdata2_next_offset = 0;
  retval += trigger_test(1, 0, (uint32_t) &execute_test_high_addr);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &execute_test_high_addr);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &execute_test_high_addr);

  execute_debug_command(DEBUG_SEL_DISABLE_TRIGGER);
  execute_debug_command(DEBUG_SEL_ENTER_MACHINEMODE);

  return retval;
}


/*
 * test_load_trigger
 *
 * Load trigger test
 *
 * Tests Load triggers with a range of configurations.
 *
 */
int test_load_trigger (int priv_lvl) {
  int retval = 0;

  if (priv_lvl == PRIV_LVL_USER_MODE) {
    printf("\n\n\n --- Testing load triggers (in user mode) ---\n\n");
    execute_debug_command(DEBUG_SEL_ENTER_USERMODE);

  } else if (priv_lvl == PRIV_LVL_MACHINE_MODE) {
    printf("\n\n\n --- Testing load triggers (in machine mode) ---\n\n");
    execute_debug_command(DEBUG_SEL_ENTER_MACHINEMODE);
  }

  // Set up trigger
  tdata1_next = (6 << 28 | // TYPE = 6
                 1 << 12 | // ACTION = Enter debug mode
                 0 << 7  | // MATCH = EQ
                 1 << 6  | // M = Match in machine mode
                 1 << 3  | // U = Match in user mode
                 1 << 0 ); // LOAD = Match on load from data address

  // Check with both machine and user mode

  trigger_type    = TRIGGER_LOAD_WORD;
  tdata2_next_offset = 0;

  debug_break_loop   = DEBUG_LOOPBREAK_TDATA2;
  retval += trigger_test(1, 1, (uint32_t) &some_data_word);

  debug_break_loop   = DEBUG_LOOPBREAK_DPCINCR;
  retval += trigger_test(1, 1, (uint32_t) &some_data_word);

  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);

  tdata2_next_offset = 0;

  trigger_type    = TRIGGER_LOAD_HALFWORD;
  retval += trigger_test(1, 1, (uint32_t) &some_data_halfwords[0]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_halfwords[1]);

  trigger_type    = TRIGGER_LOAD_BYTE;
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[0]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[1]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[2]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[3]);

  trigger_type    = TRIGGER_LOAD_WORD;


  tdata1_next |= 2 << 7; // Set MATCH = 2 (GEQ)
  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  // Loading from start of debug memory to avoid triggering on loads from other variables
  tdata2_next_offset = 0;
  retval += trigger_test(1, 1, (uint32_t) &load_store_test_high_addr);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 1, (uint32_t) &load_store_test_high_addr);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_high_addr);

  tdata1_next |=  3 << 7; // Set MATCH = 3 (LESS)
  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  // Loading from constructor function as it is known to have a lower address than other variables loaded in test code
  tdata2_next_offset = 0;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 1, (uint32_t) &load_store_test_constructor);


  // Trigger on current privilege mode only //

  // Set up trigger
  tdata1_next = (6 << 28 | // TYPE = 6
                 1 << 12 | // ACTION = Enter debug mode
                 0 << 7  | // MATCH = EQ
                 1 << 0 ); // LOAD = Match on load from data address

  if (priv_lvl == PRIV_LVL_MACHINE_MODE) {
    tdata1_next |= (1 << 6); // M = Match in machine mode
  } else if (priv_lvl == PRIV_LVL_USER_MODE){
    tdata1_next |= (1 << 3); // M = Match in user mode
  }

  trigger_type    = TRIGGER_LOAD_WORD;
  tdata2_next_offset = 0;

  debug_break_loop   = DEBUG_LOOPBREAK_TDATA2;
  retval += trigger_test(1, 1, (uint32_t) &some_data_word);

  debug_break_loop   = DEBUG_LOOPBREAK_DPCINCR;
  retval += trigger_test(1, 1, (uint32_t) &some_data_word);

  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);

  tdata2_next_offset = 0;

  trigger_type    = TRIGGER_LOAD_HALFWORD;
  retval += trigger_test(1, 1, (uint32_t) &some_data_halfwords[0]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_halfwords[1]);

  trigger_type    = TRIGGER_LOAD_BYTE;
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[0]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[1]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[2]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[3]);

  trigger_type    = TRIGGER_LOAD_WORD;


  tdata1_next |= 2 << 7; // Set MATCH = 2 (GEQ)

  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  // Loading from start of debug memory to avoid triggering on loads from other variables
  tdata2_next_offset = 0;
  retval += trigger_test(1, 1, (uint32_t) &load_store_test_high_addr);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 1, (uint32_t) &load_store_test_high_addr);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_high_addr);

  tdata1_next |=  3 << 7; // Set MATCH = 3 (LESS)
  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  // Loading from constructor function as it is known to have a lower address than other functions
  tdata2_next_offset = 0;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 1, (uint32_t) &load_store_test_constructor);


  // Test with only oposite privilege mode enabled, expect no matches
  tdata1_next = (6 << 28 | // TYPE = 6
                 1 << 12 | // ACTION = Enter debug mode
                 0 << 7  | // MATCH = EQ
                 1 << 6  | // M = Match in machine mode
                 1 << 3  | // U = Match in user mode
                 1 << 0 ); // LOAD = Match on load from data address


  if (priv_lvl == PRIV_LVL_MACHINE_MODE) {
    tdata1_next &= ~(1 << 6); // M = Don't match in machine mode
  } else if (priv_lvl == PRIV_LVL_USER_MODE){
    tdata1_next &= ~(1 << 3); // U = Don't match in user mode
  }

  trigger_type    = TRIGGER_LOAD_WORD;
  tdata2_next_offset = 0;

  debug_break_loop   = DEBUG_LOOPBREAK_TDATA2;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);

  debug_break_loop   = DEBUG_LOOPBREAK_DPCINCR;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);

  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);

  tdata2_next_offset = 0;

  trigger_type    = TRIGGER_LOAD_HALFWORD;
  retval += trigger_test(1, 0, (uint32_t) &some_data_halfwords[0]);
  retval += trigger_test(1, 0, (uint32_t) &some_data_halfwords[1]);

  trigger_type    = TRIGGER_LOAD_BYTE;
  retval += trigger_test(1, 0, (uint32_t) &some_data_bytes[0]);
  retval += trigger_test(1, 0, (uint32_t) &some_data_bytes[1]);
  retval += trigger_test(1, 0, (uint32_t) &some_data_bytes[2]);
  retval += trigger_test(1, 0, (uint32_t) &some_data_bytes[3]);

  trigger_type    = TRIGGER_LOAD_WORD;


  tdata1_next |= 2 << 7; // Set MATCH = 2 (GEQ)
  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  // Loading from start of debug memory to avoid triggering on loads from other variables
  tdata2_next_offset = 0;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_high_addr);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_high_addr);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_high_addr);

  tdata1_next |=  3 << 7; // Set MATCH = 3 (LESS)
  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  // Loading from constructor function as it is known to have a lower address than other functions
  tdata2_next_offset = 0;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);


  execute_debug_command(DEBUG_SEL_DISABLE_TRIGGER);
  execute_debug_command(DEBUG_SEL_ENTER_MACHINEMODE);

  return retval;
}


/*
 * test_store_trigger
 *
 * Store trigger test
 *
 * Tests store triggers for a range of configurations.
 *
 */
int test_store_trigger (int priv_lvl) {
  int retval = 0;

  if (priv_lvl == PRIV_LVL_USER_MODE) {
    printf("\n\n\n --- Testing store triggers (in user mode) ---\n\n");
    execute_debug_command(DEBUG_SEL_ENTER_USERMODE);

  } else if (priv_lvl == PRIV_LVL_MACHINE_MODE) {
    printf("\n\n\n --- Testing store triggers (in machine mode) ---\n\n");
    execute_debug_command(DEBUG_SEL_ENTER_MACHINEMODE);
  }

  // Set up trigger
  tdata1_next = (6 << 28 | // TYPE = 6
                 1 << 12 | // ACTION = Enter debug mode
                 0 << 7  | // MATCH = EQ
                 1 << 6  | // M = Match in machine mode
                 1 << 3  | // U = Match in user mode
                 1 << 1 ); // STORE = Match on store to data address

  trigger_type   = TRIGGER_STORE_WORD;
  tdata2_next_offset = 0;

  debug_break_loop   = DEBUG_LOOPBREAK_TDATA2;
  retval += trigger_test(1, 1, (uint32_t) &some_data_word);

  debug_break_loop   = DEBUG_LOOPBREAK_DPCINCR;
  retval += trigger_test(1, 1, (uint32_t) &some_data_word);

  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);

  tdata2_next_offset = 0;

  trigger_type    = TRIGGER_STORE_HALFWORD;
  retval += trigger_test(1, 1, (uint32_t) &some_data_halfwords[0]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_halfwords[1]);

  trigger_type    = TRIGGER_STORE_BYTE;
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[0]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[1]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[2]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[3]);

  trigger_type    = TRIGGER_STORE_WORD;

  tdata1_next |= 2 << 7; // Set MATCH = 2 (GEQ)

  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  // Storing to unsused debugger_exception section to ensure it is not triggered by variables at higher addresses
  tdata2_next_offset = 0;
  retval += trigger_test(1, 1, (uint32_t) &load_store_test_high_addr);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 1, (uint32_t) &load_store_test_high_addr);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_high_addr);

  tdata1_next |=  3 << 7; // Set MATCH = 3 (LESS)
  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  tdata2_next_offset = 0;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 1, (uint32_t) &load_store_test_constructor);


  // Trigger on current privilege mode only //

  // Set up trigger
  tdata1_next = (6 << 28 | // TYPE = 6
                 1 << 12 | // ACTION = Enter debug mode
                 0 << 7  | // MATCH = EQ
                 1 << 1 ); // STORE = Match on store to data address

  if (priv_lvl == PRIV_LVL_MACHINE_MODE) {
    tdata1_next |= (1 << 6); // M = Match in machine mode
  } else if (priv_lvl == PRIV_LVL_USER_MODE){
    tdata1_next |= (1 << 3); // M = Match in user mode
  }

  trigger_type   = TRIGGER_STORE_WORD;
  tdata2_next_offset = 0;

  debug_break_loop   = DEBUG_LOOPBREAK_TDATA2;
  retval += trigger_test(1, 1, (uint32_t) &some_data_word);

  debug_break_loop   = DEBUG_LOOPBREAK_DPCINCR;
  retval += trigger_test(1, 1, (uint32_t) &some_data_word);

  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);

  tdata2_next_offset = 0;

  trigger_type    = TRIGGER_STORE_HALFWORD;
  retval += trigger_test(1, 1, (uint32_t) &some_data_halfwords[0]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_halfwords[1]);

  trigger_type    = TRIGGER_STORE_BYTE;
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[0]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[1]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[2]);
  retval += trigger_test(1, 1, (uint32_t) &some_data_bytes[3]);

  trigger_type    = TRIGGER_STORE_WORD;

  tdata1_next |= 2 << 7; // Set MATCH = 2 (GEQ)

  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  // Storing to unsused debugger_exception section to ensure it is not triggered by variables at higher addresses
  tdata2_next_offset = 0;
  retval += trigger_test(1, 1, (uint32_t) &load_store_test_high_addr);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 1, (uint32_t) &load_store_test_high_addr);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_high_addr);

  tdata1_next |=  3 << 7; // Set MATCH = 3 (LESS)
  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  tdata2_next_offset = 0;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 1, (uint32_t) &load_store_test_constructor);


  // Test with only oposite privilege mode enabled, expect no matches
  tdata1_next = (6 << 28 | // TYPE = 6
                 1 << 12 | // ACTION = Enter debug mode
                 0 << 7  | // MATCH = EQ
                 1 << 6  | // M = Match in machine mode
                 1 << 3  | // U = Match in user mode
                 1 << 1 ); // STORE = Match on store to data address

  if (priv_lvl == PRIV_LVL_MACHINE_MODE) {
    tdata1_next &= ~(1 << 6); // M = Don't match in machine mode
  } else if (priv_lvl == PRIV_LVL_USER_MODE){
    tdata1_next &= ~(1 << 3); // U = Don't match in user mode
  }

  trigger_type   = TRIGGER_STORE_WORD;
  tdata2_next_offset = 0;

  debug_break_loop   = DEBUG_LOOPBREAK_TDATA2;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);

  debug_break_loop   = DEBUG_LOOPBREAK_DPCINCR;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);

  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &some_data_word);

  tdata2_next_offset = 0;

  trigger_type    = TRIGGER_STORE_HALFWORD;
  retval += trigger_test(1, 0, (uint32_t) &some_data_halfwords[0]);
  retval += trigger_test(1, 0, (uint32_t) &some_data_halfwords[1]);

  trigger_type    = TRIGGER_STORE_BYTE;
  retval += trigger_test(1, 0, (uint32_t) &some_data_bytes[0]);
  retval += trigger_test(1, 0, (uint32_t) &some_data_bytes[1]);
  retval += trigger_test(1, 0, (uint32_t) &some_data_bytes[2]);
  retval += trigger_test(1, 0, (uint32_t) &some_data_bytes[3]);

  trigger_type    = TRIGGER_STORE_WORD;

  tdata1_next |= 2 << 7; // Set MATCH = 2 (GEQ)

  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  // Storing to unsused debugger_exception section to ensure it is not triggered by variables at higher addresses
  tdata2_next_offset = 0;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_high_addr);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_high_addr);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_high_addr);

  tdata1_next |=  3 << 7; // Set MATCH = 3 (LESS)
  debug_break_loop =   DEBUG_LOOPBREAK_TDATA1;

  tdata2_next_offset = 0;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);
  tdata2_next_offset = -4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);
  tdata2_next_offset = 4;
  retval += trigger_test(1, 0, (uint32_t) &load_store_test_constructor);

  execute_debug_command(DEBUG_SEL_DISABLE_TRIGGER);
  execute_debug_command(DEBUG_SEL_ENTER_MACHINEMODE);

  return retval;
}

/*
 * test_exception_trigger
 *
 * Exception trigger test
 *
 * Tests Exception triggers with a range of configurations
 *
 */
int test_exception_trigger (int priv_lvl) {
  int retval = 0;

  if (priv_lvl == PRIV_LVL_USER_MODE) {
    printf("\n\n\n --- Testing Exception triggers (in user mode) ---\n\n");
    execute_debug_command(DEBUG_SEL_ENTER_USERMODE);

  } else if (priv_lvl == PRIV_LVL_MACHINE_MODE) {
    printf("\n\n\n --- Testing Exception triggers (in machine mode) ---\n\n");
    execute_debug_command(DEBUG_SEL_ENTER_MACHINEMODE);
  }

  // Set up trigger
  tdata1_next = (5 << 28 | // TYPE = etrigger
                 1 <<  9 | // M = Match in machine mode
                 1 <<  6); // U = Match in user mode

  tdata2_next_offset = 0;
  trigger_type = TRIGGER_EXCEPTION_ILLEGAL;
  retval += trigger_test(1, 0, 0);
  retval += trigger_test(1, 1, -1);
  retval += trigger_test(1, 1,((1 << EXCEPTION_CODE_ILLEGAL_INSTRUCTION) |
                               (1 << EXCEPTION_CODE_BREAKPOINT) |
                               (1 << EXCEPTION_CODE_RESERVED)));
  retval += trigger_test(1, 0, (1 << EXCEPTION_CODE_RESERVED));
  retval += trigger_test(1, 0, (1 << EXCEPTION_CODE_BREAKPOINT));
  retval += trigger_test(1, 1, (1 << EXCEPTION_CODE_ILLEGAL_INSTRUCTION));

  trigger_type = TRIGGER_EXCEPTION_EBREAK;
  retval += trigger_test(1, 0, 0);
  retval += trigger_test(1, 1, -1);
  retval += trigger_test(1, 0,((1 << EXCEPTION_CODE_ILLEGAL_INSTRUCTION) |
                               (1 << EXCEPTION_CODE_RESERVED)));
  retval += trigger_test(1, 1, (1 << EXCEPTION_CODE_BREAKPOINT));
  retval += trigger_test(1, 1,((1 << EXCEPTION_CODE_ILLEGAL_INSTRUCTION) |
                               (1 << EXCEPTION_CODE_BREAKPOINT)));
  retval += trigger_test(1, 0, 0);


  // Set up trigger
  tdata1_next = (5 << 28); // TYPE = etrigger

  if (priv_lvl == PRIV_LVL_MACHINE_MODE) {
    tdata1_next |= (1 << 9); // M = Match in machine mode
  } else if (priv_lvl == PRIV_LVL_USER_MODE){
    tdata1_next |= (1 << 6); // M = Match in user mode
  }

  tdata2_next_offset = 0;
  trigger_type = TRIGGER_EXCEPTION_ILLEGAL;
  retval += trigger_test(1, 0, 0);
  retval += trigger_test(1, 1, -1);
  retval += trigger_test(1, 1,((1 << EXCEPTION_CODE_ILLEGAL_INSTRUCTION) |
                               (1 << EXCEPTION_CODE_BREAKPOINT) |
                               (1 << EXCEPTION_CODE_RESERVED)));
  retval += trigger_test(1, 0, (1 << EXCEPTION_CODE_RESERVED));
  retval += trigger_test(1, 0, (1 << EXCEPTION_CODE_BREAKPOINT));
  retval += trigger_test(1, 1, (1 << EXCEPTION_CODE_ILLEGAL_INSTRUCTION));

  trigger_type = TRIGGER_EXCEPTION_EBREAK;
  retval += trigger_test(1, 0, 0);
  retval += trigger_test(1, 1, -1);
  retval += trigger_test(1, 0,((1 << EXCEPTION_CODE_ILLEGAL_INSTRUCTION) |
                               (1 << EXCEPTION_CODE_RESERVED)));
  retval += trigger_test(1, 1, (1 << EXCEPTION_CODE_BREAKPOINT));
  retval += trigger_test(1, 1,((1 << EXCEPTION_CODE_ILLEGAL_INSTRUCTION) |
                               (1 << EXCEPTION_CODE_BREAKPOINT)));
  retval += trigger_test(1, 0, 0);

  // Set up trigger
  tdata1_next = (5 << 28 | // TYPE = etrigger
                 1 <<  9 | // M = Match in machine mode
                 1 <<  6); // U = Match in user mode

  if (priv_lvl == PRIV_LVL_MACHINE_MODE) {
    tdata1_next &= ~(1 << 9); // M = Don't match in machine mode
  } else if (priv_lvl == PRIV_LVL_USER_MODE){
    tdata1_next &= ~(1 << 6); // U = Don't match in user mode
  }

  tdata2_next_offset = 0;
  trigger_type = TRIGGER_EXCEPTION_ILLEGAL;
  retval += trigger_test(1, 0, 0);
  retval += trigger_test(1, 0, -1);
  retval += trigger_test(1, 0,((1 << EXCEPTION_CODE_ILLEGAL_INSTRUCTION) |
                               (1 << EXCEPTION_CODE_BREAKPOINT) |
                               (1 << EXCEPTION_CODE_RESERVED)));
  retval += trigger_test(1, 0, (1 << EXCEPTION_CODE_RESERVED));
  retval += trigger_test(1, 0, (1 << EXCEPTION_CODE_BREAKPOINT));
  retval += trigger_test(1, 0, (1 << EXCEPTION_CODE_ILLEGAL_INSTRUCTION));

  trigger_type = TRIGGER_EXCEPTION_EBREAK;
  retval += trigger_test(1, 0, 0);
  retval += trigger_test(1, 0, -1);
  retval += trigger_test(1, 0,((1 << EXCEPTION_CODE_ILLEGAL_INSTRUCTION) |
                               (1 << EXCEPTION_CODE_RESERVED)));
  retval += trigger_test(1, 0, (1 << EXCEPTION_CODE_BREAKPOINT));
  retval += trigger_test(1, 0,((1 << EXCEPTION_CODE_ILLEGAL_INSTRUCTION) |
                               (1 << EXCEPTION_CODE_BREAKPOINT)));
  retval += trigger_test(1, 0, 0);


  execute_debug_command(DEBUG_SEL_DISABLE_TRIGGER);
  execute_debug_command(DEBUG_SEL_ENTER_MACHINEMODE);

  return retval;
}

/*
 * _debug_mode_register_test
 *
 * Debug mode register access test
 *
 * Checks that registers are implemented according to spec for debug mode
 *
 */
void _debug_mode_register_test(void) {
  printf("    _debug_mode_register_test():\n");

  // TDATA1 - Check reset value
  __asm__ volatile (R"(csrr  s0,     tdata1
                           li    s1,     0x28001000
                           beq   s0,     s1, 1f
                           li    s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                           sw    s1,     debug_entry_status, s2
                         1:nop
                           )" ::: "s0", "s1");

  // TDATA1 (Type==6) - Write 1s
  tdata1_next = (6 << 28) | ~(0xF << 28); // TYPE = Address match
  __asm__ volatile (R"(la   s1,     tdata1_next
                           lw   s0,     0(s1)
                           csrw tdata1, s0
                           csrr s1,     tdata1
                           li   s0,     0x6800104F
                           beq  s0,     s1,  1f
                           li   s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                           sw   s1,     debug_entry_status, s2
                         1:nop
                           )" ::: "s0", "s1");

  // TDATA1 (Type==6) - Write 0s
  tdata1_next = (6 << 28); // TYPE = Address match
  __asm__ volatile (R"(la   s1,     tdata1_next
                           lw   s0,     0(s1)
                           csrw tdata1, s0
                           csrr s1,     tdata1
                           li   s0,     0x68001000
                           beq  s0,     s1,  1f
                           li   s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                           sw   s1,     debug_entry_status, s2
                         1:nop
                           )" ::: "s0", "s1");

  // TDATA2 (Type==6) - Address match - Write 1s
  __asm__ volatile (R"(li   s1,     0xFFFFFFFF
                           csrw tdata2, s1
                           csrr s0,     tdata2
                           beq  s0,     s1,  1f
                           li    s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                           sw    s1,     debug_entry_status, s2
                         1:nop
                           )" ::: "s0", "s1");

  // TDATA2 (Type==6) - Address match - Write 0s
  __asm__ volatile (R"(csrwi tdata2, 0x0
                           csrr  s0,     tdata2
                           beqz  s0,     1f
                           li    s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                           sw    s1,     debug_entry_status, s2
                         1:nop
                           )" ::: "s0", "s1");

  // TDATA1 (Type==2) - Write 1s
  tdata1_next = (2 << 28) | ~(0xF << 28); // TYPE = Address match
  __asm__ volatile (R"(la   s1,     tdata1_next
                       lw   s0,     0(s1)
                       csrw tdata1, s0
                       csrr s1,     tdata1
                       li   s0,     0x2800104F
                       beq  s0,     s1,  1f
                       li   s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw   s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");

  // TDATA1 (Type==2) - Write 0s
  tdata1_next = (2 << 28); // TYPE = Address match
  __asm__ volatile (R"(la   s1,     tdata1_next
                       lw   s0,     0(s1)
                       csrw tdata1, s0
                       csrr s1,     tdata1
                       li   s0,     0x28001000
                       beq  s0,     s1,  1f
                       li   s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw   s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");


  // TDATA2 (Type==2) - Legacy Address match - Write 1s
  __asm__ volatile (R"(li   s1,     0xFFFFFFFF
                       csrw tdata2, s1
                       csrr s0,     tdata2
                       beq  s0,     s1,  1f
                       li   s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw   s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");

  // TDATA2 (Type==2) - Legacy Address match - Write 0s
  __asm__ volatile (R"(csrwi tdata2, 0x0
                       csrr  s0,     tdata2
                       beqz  s0,     1f
                       li    s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw    s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");

  // TDATA1 (Type==5) - Exception Trigger - Write when tdata2 is illegal
  tdata1_next = (5 << 28) | ~(0xF << 28); // TYPE = Exception Trigger
  __asm__ volatile (R"(csrwi tdata1, 0x0
                       li   s1,     0xFFFFFFFF
                       csrw tdata2, s1
                       la   s1,     tdata1_next
                       lw   s0,     0(s1)
                       csrw tdata1, s0
                       csrr s1,     tdata1
                       li   s0,     0xF8000000
                       beq  s0,     s1,  1f
                       li   s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw   s1,     debug_entry_status, s2
                     1:csrwi tdata2, 0x0
                       )" ::: "s0", "s1");

  // TDATA1 (Type==5) - Exception Trigger - Write 1s
  tdata1_next = (5 << 28) | ~(0xF << 28); // TYPE = Exception Trigger
  __asm__ volatile (R"(la   s1,     tdata1_next
                       lw   s0,     0(s1)
                       csrw tdata1, s0
                       csrr s1,     tdata1
                       li   s0,     0x58000241
                       beq  s0,     s1,  1f
                       li   s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw   s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");

  // TDATA1 (Type==5) - Exception Trigger - Write 0s
  tdata1_next = (5 << 28); // TYPE = Exception Trigger
  __asm__ volatile (R"(la   s1,     tdata1_next
                       lw   s0,     0(s1)
                       csrw tdata1, s0
                       csrr s1,     tdata1
                       li   s0,     0x58000001
                       beq  s0,     s1,  1f
                       li   s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw   s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");


  // TDATA2 (Type==5) - Exception Trigger - Write 1s
  __asm__ volatile (R"(li   s1,     0xFFFFFFFF
                       csrw tdata2, s1
                       csrr s0,     tdata2
                       li   s1,     0x030009AE
                       beq  s0,     s1,  1f
                       li   s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw   s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");

  // TDATA2 (Type==5) - Exception Trigger  - Write 0s
  __asm__ volatile (R"(csrwi tdata2, 0x0
                       csrr  s0,     tdata2
                       beqz  s0,     2f
                     1:li    s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw    s1,     debug_entry_status, s2
                     2:nop
                       )" ::: "s0", "s1");
  // TDATA1 - Write 0s
  __asm__ volatile (R"(csrwi tdata1, 0x0
                       csrr  s0,     tdata1
                       li    s1,     0xF8000000
                       beq   s0,     s1, 1f
                       li    s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw    s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");

  // TDATA1 - Write 1s
  __asm__ volatile (R"(li    s0,     0xFFFFFFFF
                       csrw  tdata1, s0
                       csrr  s1,     tdata1
                       li    s0,     0xF8000000
                       beq   s0,     s1,  1f
                       li    s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw    s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");


  // TDATA2 (Disabled) - Write 1s
  __asm__ volatile (R"(li    s0,     0xFFFFFFFF
                       csrw  tdata2, s0
                       csrr  s1,     tdata2
                       beq   s0,     s1,  1f
                       li    s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw    s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");

  // TDATA2 (Disabled) - Write 0s
  __asm__ volatile (R"(csrwi tdata2, 0x0
                       csrr  s0,     tdata2
                       beqz  s0,     1f
                       li    s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw    s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");

  // TDATA3 - Write 1s
  __asm__ volatile (R"(li    s0,     0xFFFFFFFF
                       csrw  tdata3, s0
                       csrr  s1,     tdata3
                       beqz  s1,     1f
                       li    s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw    s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");

  // TINFO - Write 1s, Debug Access test
  __asm__ volatile (R"(li    s1,     0xFFFFFFFF
                       csrw  tinfo,  s1
                       csrr  s0,     tinfo
                       li    s1,     0x8064
                       beq   s0,     s1,  1f
                       li    s1,     0x2   #DEBUG_STATUS_ENTERED_FAIL
                       sw    s1,     debug_entry_status, s2
                     1:nop
                       )" ::: "s0", "s1");

  if  (debug_entry_status == DEBUG_STATUS_ENTERED_FAIL) {
    printf("Debug Mode Register test FAILED\n\n");
  }
  return;
}

/*
 * test_register_access
 *
 * Register access test
 *
 * Checks that registers are implemented according to spec for machine mode and user mode
 *
 */
int test_register_access(void) {

  printf("\n\n\n --- Testing register access ---\n\n");

#ifdef DEBUG_PRINT
  printf("  Checking register access from debug mode\n");
#endif
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

#ifdef DEBUG_PRINT
  printf("\n  Checking register access from Machine mode\n");
#endif

  // TDATA1 - Write valid value (in m-mode), check that is ignored
  __asm__ volatile (R"(li    s1,     0x60000000
                       csrw  tdata1, s1
                       csrr  s0,     tdata1
                       li    s1,     0xF8000000
                       beq   s0,     s1, 1f
                       li    a0,     0x1   #FAIL
                       ret
                     1:nop
                       )" ::: "s0", "s1");

  // TDATA2 - Write valid value (in m-mode), check that is ignored
  __asm__ volatile (R"(li    s1,     0xFFFFFFFF
                       csrw  tdata2, s1
                       csrr  s0,     tdata2
                       beqz  s0,     1f
                       li    a0,     0x1   #FAIL
                       ret
                     1:nop
                       )" ::: "s0", "s1");

  // TINFO - Write 0s, machine mode access test
  __asm__ volatile (R"(li    s1,     0x0
                       csrw  tinfo,  s1
                       csrr  s0,     tinfo
                       li    s1,     0x8064
                       beq   s0,     s1,  1f
                       li    a0,     0x1   #FAIL
                       ret
                     1:nop
                       )" ::: "s0", "s1");

  // TCONTROL - Write 1s
  __asm__ volatile (R"(li    s1,     0xFFFFFFFF
                       csrw  tcontrol,  s1
                       csrr  s0,     tcontrol
                       beqz  s0,     1f
                       li    a0,     0x1   #FAIL
                       ret
                     1:nop
                       )" ::: "s0", "s1");
  // TDATA1 - Write valid value (in m-mode), check that is ignored
  __asm__ volatile (R"(li    s1,     0x60000000
                       csrw  tdata1, s1
                       csrr  s0,     tdata1
                       li    s1,     0xF8000000
                       beq   s0,     s1, 1f
                       li    a0,     0x1   #FAIL
                       ret
                     1:nop
                       )" ::: "s0", "s1");

  // TDATA2 - Write valid value (in m-mode), check that is ignored
  __asm__ volatile (R"(li    s1,     0xFFFFFFFF
                       csrw  tdata2, s1
                       csrr  s0,     tdata2
                       beqz  s0,     1f
                       li    a0,     0x1   #FAIL
                       ret
                     1:nop
                       )" ::: "s0", "s1");

  // TINFO - Write 0s, machine mode access test
  __asm__ volatile (R"(li    s1,     0x0
                       csrw  tinfo,  s1
                       csrr  s0,     tinfo
                       li    s1,     0x8064
                       beq   s0,     s1,  1f
                       li    a0,     0x1   #FAIL
                       ret
                     1:nop
                       )" ::: "s0", "s1");

  // TCONTROL - Write 1s
  __asm__ volatile (R"(li    s1,     0xFFFFFFFF
                       csrw  tcontrol,  s1
                       csrr  s0,     tcontrol
                       beqz  s0,     1f
                       li    a0,     0x1   #FAIL
                       ret
                     1:nop
                       )" ::: "s0", "s1");

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
  // Allow user mode access to full memory map
  __asm__ volatile (R"(li    t0, 0xFFFFFFFF
                       csrw  pmpaddr0, t0
                       csrwi pmpcfg0, ((1 << 3) | (7 << 0))
                       )" ::: "t0");
}

/*
 * get_num_triggers
 *
 * Get number of triggers
 *
 * Determine number of triggers implemented by probing tselect
 *
 */
uint32_t get_num_triggers() {
  illegal_insn_status = 0;
  __asm__ volatile ("csrwi tselect, 0x0");

  if (illegal_insn_status) {
    num_triggers = 0;
  } else {
    __asm__ volatile (R"(
      csrwi tselect, 0x1
      csrwi tselect, 0x2
      csrwi tselect, 0x3
      csrr s2, tselect
      la   s3, num_triggers
      sw   s2, 0(s3)

      csrwi tselect, 0x0
    )" ::: "s2", "s3");

    num_triggers++;
  }

  printf ("NUM_TRIGGERS = %ld\n", num_triggers);

  return num_triggers;
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
  num_triggers = get_num_triggers();

  if (num_triggers > 0) {
    for (int i = 0; i < num_triggers; i++) {

      trigger_sel = i;
      printf ("csr_write: tselect = %ld\n", trigger_sel);
      __asm__ volatile (R"(lw        s2, trigger_sel
                           csrw tselect, s2         )" ::: "s2");

      if (test_register_access()) {
        printf("Register access test failed\n");
        return FAIL;
      }
      if (test_execute_trigger(PRIV_LVL_MACHINE_MODE)) {
        printf("Execute trigger test (machine mode) failed\n");
        return FAIL;
      }
      if (test_execute_trigger(PRIV_LVL_USER_MODE)) {
        printf("Execute trigger test (user mode) failed\n");
        return FAIL;
      }
      if (test_load_trigger(PRIV_LVL_MACHINE_MODE)) {
        printf("Load trigger test (machine mode) failed\n");
        return FAIL;
      }
      if (test_load_trigger(PRIV_LVL_USER_MODE)) {
        printf("Load trigger (user mode) test failed\n");
        return FAIL;
      }
      if (test_store_trigger(PRIV_LVL_MACHINE_MODE)) {
        printf("Store trigger test (machine mode) failed\n");
        return FAIL;
      }
      if (test_store_trigger(PRIV_LVL_USER_MODE)) {
        printf("Store trigger (user mode) test failed\n");
        return FAIL;
      }
      if (test_exception_trigger(PRIV_LVL_MACHINE_MODE)) {
        printf("Exception trigger test (machine mode) failed\n");
        return FAIL;
      }
      if (test_exception_trigger(PRIV_LVL_USER_MODE)) {
        printf("Exception trigger (user mode) test failed\n");
        return FAIL;
      }
    }
    printf("Finished \n");
    return SUCCESS;
  } else {
    printf("Error: Tselect register does not exist (NUM_TRIGGERS=0 not supported in this test) \n");
    return FAIL;
  }
}

