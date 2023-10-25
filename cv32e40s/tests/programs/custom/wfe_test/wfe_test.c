//
// Copyright 2022 Silicon Labs, Inc.
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
///////////////////////////////////////////////////////////////////////////////
//
// Author: Henrik Fegran
//
// WFE directed test
// Also includes test for wfi + mstatus.tw = 1 => illegal instruction in U-mode
//
/////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>
#include <assert.h>
#include "bsp.h"
#include "corev_uvmt.h"

// MUST be 31 or less (bit position-1 in result array determines test pass/fail
// status, thus we are limited to 31 tests with this construct.
#define NUM_TESTS 3
// Set which test index to start testing at (for quickly running specific tests during development)
#define START_TEST_IDX 0

#define WFE_INSTR 0x8c000073

#define MARCHID_CV32E40X 0x14
#define MARCHID_CV32E40S 0x15

// __FUNCTION__ is C99 and newer, -Wpedantic flags a warning that
// this is not ISO C, thus we wrap this instatiation in a macro
// ignoring this GCC warning to avoid a long list of warnings during
// compilation.
#define SET_FUNC_INFO \
  _Pragma("GCC diagnostic push") \
  _Pragma("GCC diagnostic ignored \"-Wpedantic\"") \
  const volatile char * const volatile name = __FUNCTION__; \
  _Pragma("GCC diagnostic pop")

// ---------------------------------------------------------------
// Convenience macros for bit fields
// ---------------------------------------------------------------

// ---------------------------------------------------------------
// Global variables
// ---------------------------------------------------------------
// Print verbosity, consider implementing this as a virtual
// peripheral setting to be controlled from UVM.
volatile verbosity_t global_verbosity = V_LOW;

volatile uint32_t * volatile g_illegal_instr_exp;
// ---------------------------------------------------------------
// Test prototypes - should match
// uint32_t <name>(uint32_t index, uint8_t report_name)
//
// Use template below for implementation
// ---------------------------------------------------------------
uint32_t wfe_wakeup(uint32_t index, uint8_t report_name);
uint32_t wfe_wakeup_umode(uint32_t index, uint8_t report_name);
uint32_t wfi_mstatus_tw_umode_illegal(uint32_t index, uint8_t report_name);

// ---------------------------------------------------------------
// Generic test template:
// ---------------------------------------------------------------
// uint32_t <test_name>(uint32_t index, uint8_t report_name){
//   volatile uint8_t test_fail = 0;
//   /* Test variable instantiation */
//
//   SET_FUNC_INFO
//
//   if (report_name) {
//     cvprintf(V_LOW, "\"%s\"", name);
//     return 0;
//   }
//
//   /* Insert test code here /*
//
//   if (test_fail) {
//     cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
//     return index + 1;
//   }
//   cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
//   return 0;
// }
// ---------------------------------------------------------------

// ---------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------
/*
 * set_test_status
 *
 * Sets the pass/fail criteria for a given tests and updates
 * the 32bit test status variable.
 *
 * - test_no: current test index
 * - val_prev: status vector variable, holding previous test results
 */
uint32_t set_test_status(uint32_t test_no, uint32_t val_prev);

/*
 * get_result
 *
 * Reports result of self checking tests
 *
 * - res: result-vector from previously run tests
 * - ptr: Pointer to test functions, this is intended to be
 *        invoked with "report_name == 1" here, as that will
 *        only print the name of the test and not actually
 *        run it.
 */
int get_result(uint32_t res, uint32_t (* volatile ptr[])(uint32_t, uint8_t));

/*
 * cvprintf
 *
 * verbosity controlled printf
 * use as printf, but with an added verbosity-level setting
 *
 */
int cvprintf(verbosity_t verbosity, const char *format, ...);

/*
 * set_mseccfg
 *
 * Sets up mseccfg with the provided
 * mseccfg_t object
 */
void set_mseccfg(mseccfg_t mseccfg);

/*
 * set_pmpcfg
 *
 * Sets up pmp configuration for a given region
 * (defined in pmpcfg_t object)
 */
void set_pmpcfg(pmpsubcfg_t pmpsubcfg, uint32_t reg_no);

/*
 * increment_mepc
 *
 * Increments mepc,
 * incr_val 0 = auto detect
 *          2 = halfword
 *          4 = word
 */
void increment_mepc(volatile uint32_t incr_val);

/*
 * has_pmp_configured
 *
 * Returns 1 if pmp is enabled/supported else returns 0
 */
uint32_t has_pmp_configured(void);

/*
 * Non-standard illegal instruction and ecall handlers
 */
void handle_illegal_insn(void);
void handle_ecall(void);
void handle_ecall_u(void);

// ---------------------------------------------------------------
// Test entry point
// ---------------------------------------------------------------
int main(int argc, char **argv){

  volatile uint32_t (* volatile tests[NUM_TESTS])(volatile uint32_t, volatile uint8_t);

  volatile uint32_t test_res = 0x1;
  volatile int      retval   = 0;

  g_illegal_instr_exp = calloc(1, sizeof(uint32_t));

  // Add function pointers to new tests here
  tests[0]  = wfe_wakeup;
  tests[1]  = wfe_wakeup_umode;
  tests[2]  = wfi_mstatus_tw_umode_illegal;

  // Run all tests in list above
  cvprintf(V_LOW, "\nWFE Test start\n\n");
  for (volatile int i = START_TEST_IDX; i < NUM_TESTS; i++) {
    test_res = set_test_status(tests[i](i, (volatile uint32_t)(0)), test_res);
  }

  // Report failures
  retval = get_result(test_res, tests);

  free((void *)g_illegal_instr_exp            );
  return retval; // Nonzero for failing tests
}

// -----------------------------------------------------------------------------

int cvprintf(volatile verbosity_t verbosity, const char * volatile format, ...){
  va_list args;
  volatile int retval = 0;

  va_start(args, format);

  if (verbosity <= global_verbosity){
    retval = vprintf(format, args);
  }
  va_end(args);
  return retval;
}

// -----------------------------------------------------------------------------

uint32_t set_test_status(uint32_t test_no, uint32_t val_prev){
  volatile uint32_t res;
  res = val_prev | (1 << test_no);
  return res;
}

// -----------------------------------------------------------------------------

int get_result(uint32_t res, uint32_t (* volatile ptr[])(uint32_t, uint8_t)){
  cvprintf(V_LOW, "=========================\n");
  cvprintf(V_LOW, "=        SUMMARY        =\n");
  cvprintf(V_LOW, "=========================\n");
  for (int i = START_TEST_IDX; i < NUM_TESTS; i++){
    if ((res >> (i+1)) & 0x1) {
      cvprintf (V_LOW, "Test %0d FAIL: ", i);
      (void)ptr[i](i, 1);
      cvprintf (V_LOW, "\n");
    } else {
      cvprintf (V_LOW, "Test %0d PASS: ", i);
      (void)ptr[i](i, 1);
      cvprintf (V_LOW, "\n");
    }
  }
  if (res == 1) {
    cvprintf(V_LOW, "\n\tALL SELF CHECKS PASS!\n\n");
    return 0;
  } else {
    cvprintf(V_LOW, "\n\tSELF CHECK FAILURES OCCURRED!\n\n");
    return res;
  }
}

// -----------------------------------------------------------------------------

uint32_t has_pmp_configured(void) {
  volatile uint32_t pmpaddr0 = 0xffffffff;
  volatile uint32_t pmpaddr0_backup = 0;
  volatile uint32_t marchid = 0x0;

  __asm__ volatile (R"(
    csrrs %[marchid], marchid, zero
  )":[marchid] "=r"(marchid));

  // CV32E40X does not support PMP, skip
  switch (marchid) {
    case (MARCHID_CV32E40X):
      return 0;
      break;
    case (MARCHID_CV32E40S):
      ;; // Do nothing and continue execution
      break;
  }

  __asm__ volatile (R"(
    csrrw %[pmpaddr0_backup] , pmpaddr0, %[pmpaddr0]
    csrrw %[pmpaddr0], pmpaddr0, %[pmpaddr0_backup]
  )" :[pmpaddr0_backup] "+r"(pmpaddr0_backup),
      [pmpaddr0]        "+r"(pmpaddr0));

  return (pmpaddr0 != 0);
}

// -----------------------------------------------------------------------------

void set_mseccfg(mseccfg_t mseccfg){

  __asm__ volatile ( R"(
    csrrs x0, mseccfg, %[cfg_vec]
  )"
      :
      : [cfg_vec] "r"(mseccfg.raw)
      :);

  cvprintf(V_DEBUG, "Wrote mseccfg: 0x%08lx\n", mseccfg.raw);
}

// -----------------------------------------------------------------------------

void set_pmpcfg(pmpsubcfg_t pmpsubcfg, uint32_t reg_no){
  volatile pmpcfg_t temp   = { 0 };
  volatile pmpcfg_t pmpcfg = { 0 };

  pmpcfg.reg_idx[reg_no % 4].cfg = pmpsubcfg.raw;

  temp.reg_idx[reg_no % 4].cfg = 0xff;

  switch (reg_no / 4) {
    case 0:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg0, t0
        csrrs zero, pmpcfg0, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 1:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg1, t0
        csrrs zero, pmpcfg1, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 2:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg2, t0
        csrrs zero, pmpcfg2, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 3:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg3, t0
        csrrs zero, pmpcfg3, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 4:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg4, t0
        csrrs zero, pmpcfg4, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    case 5:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg5, t0
        csrrs zero, pmpcfg5, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 6:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg6, t0
        csrrs zero, pmpcfg6, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 7:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg7, t0
        csrrs zero, pmpcfg7, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 8:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg8, t0
        csrrs zero, pmpcfg8, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 9:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg9, t0
        csrrs zero, pmpcfg9, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 10:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg10, t0
        csrrs zero, pmpcfg10, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 11:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg11, t0
        csrrs zero, pmpcfg11, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 12:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg12, t0
        csrrs zero, pmpcfg12, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 13:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg13, t0
        csrrs zero, pmpcfg13, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 14:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg14, t0
        csrrs zero, pmpcfg14, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
    case 15:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg15, t0
        csrrs zero, pmpcfg15, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg.raw)
          : [tmp] "r"(temp.raw)
          : "t0"
          );
    break;
  }

  cvprintf(V_DEBUG, "Set pmpcfg_vector: 0x%08lx\n", pmpcfg.raw);
  return;
}

// -----------------------------------------------------------------------------

void increment_mepc(volatile uint32_t incr_val) {
  volatile uint32_t mepc = 0;

  __asm__ volatile ( R"(
    csrrs %[mepc], mepc, zero
  )" : [mepc] "=r"(mepc));

  if (incr_val == 0) {
    // No increment specified, check *mepc instruction
    if (((*(uint32_t *)mepc) & 0x3UL) == 0x3UL) {
      // non-compressed
      mepc += 4;
    } else {
      // compressed
      mepc += 2;
    }
  } else {
    // explicitly requested increment
    mepc += incr_val;
  }

  __asm__ volatile ( R"(
    csrrw zero, mepc, %[mepc]
  )" :: [mepc] "r"(mepc));
}

// -----------------------------------------------------------------------------

void __attribute__((naked)) handle_ecall(void){
  __asm__ volatile ( R"(
    j handle_ecall_u
  )");
}

// -----------------------------------------------------------------------------

void __attribute__((naked)) handle_ecall_u(void){
  __asm__ volatile ( R"(
    ## handle_ecall_u swaps privilege level,
    ## if in M-mode -> mret to U
    ## else U-mode -> mret to M

    addi sp, sp, -12
    sw   a0, 0(sp)
    sw   a1, 4(sp)
    sw   a2, 8(sp)

    # Get current priv-mode
    csrrs a2, mstatus, zero

    # clear out non-mpp bits and set up a2 to update mpp
    lui a1, 2
    addi a1, a1, -2048
    and a2, a2, a1

    # check if we trapped from U or M-mode
    beq a1, a2, 1f
    j 2f

    # mpp = M-mode -> U-mode
    1:
    csrrc zero, mstatus, a1
    j 3f

    # mpp = U-mode -> M-mode
    2:
    csrrs zero, mstatus, a1

    3:
    # Set 0 as argument for increment_mepc
    addi a0, zero, 0
    call increment_mepc

    lw   a2, 8(sp)
    lw   a1, 4(sp)
    lw   a0, 0(sp)
    addi sp, sp, 12

    # return to regular bsp handler flow
    j end_handler_ret

  )");
}

// -----------------------------------------------------------------------------

void __attribute__((naked)) handle_illegal_insn(void) {
  __asm__ volatile ( R"(
    addi sp, sp, -8
    sw   s0, 0(sp)
    sw   s1, 4(sp)

    # Decrement *g_illegal_instr_exp
    lw s0, g_illegal_instr_exp
    lw s1, 0(s0)
    addi s1, s1, -1
    sw s1, 0(s0)

    lw s1, 4(sp)
    lw s0, 0(sp)
    addi sp, sp, 8

    j end_handler_incr_mepc
  )");
}

// -----------------------------------------------------------------------------

uint32_t wfe_wakeup(uint32_t index, uint8_t report_name){
  volatile uint8_t test_fail = 0;
  volatile mstatus_t mstatus   = { 0 };

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_illegal_instr_exp = 0;

  // Execute wfe instructions and wait for wfe noise gen to wake core up
  // Expected to be checked by ISS
  __asm__ volatile (R"(
    #back to back
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
  )"::[wfe] "i"(WFE_INSTR));

  // print string to execute many instructions
  cvprintf(V_LOW, "1234567890\n");
  __asm__ volatile (R"(
    .word(%[wfe])
  )"::[wfe] "i"(WFE_INSTR));

  // print another string to execute many instructions
  cvprintf(V_LOW, "abcdefghijklmnopqrstuvwxyz\n");
  __asm__ volatile (R"(
    .word(%[wfe])
  )"::[wfe] "i"(WFE_INSTR));

  // Set timeout wait (mstatus.tw)
  mstatus.fields.tw = 1;
  __asm__ volatile ( R"(
    csrrs zero, mstatus, %[mstatus]
  )":: [mstatus] "r"(mstatus.raw));

  __asm__ volatile (R"(
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
  )"::[wfe] "i"(WFE_INSTR));

  __asm__ volatile ( R"(
    csrrc zero, mstatus, %[mstatus]
  )":: [mstatus] "r"(mstatus.raw));

  test_fail = (*g_illegal_instr_exp != 0);

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t wfe_wakeup_umode(uint32_t index, uint8_t report_name){
  volatile uint8_t   test_fail = 0;
  volatile uint32_t  pmpaddr   = 0xffffffff;
  volatile mstatus_t mstatus   = { 0 };

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Check if there user mode support
  if (!has_pmp_configured()) {
    cvprintf(V_LOW, "Skipping test: User mode/PMP not supported\n");
    return 0;
  }

  // Setup PMP access for u-mode (otherwise all deny)
  set_mseccfg((mseccfg_t){
      .fields.mml  = 0,
      .fields.mmwp = 0,
      .fields.rlb  = 1,
  });

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 1,
      .fields.w = 1,
      .fields.x = 1,
      .fields.a = PMPMODE_TOR,
      .fields.l = 0
  }, 0);

  __asm__ volatile ( R"(
    csrrw zero, pmpaddr0, %[pmpaddr]
  )":: [pmpaddr] "r"(pmpaddr));

  *g_illegal_instr_exp = 0;
  __asm__ volatile ( R"(
    ecall
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    ecall
    # add safe return location
    nop
  )"::[wfe] "i"(WFE_INSTR));

  test_fail = (*g_illegal_instr_exp != 0);

  // Set timeout wait (mstatus.tw)
  mstatus.fields.tw = 1;
  __asm__ volatile ( R"(
    csrrs zero, mstatus, %[mstatus]
  )":: [mstatus] "r"(mstatus.raw));

  *g_illegal_instr_exp = 6;
  __asm__ volatile ( R"(
    ecall
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    .word(%[wfe])
    ecall
    # add safe return location
    nop
  )"::[wfe] "i"(WFE_INSTR));

  __asm__ volatile ( R"(
    csrrc zero, mstatus, %[mstatus]
  )":: [mstatus] "r"(mstatus.raw));

  test_fail = (*g_illegal_instr_exp != 0);

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t wfi_mstatus_tw_umode_illegal(uint32_t index, uint8_t report_name){
  volatile uint8_t   test_fail = 0;
  volatile mstatus_t mstatus   = { 0 };

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Check if there user mode support
  if (!has_pmp_configured()) {
    cvprintf(V_LOW, "Skipping test: User mode/pmp not supported\n");
    return 0;
  }

  // Set timeout wait (mstatus.tw)
  mstatus.fields.tw = 1;
  __asm__ volatile ( R"(
    csrrs zero, mstatus, %[mstatus]
  )":: [mstatus] "r"(mstatus.raw));

  *g_illegal_instr_exp = 6;
  __asm__ volatile ( R"(
    ecall
    wfi
    wfi
    wfi
    wfi
    wfi
    wfi
    ecall
    # add safe return location
    nop
  )":::);

  __asm__ volatile ( R"(
    csrrc zero, mstatus, %[mstatus]
  )":: [mstatus] "r"(mstatus.raw));

  test_fail = (*g_illegal_instr_exp != 0);

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}


// -----------------------------------------------------------------------------
