//
// Copyright 2023 Silicon Labs, Inc.
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
// PMP CSR access test
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
#define NUM_TESTS 2
// Set which test index to start testing at (for quickly running specific tests during development)
#define START_TEST_IDX 0

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
#define OPCODE_SYSTEM 0x73
#define PMPCFG_BASE   0x3a0
#define PMPADDR_BASE  0x3b0
#define MSECCFG_BASE  0x747

// ---------------------------------------------------------------
// Global variables
// ---------------------------------------------------------------
// Print verbosity, consider implementing this as a virtual
// peripheral setting to be controlled from UVM.
volatile verbosity_t global_verbosity = V_LOW;

volatile uint32_t * volatile g_csr_instr;
volatile uint32_t * volatile g_csr_instr_rd_val;
volatile uint32_t * volatile g_csr_instr_rs1_val;
// ---------------------------------------------------------------
// Test prototypes - should match
// uint32_t <name>(uint32_t index, uint8_t report_name)
//
// Use template below for implementation
// ---------------------------------------------------------------
uint32_t pmp_write_addr_regs(uint32_t index, uint8_t report_name);
uint32_t pmp_write_cfg_regs(uint32_t index, uint8_t report_name);

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
 * call_word_instr
 *
 * Sets up the system to execute a 32bit word as an instruction
 * and return to the regular execution flow
 */
void call_word_instr(uint32_t instr_word);

/*
 * csr_instr
 *
 * Execute a csr access instruction
 *
 * - funct3: CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI
 * - addr: csr register address (numeric)
 * - rs1_uimm_val: rs1/uimm _value_ to supply to instruction
 * - return value contains value read from csr
 *
 */
uint32_t csr_instr(csr_instr_access_t funct3, uint32_t addr, uint32_t rs1_uimm_val);

// ---------------------------------------------------------------
// Test entry point
// ---------------------------------------------------------------
int main(int argc, char **argv){

  volatile uint32_t (* volatile tests[NUM_TESTS])(volatile uint32_t, volatile uint8_t);

  volatile uint32_t test_res = 0x1;
  volatile int      retval   = 0;

  g_csr_instr         = calloc(1, sizeof(uint32_t));
  g_csr_instr_rd_val  = calloc(1, sizeof(uint32_t));
  g_csr_instr_rs1_val = calloc(1, sizeof(uint32_t));

  // Add function pointers to new tests here
  tests[0]  = pmp_write_addr_regs;
  tests[1]  = pmp_write_cfg_regs;

  // Run all tests in list above
  cvprintf(V_LOW, "\nPMP CSR Test start\n\n");
  for (volatile int i = START_TEST_IDX; i < NUM_TESTS; i++) {
    test_res = set_test_status(tests[i](i, (volatile uint32_t)(0)), test_res);
  }

  // Report failures
  retval = get_result(test_res, tests);

  free((void *)g_csr_instr            );
  free((void *)g_csr_instr_rd_val     );
  free((void *)g_csr_instr_rs1_val    );
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

void __attribute__((naked)) call_word_instr(uint32_t instr_word){
  __asm__ volatile ( R"(
    .global ptr_loc
    addi sp, sp, -8
    sw a0, 0(sp)
    sw s0, 4(sp)

    la s0, ptr_loc
    sw a0, 0(s0)
    fence.i
    # ensure that we have a location to write our pointer
    ptr_loc: .word(0x00000000)

    lw s0, 4(sp)
    lw a0, 0(sp)
    addi sp, sp, 8
    ret
  )");
}

// -----------------------------------------------------------------------------

uint32_t csr_instr(csr_instr_access_t funct3, uint32_t addr, uint32_t rs1_uimm_val) {
  volatile csr_instr_t csr_instr = { 0 };

  *g_csr_instr_rd_val  = 0;
  *g_csr_instr_rs1_val = rs1_uimm_val;

  switch (funct3) {
    case CSRRW:
    case CSRRS:
    case CSRRC:
      csr_instr = (csr_instr_t){
        .fields.opcode   = OPCODE_SYSTEM,
        .fields.rd       = 11, // a1 reg
        .fields.funct3   = funct3,
        .fields.rs1_uimm = (rs1_uimm_val == 0) ? 0 : 12, // a2 reg unless zero specified
        .fields.csr      = addr
      };
      break;
    case CSRRWI:
    case CSRRSI:
    case CSRRCI:
      csr_instr = (csr_instr_t){
        .fields.opcode   = OPCODE_SYSTEM,
        .fields.rd       = 11, // a1 reg
        .fields.funct3   = funct3,
        .fields.rs1_uimm = rs1_uimm_val,
        .fields.csr      = addr
      };
      break;
    default: return 0;
  }

  *g_csr_instr = csr_instr.raw;

  __asm__ volatile ( R"(
    addi sp, sp, -16
    sw a0, 0(sp)
    sw a1, 4(sp)
    sw a2, 8(sp)
    sw ra, 12(sp)

    lw a0, g_csr_instr
    lw a0, 0(a0)
    lw a2, g_csr_instr_rs1_val
    lw a2, 0(a2)
    jal ra, call_word_instr
    lw a2, g_csr_instr_rd_val
    sw a1, 0(a2)

    lw ra, 12(sp)
    lw a2, 8(sp)
    lw a1, 4(sp)
    lw a0, 0(sp)
    addi sp, sp, 16
  )");

  return *g_csr_instr_rd_val;
}

// -----------------------------------------------------------------------------

uint32_t pmp_write_addr_regs(uint32_t index, uint8_t report_name){
  volatile uint8_t test_fail = 0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  for (int i = 0; i < 64; i++) {
    (void)csr_instr(CSRRW, PMPADDR_BASE + i, 0xffffffffUL);
    (void)csr_instr(CSRRW, PMPADDR_BASE + i, 0x00000000UL);
    (void)csr_instr(CSRRS, PMPADDR_BASE + i, 0xffffffffUL);
    (void)csr_instr(CSRRC, PMPADDR_BASE + i, 0xffffffffUL);
    test_fail = 63 - i; // fail test if we somehow did not run through the entire loop
  }

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t pmp_write_cfg_regs(uint32_t index, uint8_t report_name){
  volatile uint8_t test_fail = 0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Set rlb in mseccfg to enable us to revert changes to pmp regions
  (void)csr_instr(CSRRS, MSECCFG_BASE, 4UL);

  // Set all addr regs to top of memory (unused) to avoid lockout
  for (int i = 0; i < 64; i++) {
    (void)csr_instr(CSRRW, PMPADDR_BASE + i, 0xffffffffUL);
  }

  // Set/clear all cfg reg bits to 1
  for (int i = 0; i < 16; i++) {
    (void)csr_instr(CSRRW, PMPCFG_BASE + i, 0xffffffffUL);
    (void)csr_instr(CSRRW, PMPCFG_BASE + i, 0x00000000UL);
    (void)csr_instr(CSRRS, PMPCFG_BASE + i, 0xffffffffUL);
    (void)csr_instr(CSRRC, PMPCFG_BASE + i, 0xffffffffUL);
    test_fail = 15 - i; // fail test if we somehow did not run through the entire loop
  }

  // Clear all addr reg bits
  for (int i = 0; i < 64; i++) {
    (void)csr_instr(CSRRCI, PMPADDR_BASE + i, 0x00000000UL);
  }

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

