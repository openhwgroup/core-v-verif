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
//
/////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>
#include <assert.h>
#include "corev_uvmt.h"

// MUST be 31 or less (bit position-1 in result array determines test pass/fail
// status, thus we are limited to 31 tests with this construct.
#define NUM_TESTS 1
// Set which test index to start testing at (for quickly running specific tests during development)
#define START_TEST_IDX 0

#define WFE_INSTR 0x8c000073

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

// Verbosity levels (Akin to the uvm verbosity concept)
typedef enum {
  V_OFF    = 0,
  V_LOW    = 1,
  V_MEDIUM = 2,
  V_HIGH   = 3,
  V_DEBUG  = 4
} verbosity_t;

// ---------------------------------------------------------------
// Global variables
// ---------------------------------------------------------------
// Print verbosity, consider implementing this as a virtual
// peripheral setting to be controlled from UVM.
volatile verbosity_t global_verbosity = V_LOW;

// ---------------------------------------------------------------
// Test prototypes - should match
// uint32_t <name>(uint32_t index, uint8_t report_name)
//
// Use template below for implementation
// ---------------------------------------------------------------
uint32_t wfe_wakeup(uint32_t index, uint8_t report_name);

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

// ---------------------------------------------------------------
// Test entry point
// ---------------------------------------------------------------
int main(int argc, char **argv){

  volatile uint32_t (* volatile tests[NUM_TESTS])(volatile uint32_t, volatile uint8_t);

  volatile uint32_t test_res = 0x1;
  volatile int      retval   = 0;

  // Add function pointers to new tests here
  tests[0]  = wfe_wakeup;

  // Run all tests in list above
  cvprintf(V_LOW, "\nWFE Test start\n\n");
  for (volatile int i = START_TEST_IDX; i < NUM_TESTS; i++) {
    test_res = set_test_status(tests[i](i, (volatile uint32_t)(0)), test_res);
  }

  // Report failures
  retval = get_result(test_res, tests);

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

uint32_t wfe_wakeup(uint32_t index, uint8_t report_name){
  volatile uint8_t test_fail = 0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

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
  cvprintf(V_LOW, "abcdefghijklmnopqrstuvwxyz");
  __asm__ volatile (R"(
    .word(%[wfe])
  )"::[wfe] "i"(WFE_INSTR));

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------
