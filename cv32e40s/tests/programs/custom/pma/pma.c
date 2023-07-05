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
// Author: Robin Pedersen/Henrik Fegran
//
// PMA directed tests
//
/////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>
#include "corev_uvmt.h"

// MUST be 31 or less (bit position-1 in result array determines test pass/fail
// status, thus we are limited to 31 tests with this construct.
#define NUM_TESTS 9
// Start at 1 (ignore dummy test that is only used for env sanity checking during dev.)
#define START_TEST_NUM 1
// Abort test at first self-check fail, useful for debugging.
#define ABORT_ON_ERROR_IMMEDIATE 0

// Addresses of VP interrupt control registers
#define TIMER_REG_ADDR         ((volatile uint32_t * volatile) (CV_VP_INTR_TIMER_BASE))
#define TIMER_VAL_ADDR         ((volatile uint32_t * volatile) (CV_VP_INTR_TIMER_BASE + 4))
#define DEBUG_REQ_CONTROL_REG *((volatile uint32_t * volatile) (CV_VP_DEBUG_CONTROL_BASE))

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
// Type definitions
// ---------------------------------------------------------------


// Verbosity levels (Akin to the uvm verbosity concept)
typedef enum {
  V_OFF    = 0,
  V_LOW    = 1,
  V_MEDIUM = 2,
  V_HIGH   = 3,
  V_DEBUG  = 4
} verbosity_t;

typedef enum {
  MCAUSE_ACCESS_FAULT    = 1,
  MCAUSE_ILLEGAL         = 2,
  MCAUSE_BREAKPT         = 3,
  MCAUSE_LOAD_FAULT      = 5,
  MCAUSE_STORE_FAULT     = 7,
  MCAUSE_UMODE_ECALL     = 8,
  MCAUSE_MMODE_ECALL     = 11,
  MCAUSE_INSTR_BUS_FAULT = 24,
  MCAUSE_CHK_FAULT       = 25,
} mcause_exception_status_t;

typedef union {
  struct {
    volatile uint32_t exccode   : 12;
    volatile uint32_t res_30_12 : 19;
    volatile uint32_t interrupt : 1;
  } __attribute__((packed)) volatile clint;
  struct {
    volatile uint32_t exccode    : 12;
    volatile uint32_t res_15_12  : 4;
    volatile uint32_t mpil       : 8;
    volatile uint32_t res_26_24  : 3;
    volatile uint32_t mpie       : 1;
    volatile uint32_t mpp        : 2;
    volatile uint32_t minhv      : 1;
    volatile uint32_t interrupt  : 1;
  } __attribute__((packed)) volatile clic;
  volatile uint32_t raw : 32;
} __attribute__((packed)) mcause_t;

// ---------------------------------------------------------------
// Global variables
// ---------------------------------------------------------------

// Print verbosity, consider implementing this as a virtual
// peripheral setting to be controlled from UVM.
volatile verbosity_t global_verbosity = V_LOW;

// Global pointer variables
volatile uint32_t * volatile g_has_clic;
volatile uint32_t * volatile g_exp_fault;
volatile mcause_t * volatile g_mcause;
volatile uint32_t * volatile g_mepc;
volatile uint32_t * volatile g_mtval;
volatile uint32_t * volatile g_test_num;
volatile uint32_t * volatile g_recovery_ptr;

// External symbols
extern volatile uint32_t mtvt_table;

// Message strings for use in assembly printf
//const volatile char * const volatile asm_printf_msg_template = "Entered handler %0d\n";

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
//   cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
//   return 0;
// }
// ---------------------------------------------------------------

// ---------------------------------------------------------------
// Test prototypes - should match
// uint32_t <name>(uint32_t index, uint8_t report_name)
//
// Use template below for implementation
// ---------------------------------------------------------------
uint32_t dummy(uint32_t index, uint8_t report_name);
uint32_t exec_only_for_main_regions(uint32_t index, uint8_t report_name);
uint32_t non_natural_aligned_store_to_io(uint32_t index, uint8_t report_name);
uint32_t non_natural_aligned_loads_from_io(uint32_t index, uint8_t report_name);
uint32_t misaligned_fault_nochange_regfile(uint32_t index, uint8_t report_name);
uint32_t misaligned_border_io_to_mem(uint32_t index, uint8_t report_name);
uint32_t misaligned_border_mem_to_io(uint32_t index, uint8_t report_name);
uint32_t misalign_store_fault_no_bus_access_second(uint32_t index, uint8_t report_name);
uint32_t misalign_store_fault_io_no_bus_access_first(uint32_t index, uint8_t report_name);

// ---------------------------------------------------------------
// Prototypes for functions that are test specific and
// perform the debug part of specific tests.
// ---------------------------------------------------------------
//void template_function_dbg(void) __attribute__((section(".debugger"), __noinline__));

// ---------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------
void increment_mepc(volatile uint32_t incr_val);
void clear_status_csrs(void);

// IRQ related
uint32_t detect_irq_mode(void);
void setup_clic(void);


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
uint32_t set_test_status(volatile uint32_t test_no, volatile uint32_t val_prev);

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
int cvprintf(verbosity_t verbosity, const char *format, ...) __attribute((__noinline__));

// ---------------------------------------------------------------
// Test entry point
// ---------------------------------------------------------------
int main(int argc, char **argv){

  volatile uint32_t (* volatile tests[NUM_TESTS])(volatile uint32_t, volatile uint8_t);
  volatile uint32_t test_res = 0x1;
  volatile int      retval   = 0;

  // Allocate memory for global pointers here
  g_has_clic               = calloc(1, sizeof(uint32_t));
  g_mcause                 = calloc(1, sizeof(mcause_t));
  g_mepc                   = calloc(1, sizeof(uint32_t));
  g_mtval                  = calloc(1, sizeof(uint32_t));
  g_test_num               = calloc(1, sizeof(uint32_t));
  g_exp_fault              = calloc(1, sizeof(uint32_t));
  g_recovery_ptr           = calloc(1, sizeof(uint32_t));

  // Setup clic mtvt if clic is enabled
  *g_has_clic = detect_irq_mode();
  setup_clic();

  // Add function pointers to new tests here
  tests[0]  = dummy; // unused, can be used for env sanity checking
  tests[1]  = exec_only_for_main_regions;
  tests[2]  = non_natural_aligned_store_to_io;
  tests[3]  = non_natural_aligned_loads_from_io;
  tests[4]  = misaligned_fault_nochange_regfile;
  tests[5]  = misaligned_border_io_to_mem;
  tests[6]  = misaligned_border_mem_to_io;
  tests[7]  = misalign_store_fault_no_bus_access_second;
  tests[8]  = misalign_store_fault_io_no_bus_access_first;
  // Run all tests in list above
  cvprintf(V_LOW, "\nPMA test start\n\n");
  for (volatile uint32_t i = START_TEST_NUM; i < NUM_TESTS; i++) {
    test_res = set_test_status(tests[i](i, (volatile uint32_t)(0)), test_res);
  }

  // Report failures
  retval = get_result(test_res, tests);

  // Free dynamically allocated memory
  free((void *)g_has_clic                  );
  free((void *)g_mcause                    );
  free((void *)g_mepc                      );
  free((void *)g_mtval                     );
  free((void *)g_test_num                  );
  free((void *)g_exp_fault                 );
  free((void *)g_recovery_ptr              );

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

uint32_t set_test_status(volatile uint32_t test_no, volatile uint32_t val_prev){
  volatile uint32_t res;
  res = val_prev | (1 << test_no);
  return res;
}

// -----------------------------------------------------------------------------

int get_result(uint32_t res, uint32_t (* volatile ptr[])(uint32_t, uint8_t)){
    cvprintf(V_LOW, "=========================\n");
    cvprintf(V_LOW, "=        SUMMARY        =\n");
    cvprintf(V_LOW, "=========================\n");
    for (int i = START_TEST_NUM; i < NUM_TESTS; i++){
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
  return res;
}

// -----------------------------------------------------------------------------

uint32_t dummy(uint32_t index, uint8_t report_name) {
  volatile uint32_t test_fail = 0;
  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Example:
  // ...
  // Some directed test code here
  // ...

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t exec_only_for_main_regions(uint32_t index, uint8_t report_name) {
  volatile uint32_t test_fail = 0;
  volatile void (* volatile io_addr)(void) = (volatile void (* volatile)(void))0x1a110810;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_test_num = index;
  *g_exp_fault = 1;

  test_fail += (g_mcause->raw != 0);
  test_fail += (*g_mtval      != 0);
  test_fail += (*g_mepc       != 0);

  io_addr();

  test_fail += (g_mcause->raw != MCAUSE_ACCESS_FAULT);
  test_fail += (*g_mtval      != 0);
  test_fail += (*g_mepc       != (uint32_t)io_addr);

  test_fail += *g_exp_fault;
  clear_status_csrs();

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t non_natural_aligned_store_to_io(uint32_t index, uint8_t report_name) {
  volatile uint32_t test_fail = 0;
  volatile uint32_t io_addr   = 0x1a110810;
  volatile uint32_t tmp       = 0xaaaaaaaa;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_test_num               = index;
  // Sanity, aligned store to IO
  *g_exp_fault = 0;

  __asm__ volatile (R"(
    sw %[tmp], 0(%[addr])
  )" : [tmp] "=r"(tmp)
     : [addr]  "r"(io_addr)
  );

  test_fail += *g_exp_fault;
  test_fail += g_mcause->raw != 0;
  test_fail += *g_mepc       != 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();

  // Misalgined store to IO
  *g_exp_fault = 1;
  tmp = 0xbbbbbbbb;

  __asm__ volatile (R"(
    sw %[tmp], 1(%[addr])
  )" : [tmp] "=r"(tmp)
     : [addr]  "r"(io_addr)
  );

  test_fail += *g_exp_fault;
  test_fail += g_mcause->raw != MCAUSE_STORE_FAULT;
  test_fail += *g_mepc       == 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();

  // Sanity, misaligned store to MAIN
  *g_exp_fault = 0;

  __asm__ volatile (R"(
    sw %[tmp], -9(%[addr])
  )" : [tmp] "=r"(tmp)
     : [addr]  "r"(io_addr)
  );

  test_fail += *g_exp_fault;
  test_fail += g_mcause->raw != 0;
  test_fail += *g_mepc       != 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t non_natural_aligned_loads_from_io(uint32_t index, uint8_t report_name) {
  volatile uint32_t test_fail = 0;
  volatile uint32_t io_addr   = 0x1a110810;
  volatile uint32_t mem_addr  = 0x80;
  volatile uint32_t tmp       = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_test_num               = index;
  *g_exp_fault = 0;

  // Sanity, aligned loads should be OK
  __asm__ volatile (R"(
    lw %[tmp], 0(%[addr])
  )" : [tmp] "=r"(tmp)
     : [addr] "r"(io_addr)
  );

  test_fail += *g_exp_fault;
  test_fail += g_mcause->raw != 0;
  test_fail += *g_mepc       != 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();

  // Check that misaligned load will except
  *g_exp_fault = 1;

  __asm__ volatile (R"(
    lw %[tmp], 5(%[addr])
  )" : [tmp] "=r"(tmp)
     : [addr] "r"(io_addr)
  );

  test_fail += *g_exp_fault;
  test_fail += g_mcause->raw != MCAUSE_LOAD_FAULT;
  test_fail += *g_mepc       == 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();

  // check that misaligned to MAIN does not fail
  *g_exp_fault = 0;

  __asm__ volatile (R"(
   lw %[tmp], 3(%[addr])
  )" : [tmp] "=r"(tmp)
     : [addr] "r"(mem_addr)
  );

  test_fail += *g_exp_fault;
  test_fail += g_mcause->raw != 0;
  test_fail += *g_mepc       != 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t misaligned_fault_nochange_regfile(uint32_t index, uint8_t report_name) {
  volatile uint32_t test_fail = 0;
  volatile uint32_t io_addr   = 0x1a110810;
  volatile uint32_t tmp       = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_test_num               = index;

  *g_exp_fault = 0;
  // Store data to check address
  __asm__ volatile (R"(
    li %[tmp], 0xaaaaaaaa
    sw %[tmp], 0(%[addr])
    li %[tmp], 0xbbbbbbbb
    sw %[tmp], 4(%[addr])
  )"
     : [tmp] "+r"(tmp)
     : [addr] "r"(io_addr)
     : "memory"
  );
  test_fail += *g_exp_fault;
  test_fail += g_mcause->raw != 0;
  test_fail += *g_mepc       != 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();

  tmp = 0xcafeabba;
  // Read misaligned
  *g_exp_fault = 1;

  __asm__ volatile (R"(
    # need to use explicit register to prevent the compiler from backing up
    add t0, %[tmp], zero
    # should never execute
    lw t0, 3(%[addr])

    add %[tmp], t0, zero
  )"
     : [tmp] "+r"(tmp)
     : [addr] "r"(io_addr)
     : "t0", "memory"
  );

  test_fail += *g_exp_fault;
  test_fail += tmp           != 0xcafeabba;
  test_fail += g_mcause->raw != MCAUSE_LOAD_FAULT;
  test_fail += *g_mepc       == 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();
  cvprintf(V_DEBUG, "Tmp: %08lx\n", tmp);

  // Read aligned
  *g_exp_fault = 0;

  __asm__ volatile (R"(
    lw %[tmp], 0(%[addr])
  )"
     : [tmp] "=r"(tmp)
     : [addr] "r"(io_addr)
     :
  );

  test_fail += *g_exp_fault;
  test_fail += tmp           != 0xaaaaaaaa;
  test_fail += g_mcause->raw != 0;
  test_fail += *g_mepc       != 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();
  cvprintf(V_DEBUG, "Tmp: %08lx\n", tmp);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

uint32_t misaligned_border_io_to_mem(uint32_t index, uint8_t report_name) {
  volatile uint32_t test_fail  = 0;
  volatile uint32_t mem_addr_1 = 0x1a111000;
  volatile uint32_t tmp        = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_test_num               = index;

  *g_exp_fault = 1;
  __asm__ volatile(R"(
    # store reference values
    li %[tmp], 0xaaaaaaaa
    sw %[tmp], -4(%[addr])
    li %[tmp], 0xbbbbbbbb
    sw %[tmp], 0(%[addr])

    # misaligned load
    # need to use explicit register to prevent the compiler from backing up
    add t0, %[tmp], zero
    # should not execute
    lw t0, -2(%[addr])

    add %[tmp], t0, zero
  )"
    : [tmp] "+r"(tmp)
    : [addr] "r"(mem_addr_1)
    : "t0", "memory"
  );

  test_fail += *g_exp_fault;
  test_fail += tmp           != 0xbbbbbbbb;
  test_fail += g_mcause->raw != MCAUSE_LOAD_FAULT;
  test_fail += *g_mepc       == 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();

  cvprintf(V_DEBUG, "Tmp: %08lx\n", tmp);

  *g_exp_fault = 0;
  tmp = 0;
  __asm__ volatile(R"(
    # halfword load not crossing boundary
    lh %[tmp], -2(%[addr])
  )"
    : [tmp] "+r"(tmp)
    : [addr] "r"(mem_addr_1)
    : "memory"
  );

  test_fail += *g_exp_fault;
  test_fail += tmp           != 0xffffaaaa; // f's due to sign extension
  test_fail += g_mcause->raw != 0;
  test_fail += *g_mepc       != 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();

  cvprintf(V_DEBUG, "Tmp: %08lx\n", tmp);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t misaligned_border_mem_to_io(uint32_t index, uint8_t report_name) {
  volatile uint32_t test_fail  = 0;
  volatile uint32_t io_addr    = 0x1a110810;
  volatile uint32_t tmp        = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_test_num               = index;

  *g_exp_fault = 1;

  __asm__ volatile(R"(
    # store reference values
    li %[tmp], 0xaaaaaaaa
    sw %[tmp], -4(%[addr])
    li %[tmp], 0xbbbbbbbb
    sw %[tmp], 0(%[addr])

    # Misaligned, boundary crossing load
    # need to use explicit register to prevent the compiler from backing up
    add t0, %[tmp], zero
    # should not execute
    lw t0, -1(%[addr])

    add %[tmp], t0, zero
  )"
    : [tmp] "+r"(tmp)
    : [addr] "r"(io_addr)
    : "t0", "memory"
  );

  test_fail += *g_exp_fault;
  test_fail += tmp           != 0xbbbbbbbb;
  test_fail += g_mcause->raw != MCAUSE_LOAD_FAULT;
  test_fail += *g_mepc       == 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();
  cvprintf(V_DEBUG, "Tmp: %08lx\n", tmp);
  tmp = 0;

  *g_exp_fault = 0;
  // Sanity, aligned
  __asm__ volatile(R"(
    # aligned load
    lb %[tmp], -1(%[addr])
  )"
    : [tmp] "+r"(tmp)
    : [addr] "r"(io_addr)
    : "memory"
  );

  test_fail += *g_exp_fault;
  test_fail += tmp           != 0xffffffaa; // f's due to sign extension
  test_fail += g_mcause->raw != 0;
  test_fail += *g_mepc       != 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();
  cvprintf(V_DEBUG, "Tmp: %08lx\n", tmp);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t misalign_store_fault_no_bus_access_second(uint32_t index, uint8_t report_name) {
  volatile uint32_t test_fail  = 0;
  volatile uint32_t io_addr    = 0x1a110810;
  volatile uint32_t tmp        = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_test_num               = index;

  // Check first access fail
  *g_exp_fault = 1;

  tmp = 0;
  __asm__ volatile(R"(
    # store reference values
    li t0, 0xaaaaaaaa
    sw t0, 0(%[addr])
    li t0, 0xbbbbbbbb
    sw t0, 4(%[addr])

    # Misaligned, boundary crossing store
    li t0, 0x11223344
    sw t0, 2(%[addr])
  )"
    :
    : [addr] "r"(io_addr)
    : "t0", "memory"
  );

  test_fail += *g_exp_fault;
  test_fail += g_mcause->raw != MCAUSE_STORE_FAULT;
  test_fail += *g_mepc       == 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();

  __asm__ volatile(R"(
    # Check if first store op reached bus
    lw t0, 0(%[addr])
    add %[tmp], t0, zero
  )"
    : [tmp] "=r"(tmp)
    : [addr] "r"(io_addr)
    : "t0", "memory"
  );

  test_fail += *g_exp_fault;
  test_fail += tmp           != 0xaaaaaaaa;
  test_fail += g_mcause->raw != 0;
  test_fail += *g_mepc       != 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();
  cvprintf(V_DEBUG, "Tmp: %08lx\n", tmp);
  tmp = 0;

  *g_exp_fault = 0;

  __asm__ volatile(R"(
    # Check if second store op reached bus
    lw %[tmp], 4(%[addr])
  )"
    : [tmp] "+r"(tmp)
    : [addr] "r"(io_addr)
    : "memory"
  );

  test_fail += *g_exp_fault;
  test_fail += tmp           != 0xbbbbbbbb;
  test_fail += g_mcause->raw != 0;
  test_fail += *g_mepc       != 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();
  cvprintf(V_DEBUG, "Tmp: %08lx\n", tmp);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t misalign_store_fault_io_no_bus_access_first(uint32_t index, uint8_t report_name) {
  volatile uint32_t test_fail  = 0;
  volatile uint32_t mem_addr_1 = 0x1a111000;
  volatile uint32_t tmp        = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_test_num               = index;

  // Check first access fail
  *g_exp_fault = 1;

  tmp = 0;
  __asm__ volatile(R"(
    # store reference values
    li t0, 0xaaaaaaaa
    sw t0, -4(%[addr])
    li t0, 0xbbbbbbbb
    sw t0, 0(%[addr])

    # Misaligned, boundary crossing store
    li t0, 0x22334455
    sw t0, -2(%[addr])
  )"
    :
    : [addr] "r"(mem_addr_1)
    : "t0", "memory"
  );

  test_fail += *g_exp_fault;
  test_fail += g_mcause->raw != MCAUSE_STORE_FAULT;
  test_fail += *g_mepc       == 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();

  *g_exp_fault = 0;

  __asm__ volatile(R"(
    # Check if first store op reached bus
    lw t0, -4(%[addr])
    add %[tmp], t0, zero
  )"
    : [tmp] "=r"(tmp)
    : [addr] "r"(mem_addr_1)
    : "t0", "memory"
  );

  test_fail += *g_exp_fault;
  test_fail += tmp           != 0xaaaaaaaa;
  test_fail += g_mcause->raw != 0;
  test_fail += *g_mepc       != 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();
  cvprintf(V_DEBUG, "Tmp: %08lx\n", tmp);

  tmp = 0;

  *g_exp_fault = 0;

  __asm__ volatile(R"(
    # Check if second store op reached bus
    lw t0, 0(%[addr])
    add %[tmp], t0, zero
  )"
    : [tmp] "+r"(tmp)
    : [addr] "r"(mem_addr_1)
    : "t0", "memory"
  );

  test_fail += *g_exp_fault;
  test_fail += tmp != 0xbbbbbbbb;
  test_fail += g_mcause->raw != 0;
  test_fail += *g_mepc       != 0;
  test_fail += *g_mtval      != 0;
  clear_status_csrs();
  cvprintf(V_DEBUG, "Tmp: %08lx\n", tmp);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

// TODO: implement the following for 40X:
// Plan: Detect 40s/40x by checking csrs (avoid ifdefs)
//
//  printf("pma: 6. Atomics should work only where it is allowed\n");
//
//  printf("pma: Sanity check that atomic ops (lr/sc) to allowed regions is ok\n");
//  reset_volatiles();
//  __asm__ volatile("lr.w %0, 0(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
//  __asm__ volatile("sc.w %0, %0, 0(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
//  assert_or_die(g_mcause, -1, "error: atomics to legal region should not except\n");
//  assert_or_die(g_mepc, -1, "error: atomics to legal region unexpected mepc\n");
//  assert_or_die(g_mtval, -1, "error: atomics to legal region unexpected mtval\n");
//
//  printf("pma: Load-reserved to disallowed regions raises precise exception\n");
//  reset_volatiles();
//  __asm__ volatile("lr.w %0, 0(%1)" : "=r"(tmp) : "r"(IO_ADDR));
//  assert_or_die(g_mcause, EXCEPTION_LOAD_ACCESS_FAULT, "error: load-reserved to non-atomic should except\n");
//  assert_or_die(g_mepc, IO_ADDR, "error: load-reserved to non-atomic unexpected mepc\n");
//  assert_or_die(g_mtval, MTVAL_READ, "error: load-reserved to non-atomic unexpected mtval\n");
//
//  printf("pma: Store-conditional to disallowed regions raises precise exception\n");
//  reset_volatiles();
//  __asm__ volatile("sc.w %0, %0, 0(%1)" : "=r"(tmp) : "r"(IO_ADDR));
//  assert_or_die(g_mcause, EXCEPTION_STOREAMO_ACCESS_FAULT, "error: store-conditional to non-atomic should except\n");
//  assert_or_die(g_mepc, IO_ADDR, "error: store-conditional to non-atomic unexpected mepc\n");
//  assert_or_die(g_mtval, MTVAL_READ, "error: store-conditional to non-atomic unexpected mtval\n");

// -----------------------------------------------------------------------------

// New tests here...

// -----------------------------------------------------------------------------

void clear_status_csrs(void) {
  g_mcause->raw = 0;
  *g_mepc       = 0;
  *g_mtval      = 0;
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

void setup_clic(void) {
  if (*g_has_clic == 1) {
    __asm__ volatile ( R"(
      csrrw zero, 0x307, %[mtvt_table]
    )" :: [mtvt_table] "r"(&mtvt_table));
  }
}

// -----------------------------------------------------------------------------

// Template for mtvt code, this may need adaptation if you want to support
// interrupts with ids in the indices below that are populated by zeros
void __attribute__((naked)) mtvt_code(void) {
  __asm__ volatile ( R"(
    .global mtvt_table
    .align 7
    mtvt_table: .long . + 4096
    mtvt_table_1: .long . + 4092
    mtvt_table_2: .long . + 4088
    mtvt_table_3: .long . + 4084
    mtvt_table_4: .long . + 4080
    .space 100, 0x0
    mtvt_table_30: .long . + 3976
    mtvt_table_31: .long . + 3972
    mtvt_table_32: .long . + 3968
    .space 3952, 0x0
    mtvt_table_1021: .long . + 12
    mtvt_table_1022: .long . + 8
    mtvt_table_1023: .long . + 4
    jal zero, m_fast14_irq_handler
  )");

}

// -----------------------------------------------------------------------------

uint32_t detect_irq_mode(void) {
  volatile uint32_t mtvec   = 0;
  volatile uint32_t is_clic = 0;

  __asm__ volatile ( R"(
    csrrs %[mtvec], mtvec, zero
  )" : [mtvec] "=r"(mtvec));

  if ((mtvec & 0x3) == 0x3) {
    is_clic = 1;
  }

  return is_clic;
}

// -----------------------------------------------------------------------------

void __attribute__((naked)) u_sw_irq_handler(void) {
  __asm__ volatile (R"(
    .extern u_sw_irq_handler_normal
    cm.push {ra, s0-s11}, -112
    addi sp, sp, -12

    # Save argument registers to stack
    # as we want to be able to call C-functions
    # from debug
    sw a0, 0(sp)
    sw a1, 4(sp)
    sw a2, 8(sp)
    sw a3, 12(sp)
    sw a4, 16(sp)
    sw a5, 20(sp)
    sw a6, 24(sp)
    sw a7, 28(sp)

    # Back up remaining temporaries
    sw tp, 32(sp)
    sw t0, 36(sp)
    sw t1, 40(sp)
    sw t2, 44(sp)
    sw t3, 48(sp)
    sw t4, 52(sp)
    sw t5, 56(sp)
    sw t6, 60(sp)

    sw gp, 64(sp)

    lw t0, g_recovery_ptr
    sw ra, 0(t0)

    jal ra, u_sw_irq_handler_normal

    lw t0, g_recovery_ptr
    lw ra, 0(t0)

    ## restore stack
    lw gp, 64(sp)

    # Restore temporary registers
    lw t6, 60(sp)
    lw t5, 56(sp)
    lw t4, 52(sp)
    lw t3, 48(sp)
    lw t2, 44(sp)
    lw t1, 40(sp)
    lw t0, 36(sp)
    lw tp, 32(sp)

    # Restore argument registers
    lw a7, 28(sp)
    lw a6, 24(sp)
    lw a5, 20(sp)
    lw a4, 16(sp)
    lw a3, 12(sp)
    lw a2, 8(sp)
    lw a1, 4(sp)
    lw a0, 0(sp)

    # Restore stack ptr
    addi sp, sp, 12
    cm.pop {ra, s0-s11}, 112
    mret
  )");

}

void u_sw_irq_handler_normal(void) {
  volatile uint32_t ra = 0;

  __asm__ volatile( R"(
    add   %[ra],     ra,     zero
    csrrs %[mcause], mcause, zero
    csrrs %[mepc],   mepc,   zero
    csrrs %[mtval],  mtval,  zero
    )"
    : [ra]     "=r"(ra),
      [mcause] "=r"(g_mcause->raw),
      [mepc]   "=r"(*g_mepc),
      [mtval]  "=r"(*g_mtval)
    :
    : "memory"
  );

  if (*g_test_num == 1) {
    *g_exp_fault = 0;
    __asm__ volatile ( R"(
      lw t0, g_recovery_ptr
      lw t0, 0(t0)
      csrrw zero, mepc, t0
    )" ::: "t0", "memory");
  }
  else if (*g_test_num >= 2 && *g_test_num <= 9) {
    increment_mepc(0);
    if (*g_exp_fault) {
      *g_exp_fault = 0;
    } else {
      *g_exp_fault = 1;
    }
  }
  return;
}
// -----------------------------------------------------------------------------
