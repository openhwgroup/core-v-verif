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
// Debug directed tests
//
// Requires: number of triggers >= 1
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
#define NUM_TESTS 1
// Start at 1 (ignore dummy test that is only used for env sanity checking during dev.)
#define START_TEST_NUM 0
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

typedef enum {
  DCAUSE_EBREAK       = 1,
  DCAUSE_TRIGGER      = 2,
  DCAUSE_HALTREQ      = 3,
  DCAUSE_STEP         = 4,
  DCAUSE_RESETHALTREQ = 5,
  DCAUSE_HALTGROUP    = 6,
} dcsr_cause_t;

typedef enum {
  MODE_USER        = 0,
  MODE_SUPERVISOR  = 1,
  MODE_RESERVED    = 2,
  MODE_MACHINE     = 3
} mode_t;

typedef enum {
  PMPMODE_OFF   = 0,
  PMPMODE_TOR   = 1,
  PMPMODE_NA4   = 2,
  PMPMODE_NAPOT = 3
} pmp_mode_t;

typedef union {
  struct {
    volatile uint32_t r            : 1;
    volatile uint32_t w            : 1;
    volatile uint32_t x            : 1;
    volatile uint32_t a            : 1;
    volatile uint32_t reserved_6_5 : 2;
    volatile uint32_t l            : 1;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw : 8;
} __attribute__((packed)) pmpsubcfg_t;

typedef union {
  struct {
    volatile uint32_t cfg : 8;
  } __attribute__((packed)) volatile reg_idx[4];
  volatile uint32_t raw : 32;
} __attribute__((packed)) pmpcfg_t;

typedef union {
  struct {
    volatile uint32_t mml           : 1;
    volatile uint32_t mmwp          : 1;
    volatile uint32_t rlb           : 1;
    volatile uint32_t reserved_31_3 : 29;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw : 32;
} mseccfg_t;

typedef union {
  struct {
    volatile uint32_t shv            : 1;
    volatile uint32_t priv           : 2;
    volatile uint32_t level          : 8;
    volatile uint32_t id             : 11;
    volatile uint32_t irq            : 1;
    volatile uint32_t reserved_31_22 : 9;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t  raw : 32;
} __attribute__((packed)) clic_t ;

typedef union {
  struct {
    volatile uint32_t irq_0  : 1;
    volatile uint32_t irq_1  : 1;
    volatile uint32_t irq_2  : 1;
    volatile uint32_t irq_3  : 1;
    volatile uint32_t irq_4  : 1;
    volatile uint32_t irq_5  : 1;
    volatile uint32_t irq_6  : 1;
    volatile uint32_t irq_7  : 1;
    volatile uint32_t irq_8  : 1;
    volatile uint32_t irq_9  : 1;
    volatile uint32_t irq_10 : 1;
    volatile uint32_t irq_11 : 1;
    volatile uint32_t irq_12 : 1;
    volatile uint32_t irq_13 : 1;
    volatile uint32_t irq_14 : 1;
    volatile uint32_t irq_15 : 1;
    volatile uint32_t irq_16 : 1;
    volatile uint32_t irq_17 : 1;
    volatile uint32_t irq_18 : 1;
    volatile uint32_t irq_19 : 1;
    volatile uint32_t irq_20 : 1;
    volatile uint32_t irq_21 : 1;
    volatile uint32_t irq_22 : 1;
    volatile uint32_t irq_23 : 1;
    volatile uint32_t irq_24 : 1;
    volatile uint32_t irq_25 : 1;
    volatile uint32_t irq_26 : 1;
    volatile uint32_t irq_27 : 1;
    volatile uint32_t irq_28 : 1;
    volatile uint32_t irq_29 : 1;
    volatile uint32_t irq_30 : 1;
    volatile uint32_t irq_31 : 1;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw : 32;
} __attribute__((packed)) clint_t;

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

typedef union {
  struct {
    volatile uint32_t data   : 27;
    volatile uint32_t dmode  : 1;
    volatile uint32_t type   : 4;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) tdata1_t;

typedef union {
  struct {
    volatile uint16_t load    : 1;
    volatile uint16_t store   : 1;
    volatile uint16_t execute : 1;
    volatile uint16_t u       : 1;
    volatile uint16_t s       : 1;
    volatile uint16_t res_5_5 : 1;
    volatile uint16_t m       : 1;
    volatile uint16_t match   : 4;
    volatile uint16_t chain   : 1;
    volatile uint16_t action  : 4;
    volatile uint16_t sizelo  : 2;
    volatile uint16_t timing  : 1;
    volatile uint16_t select  : 1;
    volatile uint16_t hit     : 1;
    volatile uint16_t maskmax : 6;
    volatile uint16_t dmode   : 1;
    volatile uint16_t type    : 4;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) mcontrol_t;

typedef union {
  struct {
    volatile uint16_t load     : 1;
    volatile uint16_t store    : 1;
    volatile uint16_t execute  : 1;
    volatile uint16_t u        : 1;
    volatile uint16_t s        : 1;
    volatile uint16_t res_5_5  : 1;
    volatile uint16_t m        : 1;
    volatile uint16_t match    : 4;
    volatile uint16_t chain    : 1;
    volatile uint16_t action   : 4;
    volatile uint16_t size     : 4;
    volatile uint16_t timing   : 1;
    volatile uint16_t select   : 1;
    volatile uint16_t hit      : 1;
    volatile uint16_t vu       : 1;
    volatile uint16_t vs       : 1;
    volatile uint16_t res_26_25: 2;
    volatile uint16_t dmode    : 1;
    volatile uint16_t type     : 4;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) mcontrol6_t;

typedef union {
  struct {
    volatile uint8_t  action     : 6;
    volatile uint8_t  u          : 1;
    volatile uint8_t  s          : 1;
    volatile uint8_t  res_8_8    : 1;
    volatile uint8_t  m          : 1;
    volatile uint8_t  res_10_10  : 1;
    volatile uint8_t  vu         : 1;
    volatile uint8_t  vs         : 1;
    volatile uint16_t res_25_13  : 13;
    volatile uint8_t  hit        : 1;
    volatile uint8_t  dmode      : 1;
    volatile uint8_t  type       : 4;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) etrigger_t;

typedef union {
  struct {
    volatile uint16_t info      : 16;
    volatile uint16_t res_31_16 : 16;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) tinfo_t;

typedef union {
  struct {
    volatile uint8_t uie   : 1;  //     0
    volatile uint8_t sie   : 1;  //     1
    volatile uint8_t wpri  : 1;  //     2
    volatile uint8_t mie   : 1;  //     3
    volatile uint8_t upie  : 1;  //     4
    volatile uint8_t spie  : 1;  //     5
    volatile uint8_t wpri0 : 1;  //     6
    volatile uint8_t mpie  : 1;  //     7
    volatile uint8_t spp   : 1;  //     8
    volatile uint8_t wpri1 : 2;  // 10: 9
    volatile uint8_t mpp   : 2;  // 12:11
    volatile uint8_t fs    : 2;  // 14:13
    volatile uint8_t xs    : 2;  // 16:15
    volatile uint8_t mprv  : 1;  //    17
    volatile uint8_t sum   : 1;  //    18
    volatile uint8_t mxr   : 1;  //    19
    volatile uint8_t tvm   : 1;  //    20
    volatile uint8_t tw    : 1;  //    21
    volatile uint8_t tsr   : 1;  //    22
    volatile uint8_t wpri3 : 8;  // 30:23
    volatile uint8_t sd    : 1;  //    31
  } volatile clint;
  volatile uint32_t raw;
} __attribute__((packed)) mstatus_t;

typedef union {
  struct {
    volatile uint16_t start_delay      : 15; // 14: 0
    volatile uint16_t rand_start_delay : 1;  //    15
    volatile uint16_t pulse_width      : 13; // 28:16
    volatile uint16_t rand_pulse_width : 1;  //    29
    volatile uint16_t pulse_mode       : 1;  //    30    0 = level, 1 = pulse
    volatile uint16_t value            : 1;  //    31
  } volatile fields;
  volatile uint32_t raw;
}  __attribute__((packed)) debug_req_control_t;

typedef union {
  struct {
    volatile uint16_t prv       : 2;  // 1:0 WARL (0x0, 0x3) PRV. Returns the privilege mode before debug entry.
    volatile uint16_t step      : 1;  // 2 RW STEP. Set to enable single stepping.
    volatile uint16_t nmip      : 1;  // 3 R NMIP. If set, an NMI is pending
    volatile uint16_t mprven    : 1;  // 4 WARL (0x1) MPRVEN. Hardwired to 1.
    volatile uint16_t res_5_5   : 1;  // 5 WARL (0x0) V. Hardwired to 0.
    volatile uint16_t cause     : 3;  // 8:6 R CAUSE. Return the cause of debug entry.
    volatile uint16_t stoptime  : 1;  // 9 WARL (0x0) STOPTIME. Hardwired to 0.
    volatile uint16_t stopcount : 1;  // 10 WARL STOPCOUNT.
    volatile uint16_t stepie    : 1;  // 11 WARL STEPIE. Set to enable interrupts during single stepping.
    volatile uint16_t ebreaku   : 1;  // 12 WARL EBREAKU. Set to enter debug mode on ebreak during user mode.
    volatile uint16_t ebreaks   : 1;  // 13 WARL (0x0) EBREAKS. Hardwired to 0.
    volatile uint16_t res_14_14 : 1;  // 14 WARL (0x0) Hardwired to 0.
    volatile uint16_t ebreakm   : 1;  // 15 RW EBREAKM. Set to enter debug mode on ebreak during machine mode.
    volatile uint16_t ebreakvu  : 1;  // 16 WARL (0x0) EBREAKVU. Hardwired to 0.
    volatile uint16_t ebreakvs  : 1;  // 17 WARL (0x0) EBREAKVS. Hardwired to 0
    volatile uint16_t res_27_18 : 10; // 27:18 WARL (0x0) Reserved
    volatile uint16_t xdebugver : 4;  // 31:28 R (0x4) XDEBUGVER. External debug support exists as described in [RISC-V-DEBUG].
  } volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) dcsr_t;

// ---------------------------------------------------------------
// Global variables
// ---------------------------------------------------------------

// Print verbosity, consider implementing this as a virtual
// peripheral setting to be controlled from UVM.
volatile verbosity_t global_verbosity = V_LOW;

// Global pointer variables
volatile uint32_t * volatile g_has_clic;

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

// ---------------------------------------------------------------
// Prototypes for functions that are test specific and
// perform the debug part of specific tests.
// ---------------------------------------------------------------
//void template_function_dbg(void) __attribute__((section(".debugger"), __noinline__));

// ---------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------
void set_dpc(volatile uint32_t dpc) __attribute__((__noinline__));
void increment_dpc(volatile uint32_t incr_val);
void increment_mepc(volatile uint32_t incr_val);
void set_pmpcfg(pmpsubcfg_t pmpcfg, uint32_t reg_no);
uint32_t set_val(uint32_t * ptr, uint32_t val);
uint32_t incr_val(uint32_t * ptr);
uint32_t has_pmp_configured(void);

// IRQ related
uint32_t detect_irq_mode(void);
void setup_clic(void);
void assert_irq(void);
void deassert_irq(void);
void clint_mie_enable(uint8_t irq_num);
void clint_mie_disable(uint8_t irq_num);

// Debug specific helper code
void disable_debug_req(void) __attribute__((section(".debugger")));


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

/*
 * vp_assert_irq
 *
 * Notify clic_interrupt_agent vp to assert given
 * clic interrupt
 */
void vp_assert_irq(uint32_t mask, uint32_t cycle_delay);

// ---------------------------------------------------------------
// Test entry point
// ---------------------------------------------------------------
int main(int argc, char **argv){

  volatile uint32_t (* volatile tests[NUM_TESTS])(volatile uint32_t, volatile uint8_t);

  volatile uint32_t test_res = 0x1;
  volatile int      retval   = 0;

  // Allocate memory for global pointers here
  g_has_clic = calloc(1, sizeof(uint32_t));

  // Setup clic mtvt if clic is enabled
  *g_has_clic = detect_irq_mode();
  setup_clic();

  // Add function pointers to new tests here
  tests[0]  = dummy; // unused, can be used for env sanity checking

  // Run all tests in list above
  cvprintf(V_LOW, "\nDebug test start\n\n");
  for (volatile uint32_t i = START_TEST_NUM; i < NUM_TESTS; i++) {
    test_res = set_test_status(tests[i](i, (volatile uint32_t)(0)), test_res);
  }

  // Report failures
  retval = get_result(test_res, tests);

  // Free dynamically allocated memory
  free((void *)g_has_clic );

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

// New tests here...

// -----------------------------------------------------------------------------

void disable_debug_req(void) {
  volatile debug_req_control_t debug_req_ctrl;

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 0,
    .fields.pulse_mode       = 0,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 0
  };

  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;
}

// -----------------------------------------------------------------------------

void clint_mie_enable(uint8_t irq_num) {
  __asm__ volatile( R"(
    csrrsi zero, mstatus, 0x8
    csrrs zero, mie, %[bit]
    )"
    : : [bit] "r" (0x1 << irq_num)
  );
}

// -----------------------------------------------------------------------------

void clint_mie_disable(uint8_t irq_num) {
  __asm__ volatile( R"(
    csrrc zero, mie, %[bit]
    )"
    : : [bit] "r" (0x1 << irq_num)
  );
}

// -----------------------------------------------------------------------------

void vp_assert_irq(uint32_t mask, uint32_t cycle_delay) {
  *TIMER_REG_ADDR = mask;
  *TIMER_VAL_ADDR = 1 + cycle_delay;
}

// -----------------------------------------------------------------------------

// Tempate wrapper to support both clic/clint
void assert_irq(void) {
  volatile clic_t clic_vector   = { 0 };
  volatile clint_t clint_vector = { 0 };

  // Use interrupt id 30 for simplicity
  if (*g_has_clic == 1) {
    // clic
    clic_vector = (clic_t){ .fields.irq   = 1,
                            .fields.id    = 30,
                            .fields.level = 81,
                            .fields.priv  = MODE_MACHINE,
                            .fields.shv   = 1
    };
    vp_assert_irq(clic_vector.raw, 2);
  }
  else {
    // clint
    clint_vector.fields.irq_30 = 1;
    vp_assert_irq(clint_vector.raw, 2);
  }
}

// -----------------------------------------------------------------------------

void deassert_irq(void) {
  // Same for clic/clint
  vp_assert_irq(0, 0);
}

// -----------------------------------------------------------------------------

void increment_dpc(volatile uint32_t incr_val) {
  volatile uint32_t dpc = 0;

  __asm__ volatile ( R"(
    csrrs %[dpc], dpc, zero
  )" : [dpc] "=r"(dpc));

  if (incr_val == 0) {
    // No increment specified, check *dpc instruction
    if (((*(uint32_t *)dpc) & 0x3UL) == 0x3UL) {
      // non-compressed
      dpc += 4;
    } else {
      // compressed
      dpc += 2;
    }
  } else {
    // explicitly requested increment
    dpc += incr_val;
  }

  __asm__ volatile ( R"(
    csrrw zero, dpc, %[dpc]
  )" :: [dpc] "r"(dpc));
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

void set_dpc(volatile uint32_t dpc) {
  __asm__ volatile ( R"(
    csrrw zero, dpc, %[dpc]
  )" :: [dpc] "r"(dpc));
  cvprintf(V_MEDIUM, "Setting dpc to %08lx\n", dpc);
}

// -----------------------------------------------------------------------------

uint32_t has_pmp_configured(void) {
  volatile uint32_t pmpaddr0 = 0xffffffff;
  volatile uint32_t pmpaddr0_backup = 0;

  __asm__ volatile (R"(
    csrrw %[pmpaddr0_backup] , pmpaddr0, %[pmpaddr0]
    csrrw %[pmpaddr0], pmpaddr0, %[pmpaddr0_backup]
  )" :[pmpaddr0_backup] "+r"(pmpaddr0_backup),
      [pmpaddr0]        "+r"(pmpaddr0));

  return (pmpaddr0 != 0);
}

// -----------------------------------------------------------------------------

uint32_t __attribute__((__noinline__)) incr_val(uint32_t * ptr) {
  *ptr += 1;
  return *ptr;
}

// -----------------------------------------------------------------------------

uint32_t __attribute__((__noinline__)) set_val(uint32_t * ptr, uint32_t val) {
  *ptr = val;
  return *ptr;
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
