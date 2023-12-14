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
#define NUM_TESTS 21
// Start at 1 (ignore dummy test that is only used for env sanity checking during dev.)
#define START_TEST_NUM 1
// Abort test at first self-check fail, useful for debugging.
#define ABORT_ON_ERROR_IMMEDIATE 0

// Addresses of VP interrupt control registers
#define TIMER_REG_ADDR         ((volatile uint32_t * volatile) (CV_VP_INTR_TIMER_BASE))
#define TIMER_VAL_ADDR         ((volatile uint32_t * volatile) (CV_VP_INTR_TIMER_BASE + 4))
#define DEBUG_REQ_CONTROL_REG *((volatile uint32_t * volatile) (CV_VP_DEBUG_CONTROL_BASE))

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
    volatile uint32_t load    : 1;
    volatile uint32_t store   : 1;
    volatile uint32_t execute : 1;
    volatile uint32_t u       : 1;
    volatile uint32_t s       : 1;
    volatile uint32_t res_5_5 : 1;
    volatile uint32_t m       : 1;
    volatile uint32_t match   : 4;
    volatile uint32_t chain   : 1;
    volatile uint32_t action  : 4;
    volatile uint32_t sizelo  : 2;
    volatile uint32_t timing  : 1;
    volatile uint32_t select  : 1;
    volatile uint32_t hit     : 1;
    volatile uint32_t maskmax : 6;
    volatile uint32_t dmode   : 1;
    volatile uint32_t type    : 4;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) mcontrol_t;

typedef union {
  struct {
    volatile uint32_t load     : 1;
    volatile uint32_t store    : 1;
    volatile uint32_t execute  : 1;
    volatile uint32_t u        : 1;
    volatile uint32_t s        : 1;
    volatile uint32_t res_5_5  : 1;
    volatile uint32_t m        : 1;
    volatile uint32_t match    : 4;
    volatile uint32_t chain    : 1;
    volatile uint32_t action   : 4;
    volatile uint32_t size     : 4;
    volatile uint32_t timing   : 1;
    volatile uint32_t select   : 1;
    volatile uint32_t hit      : 1;
    volatile uint32_t vu       : 1;
    volatile uint32_t vs       : 1;
    volatile uint32_t res_26_25: 2;
    volatile uint32_t dmode    : 1;
    volatile uint32_t type     : 4;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) mcontrol6_t;

typedef union {
  struct {
    volatile uint32_t  action     : 6;
    volatile uint32_t  u          : 1;
    volatile uint32_t  s          : 1;
    volatile uint32_t  res_8_8    : 1;
    volatile uint32_t  m          : 1;
    volatile uint32_t  res_10_10  : 1;
    volatile uint32_t  vu         : 1;
    volatile uint32_t  vs         : 1;
    volatile uint32_t  res_25_13  : 13;
    volatile uint32_t  hit        : 1;
    volatile uint32_t  dmode      : 1;
    volatile uint32_t  type       : 4;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) etrigger_t;

typedef union {
  struct {
    volatile uint32_t info      : 16;
    volatile uint32_t res_23_16 : 8;
    volatile uint32_t version   : 8;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) tinfo_t;

typedef union {
  struct {
    volatile uint32_t uie   : 1;  //     0
    volatile uint32_t sie   : 1;  //     1
    volatile uint32_t wpri  : 1;  //     2
    volatile uint32_t mie   : 1;  //     3
    volatile uint32_t upie  : 1;  //     4
    volatile uint32_t spie  : 1;  //     5
    volatile uint32_t wpri0 : 1;  //     6
    volatile uint32_t mpie  : 1;  //     7
    volatile uint32_t spp   : 1;  //     8
    volatile uint32_t wpri1 : 2;  // 10: 9
    volatile uint32_t mpp   : 2;  // 12:11
    volatile uint32_t fs    : 2;  // 14:13
    volatile uint32_t xs    : 2;  // 16:15
    volatile uint32_t mprv  : 1;  //    17
    volatile uint32_t sum   : 1;  //    18
    volatile uint32_t mxr   : 1;  //    19
    volatile uint32_t tvm   : 1;  //    20
    volatile uint32_t tw    : 1;  //    21
    volatile uint32_t tsr   : 1;  //    22
    volatile uint32_t wpri3 : 8;  // 30:23
    volatile uint32_t sd    : 1;  //    31
  } volatile clint;
  volatile uint32_t raw;
} __attribute__((packed)) mstatus_t;

typedef union {
  struct {
    volatile uint32_t start_delay      : 15; // 14: 0
    volatile uint32_t rand_start_delay : 1;  //    15
    volatile uint32_t pulse_width      : 13; // 28:16
    volatile uint32_t rand_pulse_width : 1;  //    29
    volatile uint32_t pulse_mode       : 1;  //    30    0 = level, 1 = pulse
    volatile uint32_t value            : 1;  //    31
  } volatile fields;
  volatile uint32_t raw;
}  __attribute__((packed)) debug_req_control_t;

typedef union {
  struct {
    volatile uint32_t prv       : 2;  // 1:0 WARL (0x0, 0x3) PRV. Returns the privilege mode before debug entry.
    volatile uint32_t step      : 1;  // 2 RW STEP. Set to enable single stepping.
    volatile uint32_t nmip      : 1;  // 3 R NMIP. If set, an NMI is pending
    volatile uint32_t mprven    : 1;  // 4 WARL (0x1) MPRVEN. Hardwired to 1.
    volatile uint32_t res_5_5   : 1;  // 5 WARL (0x0) V. Hardwired to 0.
    volatile uint32_t cause     : 3;  // 8:6 R CAUSE. Return the cause of debug entry.
    volatile uint32_t stoptime  : 1;  // 9 WARL (0x0) STOPTIME. Hardwired to 0.
    volatile uint32_t stopcount : 1;  // 10 WARL STOPCOUNT.
    volatile uint32_t stepie    : 1;  // 11 WARL STEPIE. Set to enable interrupts during single stepping.
    volatile uint32_t ebreaku   : 1;  // 12 WARL EBREAKU. Set to enter debug mode on ebreak during user mode.
    volatile uint32_t ebreaks   : 1;  // 13 WARL (0x0) EBREAKS. Hardwired to 0.
    volatile uint32_t res_14_14 : 1;  // 14 WARL (0x0) Hardwired to 0.
    volatile uint32_t ebreakm   : 1;  // 15 RW EBREAKM. Set to enter debug mode on ebreak during machine mode.
    volatile uint32_t ebreakvu  : 1;  // 16 WARL (0x0) EBREAKVU. Hardwired to 0.
    volatile uint32_t ebreakvs  : 1;  // 17 WARL (0x0) EBREAKVS. Hardwired to 0
    volatile uint32_t res_27_18 : 10; // 27:18 WARL (0x0) Reserved
    volatile uint32_t xdebugver : 4;  // 31:28 R (0x4) XDEBUGVER. External debug support exists as described in [RISC-V-DEBUG].
  } volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) dcsr_t;

// ---------------------------------------------------------------
// Global variables
// ---------------------------------------------------------------

// Print verbosity, consider implementing this as a virtual
// peripheral setting to be controlled from UVM.
volatile verbosity_t global_verbosity = V_LOW;

volatile uint32_t * volatile g_handler_triggered;
volatile uint32_t * volatile g_illegal_fail;
volatile uint32_t * volatile g_ebreak_fail;
volatile uint32_t * volatile g_expect_illegal;
volatile uint32_t * volatile g_expect_ebreak;
volatile uint32_t * volatile g_expect_dpc;
volatile uint32_t * volatile g_debug_status;
volatile uint32_t * volatile g_debug_status_prev;
volatile uint32_t * volatile g_debug_test_num;
volatile uint32_t * volatile g_minstret_cnt;
volatile uint32_t * volatile g_mcycle_cnt;
volatile uint32_t * volatile g_single_step_status;
volatile uint32_t * volatile g_single_step_status_prev;
volatile uint32_t * volatile g_single_step_cnt;
volatile uint32_t * volatile g_previous_dpc;
volatile uint32_t * volatile g_expect_irq;
volatile uint32_t * volatile g_unexpected_irq;
volatile uint32_t * volatile g_trigger_matched;
volatile uint32_t * volatile g_has_clic;
volatile uint32_t * volatile g_single_step_unspec_err;

volatile uint32_t            g_pushpop_area [64];

extern volatile uint32_t *trigger_loc;
extern volatile uint32_t *trigger_loc_dbg;
extern volatile uint32_t *trigger_exit;
extern volatile uint32_t mtvt_table;

// Message strings for use in assembly printf
const volatile char * const volatile entered_exc_handler_msg = "Entered handler";
const volatile char * const volatile entered_dbg_msg = "Entered debug";
const volatile char * const volatile ebreak_msg = "Ebreak\n";
const volatile char * const volatile dbg_exception = "Exception occurred in debug\n";

const volatile char * const volatile test_str = "Test number = %0d\n";
const volatile char * const volatile test_status_msg = "Test status = %0d\n";
const volatile char * const volatile debug_exit_msg = "Exiting debug, test_num = %0d\n";

// ---------------------------------------------------------------
// Entry and exit locations for debug
// ---------------------------------------------------------------
void _debugger_start(void) __attribute__((section(".debugger")));
void _debugger_restore_stack(void) __attribute__((section(".debugger")));
void _debugger_end(void) __attribute__((section(".debugger")));

// ---------------------------------------------------------------
// Interrupt/Exception handler related functions
// ---------------------------------------------------------------
void u_sw_irq_handler(void) __attribute__((naked));
void check_irq_handler(void);
void u_sw_irq_handler_default(void);
void m_fast14_irq_handler(void) __attribute__((naked));
// Mtvt table implementation
void mtvt_code(void) __attribute__((naked));

// Debug exceptions
void _debugger_exception(void) __attribute__((section(".debugger_exception")));
void debug_exception_handler(void) __attribute__((section(".debugger_exception"), __noinline__));

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
uint32_t debug_csr_rw(uint32_t index, uint8_t report_name);
uint32_t trigger_default_val(uint32_t index, uint8_t report_name);
uint32_t ebreak_behavior_m_mode(uint32_t index, uint8_t report_name);
uint32_t request_hw_debugger(uint32_t index, uint8_t report_name);
uint32_t request_ebreak_3x(uint32_t index, uint8_t report_name);
uint32_t csr_access_default_val(uint32_t index, uint8_t report_name);
uint32_t mmode_ebreakm_ebreak_executes_debug_code(uint32_t index, uint8_t report_name);
uint32_t illegal_csr_in_dmode(uint32_t index, uint8_t report_name);
uint32_t ecall_in_dmode(uint32_t index, uint8_t report_name);
uint32_t mret_in_dmode(uint32_t index, uint8_t report_name);
uint32_t exception_enters_debug_mode(uint32_t index, uint8_t report_name);
uint32_t dret_in_mmode(uint32_t index, uint8_t report_name);
uint32_t wfi_before_dmode(uint32_t index, uint8_t report_name);
uint32_t check_irq(uint32_t index, uint8_t report_name);
uint32_t check_stopcnt_bits(uint32_t index, uint8_t report_name);
uint32_t single_step(uint32_t index, uint8_t report_name);
uint32_t mprv_dret_to_umode(uint32_t index, uint8_t report_name);
uint32_t cover_known_iss_mismatches(uint32_t index, uint8_t report_name);
uint32_t push_haltreq(uint32_t index, uint8_t report_name);
uint32_t pop_haltreq(uint32_t index, uint8_t report_name);

// ---------------------------------------------------------------
// Prototypes for functions that are test specific and
// perform the debug part of specific tests.
// ---------------------------------------------------------------
void request_hw_debugger_dbg(void) __attribute__((section(".debugger"), __noinline__));
void request_ebreak_3x_dbg(void) __attribute__((section(".debugger"), __noinline__));
void mmode_ebreakm_ebreak_executes_debug_code_dbg(void) __attribute__((section(".debugger"), __noinline__));
void illegal_csr_in_dmode_dbg(void) __attribute__((section(".debugger"), __noinline__));
void ecall_in_dmode_dbg(void) __attribute__((section(".debugger"), __noinline__));
void mret_in_dmode_dbg(void) __attribute__((section(".debugger"), __noinline__));
void exception_enters_debug_mode_dbg(void) __attribute__((section(".debugger"), __noinline__));
void wfi_before_dmode_dbg(void) __attribute__((section(".debugger"), __noinline__));
void check_stopcnt_bits_dbg(void) __attribute__((section(".debugger"), __noinline__));
void single_step_dbg(void) __attribute__((section(".debugger"), __noinline__));
void single_step_trigger_setup_dbg(void) __attribute__((section(".debugger"), __noinline__));
void single_step_stepie_enable_dbg(void) __attribute__((section(".debugger"), __noinline__));
void single_step_stepie_disable_dbg(void) __attribute__((section(".debugger"), __noinline__));
void single_step_c_ebreak_dbg(void) __attribute__((section(".debugger"), __noinline__));
void single_step_ebreak_dbg(void) __attribute__((section(".debugger"), __noinline__));
void single_step_c_ebreak_exception_dbg(void) __attribute__((section(".debugger"), __noinline__));
void single_step_ebreak_exception_dbg(void) __attribute__((section(".debugger"), __noinline__));
void csr_access_default_val_dbg(void) __attribute__((section(".debugger"), __noinline__));
void single_step_basic_dbg(void) __attribute__((section(".debugger"), __noinline__));

// The following could also be placed in the debug region, but there is simply no space
// unless we go about changing the core-v-verif memory map
void single_step_trigger_entry_dbg(void) __attribute__((__noinline__));
void cover_known_iss_mismatches_dbg(void) __attribute__((__noinline__));
void single_step_enable_dbg(void) __attribute__((__noinline__));
void single_step_disable_dbg(void) __attribute__((__noinline__));
void mprv_dret_to_umode_dbg(void) __attribute__((__noinline__));
void exception_status_dbg(void) __attribute__((__noinline__));
void ebreakm_set_dbg(void);

// ---------------------------------------------------------------
// Single step test code (non-debug section
// ---------------------------------------------------------------
void single_step_code(void);


// ---------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------
void print_tdata1(verbosity_t verbosity, volatile tdata1_t * volatile tdata1);
void set_dpc(volatile uint32_t dpc) __attribute__((__noinline__));
void increment_dpc(volatile uint32_t incr_val);
void increment_mepc(volatile uint32_t incr_val);
void set_debug_status(volatile uint32_t status);
void set_single_step_status(volatile uint32_t status);
void set_mseccfg(mseccfg_t mseccfg);
void set_pmpcfg(pmpsubcfg_t pmpcfg, uint32_t reg_no);
uint32_t set_val(uint32_t * ptr, uint32_t val);
uint32_t incr_val(uint32_t * ptr);
uint32_t has_pmp_configured(void);

// Single step test related
void single_step_fail(uint32_t cause);
int get_single_step_result(uint32_t res);
void print_single_step_status(void);
void increment_single_step_status(void);

// IRQ related
uint32_t detect_irq_mode(void);
void setup_clic(void);
void assert_irq(void);
void deassert_irq(void);
void wait_irq(void);
void clint_mie_enable(uint8_t irq_num);
void clint_mie_disable(uint8_t irq_num);

// Debug specific helper code
void disable_debug_req(void) __attribute__((section(".debugger")));
uint32_t get_dcsr_cause(void) __attribute__((section(".debugger"),__noinline__));


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

  g_handler_triggered       = calloc(1, sizeof(uint32_t));
  g_illegal_fail            = calloc(1, sizeof(uint32_t));
  g_ebreak_fail             = calloc(1, sizeof(uint32_t));
  g_expect_illegal          = calloc(1, sizeof(uint32_t));
  g_expect_ebreak           = calloc(1, sizeof(uint32_t));
  g_expect_dpc              = calloc(1, sizeof(uint32_t));
  g_debug_status            = calloc(1, sizeof(uint32_t));
  g_debug_status_prev       = calloc(1, sizeof(uint32_t));
  g_debug_test_num          = calloc(1, sizeof(uint32_t));
  g_mcycle_cnt              = calloc(1, sizeof(uint32_t));
  g_minstret_cnt            = calloc(1, sizeof(uint32_t));
  g_single_step_status      = calloc(1, sizeof(uint32_t));
  g_single_step_status_prev = calloc(1, sizeof(uint32_t));
  g_single_step_cnt         = calloc(1, sizeof(uint32_t));
  g_previous_dpc            = calloc(1, sizeof(uint32_t));
  g_expect_irq              = calloc(1, sizeof(uint32_t));
  g_unexpected_irq          = calloc(1, sizeof(uint32_t));
  g_trigger_matched         = calloc(1, sizeof(uint32_t));
  g_has_clic                = calloc(1, sizeof(uint32_t));
  g_single_step_unspec_err  = calloc(1, sizeof(uint32_t));

  // Setup clic mtvt if clic is enabled
  *g_has_clic = detect_irq_mode();
  setup_clic();

  // Add function pointers to new tests here
  tests[0] = dummy; // unused, can be used for env sanity checking
  tests[1]  = debug_csr_rw;
  tests[2]  = trigger_default_val;
  tests[3]  = ebreak_behavior_m_mode;
  tests[4]  = request_hw_debugger;
  tests[5]  = request_ebreak_3x;
  tests[6]  = csr_access_default_val;
  tests[7]  = mmode_ebreakm_ebreak_executes_debug_code;
  tests[8]  = illegal_csr_in_dmode;
  tests[9]  = ecall_in_dmode;
  tests[10] = mret_in_dmode;
  tests[11] = exception_enters_debug_mode;
  tests[12] = dret_in_mmode;
  tests[13] = wfi_before_dmode;
  tests[14] = check_irq;
  tests[15] = check_stopcnt_bits;
  tests[16] = single_step;
  tests[17] = mprv_dret_to_umode;
  tests[18] = cover_known_iss_mismatches;
  tests[19] = push_haltreq;
  tests[20] = pop_haltreq;

  // Run all tests in list above
  cvprintf(V_LOW, "\nDebug test start\n\n");
  for (volatile uint32_t i = START_TEST_NUM; i < NUM_TESTS; i++) {
    test_res = set_test_status(tests[i](i, (volatile uint32_t)(0)), test_res);
  }

  // Report failures
  retval = get_result(test_res, tests);

  free((void *)g_handler_triggered      );
  free((void *)g_illegal_fail           );
  free((void *)g_ebreak_fail            );
  free((void *)g_expect_illegal         );
  free((void *)g_expect_ebreak          );
  free((void *)g_expect_dpc             );
  free((void *)g_debug_status           );
  free((void *)g_debug_status_prev      );
  free((void *)g_debug_test_num         );
  free((void *)g_mcycle_cnt             );
  free((void *)g_minstret_cnt           );
  free((void *)g_single_step_status     );
  free((void *)g_single_step_status_prev);
  free((void *)g_single_step_cnt        );
  free((void *)g_expect_irq             );
  free((void *)g_unexpected_irq         );
  free((void *)g_trigger_matched        );
  free((void *)g_has_clic               );
  free((void *)g_single_step_unspec_err );

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

int get_single_step_result(uint32_t res) {
  for (volatile int i = 0; i < 20; i++) {
    if ((res >> (i)) & 0x1) {
      cvprintf (V_LOW, "Single step section %0d FAILED\n", i);
    }
  }

  cvprintf(V_LOW, "Stepped %0d instructions\n", *g_single_step_cnt);
  return (res == 0 ? 1 : 0);
}

// -----------------------------------------------------------------------------

void print_tdata1(verbosity_t verbosity, volatile tdata1_t * volatile tdata1){
  volatile mcontrol_t  * volatile mcontrol;
  volatile mcontrol6_t * volatile mcontrol6;
  volatile etrigger_t  * volatile etrigger;

  mcontrol  = (mcontrol_t *)  tdata1;
  mcontrol6 = (mcontrol6_t *) tdata1;
  etrigger  = (etrigger_t *)  tdata1;

  switch (tdata1->fields.type) {
    case 0:
      cvprintf(verbosity, "Type: 0x%0x, dmode: 0x%0x, action: 0x%0x\n",
        tdata1->fields.type,
        tdata1->fields.dmode,
        tdata1->fields.data);
      break;
    case 2:
      cvprintf(verbosity, "Type: 0x%0x, dmode: 0x%0x, maskmax: 0x%0x, hit: 0x%0x, select: 0x%0x, "
                        "timing: 0x%0x, sizelo: 0x%0x, action: 0x%0x, chain: 0x%0x, match: 0x%0x, "
                        "m: 0x%0x, zero: 0x%0x, s: 0x%0x, u: 0x%0x, execute: 0x%0x, store: 0x%0x, load: 0x%0x\n",
        mcontrol->fields.type,
        mcontrol->fields.dmode,
        mcontrol->fields.maskmax,
        mcontrol->fields.hit,
        mcontrol->fields.select,
        mcontrol->fields.timing,
        mcontrol->fields.sizelo,
        mcontrol->fields.action,
        mcontrol->fields.chain,
        mcontrol->fields.match,
        mcontrol->fields.m,
        mcontrol->fields.res_5_5,
        mcontrol->fields.s,
        mcontrol->fields.u,
        mcontrol->fields.execute,
        mcontrol->fields.store,
        mcontrol->fields.load);
      break;
    case 5:
      cvprintf(verbosity, "Type: 0x%0x, dmode: 0x%0x, hit: 0x%0x, zero: 0x%0x, vs: 0x%0x, vu: 0x%0x "
                        "zero: 0x%0x, m: 0x%0x, zero: 0x%0x, s: 0x%0x, u: 0x%0x, action: 0x%0x\n",
        etrigger->fields.type,
        etrigger->fields.dmode,
        etrigger->fields.hit,
        etrigger->fields.res_25_13,
        etrigger->fields.vs,
        etrigger->fields.vu,
        etrigger->fields.res_10_10,
        etrigger->fields.m,
        etrigger->fields.res_8_8,
        etrigger->fields.s,
        etrigger->fields.u,
        etrigger->fields.action);
      break;
    case 6:
      cvprintf(verbosity, "Type: 0x%0x, dmode: 0x%0x, zero: 0x%0x, vs: 0x%0x, vu: 0x%0x, hit: 0x%0x, "
                        "select: 0x%0x, timing: 0x%0x, size: 0x%0x, action: 0x%0x, chain: 0x%0x, "
                        "match: 0x%0x, m: 0x%0x, zero: 0x%0x, s: 0x%0x, u: 0x%0x, execute: 0x%0x, "
                        "store: 0x%0x, load: 0x%0x\n",
        mcontrol6->fields.type,
        mcontrol6->fields.dmode,
        mcontrol6->fields.res_26_25,
        mcontrol6->fields.vs,
        mcontrol6->fields.vu,
        mcontrol6->fields.hit,
        mcontrol6->fields.select,
        mcontrol6->fields.timing,
        mcontrol6->fields.size,
        mcontrol6->fields.action,
        mcontrol6->fields.chain,
        mcontrol6->fields.match,
        mcontrol6->fields.m,
        mcontrol6->fields.res_5_5,
        mcontrol6->fields.s,
        mcontrol6->fields.u,
        mcontrol6->fields.execute,
        mcontrol6->fields.store,
        mcontrol6->fields.load);
      break;
    case 15:
      cvprintf(verbosity, "Type: 0x%0x, dmode: 0x%0x, action: 0x%0x\n",
        tdata1->fields.type,
        tdata1->fields.dmode,
        tdata1->fields.data);
      break;
  }
}

// -----------------------------------------------------------------------------

uint32_t dummy(uint32_t index, uint8_t report_name) {
  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t debug_csr_rw(uint32_t index, uint8_t report_name) {

  volatile uint8_t test_fail = 0;
  volatile uint32_t temp = 0xFFFFFFFF;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // ------------------------------------------------------------
  cvprintf(V_MEDIUM, "\nChecking write access in M-mode\n");
  // ------------------------------------------------------------
  // DCSR
  *g_expect_illegal = 1;
  __asm__ volatile ( R"( csrrw zero, dcsr, %[temp])" : : [temp] "r" (temp) :);
  test_fail += *g_illegal_fail;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  // DPC
  *g_expect_illegal = 1;
  __asm__ volatile ( R"( csrrw zero, dpc, %[temp])" : : [temp] "r" (temp) :);
  test_fail += *g_illegal_fail;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  // DSCRATCH0
  *g_expect_illegal = 1;
  __asm__ volatile ( R"( csrrw zero, dscratch0, %[temp])" : : [temp] "r" (temp) :);
  test_fail += *g_illegal_fail;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  // DSCRATCH1
  *g_expect_illegal = 1;
  __asm__ volatile ( R"( csrrw zero, dscratch1, %[temp])" : : [temp] "r" (temp) :);
  test_fail += *g_illegal_fail;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  // ------------------------------------------------------------
  cvprintf(V_MEDIUM, "\nChecking read access in M-mode\n");
  // ------------------------------------------------------------

  // DCSR
  *g_expect_illegal = 1;
  __asm__ volatile ( R"( csrrs %[temp], dcsr, zero)" : [temp] "=r" (temp) : :);
  test_fail += *g_illegal_fail;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  // DPC
  *g_expect_illegal = 1;
  __asm__ volatile ( R"( csrrs %[temp], dpc, zero)" : [temp] "=r" (temp) : :);
  test_fail += *g_illegal_fail;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  // DSCRATCH0
  *g_expect_illegal = 1;
  __asm__ volatile ( R"( csrrs %[temp], dscratch0, zero)" : [temp] "=r" (temp) : :);
  test_fail += *g_illegal_fail;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  // DSCRATCH1
  *g_expect_illegal = 1;
  __asm__ volatile ( R"( csrrs %[temp], dscratch1, zero)" : [temp] "=r" (temp) : :);
  test_fail += *g_illegal_fail;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);


  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;

}

// -----------------------------------------------------------------------------

uint32_t trigger_default_val(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile uint32_t readback_val;

  volatile uint32_t tdata1_bits;
  volatile tdata1_t * volatile tdata1;
  volatile tinfo_t * volatile tinfo;

  // Below are volatile for type consistency, ideally should be declared as const
  volatile tinfo_t tinfo_reset = {
    .fields.version = 0x1,
    .fields.info    = 0x8064
  };

  volatile tdata1_t tdata1_reset = {
    .fields.type  = 2,
    .fields.dmode = 1,
    .fields.data  = 0x1000
  };

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // tselect default value
  __asm__ volatile ( R"( csrrs %[tselect], tselect, zero )" : [tselect] "=r"(readback_val) : : );
  test_fail += (readback_val != 0);
  if (ABORT_ON_ERROR_IMMEDIATE) { assert(test_fail == 0); }

  // tdata1 default value
  __asm__ volatile ( R"( csrrs %[tdata1], tdata1, zero)" : [tdata1] "=r"(tdata1_bits) : :);

  tdata1 = (tdata1_t *)&tdata1_bits;

  test_fail += !(tdata1->raw == tdata1_reset.raw);

  if (ABORT_ON_ERROR_IMMEDIATE) {
    assert(test_fail == 0);
  }
  if (test_fail) {
    cvprintf(V_MEDIUM, "Got: ");
    print_tdata1(V_MEDIUM, tdata1);
    cvprintf(V_MEDIUM, "Exp: ");
    print_tdata1(V_MEDIUM, &tdata1_reset);
  }

  // tdata2 default value
  __asm__ volatile ( R"( csrrs %[tdata2], tdata2, zero )" : [tdata2] "=r"(readback_val) : : );
  test_fail += (readback_val != 0);
  if (ABORT_ON_ERROR_IMMEDIATE) { assert(test_fail == 0); }
  if (test_fail) {
    cvprintf(V_MEDIUM, "tdata2 exp: 0x0, got: 0x%0x\n", readback_val);
  }

  // tinfo default value
  __asm__ volatile ( R"( csrrs %[tinfo], tinfo, zero )" : [tinfo] "=r"(readback_val) : : );
  tinfo = (void *)&readback_val;
  test_fail += (  tinfo->fields.info      != tinfo_reset.fields.info
               || tinfo->fields.res_23_16 != 0
               || tinfo->fields.version   != tinfo_reset.fields.version);
  if (ABORT_ON_ERROR_IMMEDIATE) { assert(test_fail == 0); }
  if (test_fail) {
    cvprintf(V_MEDIUM, "tinfo exp: info: 0x%0x, zero: 0x%0x, version: 0x%0x, got: info: 0x%0x, zero: 0x%0x, version: 0x%0x\n",
           tinfo_reset.fields.info, tinfo_reset.fields.res_23_16, tinfo_reset.fields.version,
           tinfo->fields.info, tinfo->fields.res_23_16, tinfo->fields.version);
  }

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;

}

// -----------------------------------------------------------------------------

uint32_t ebreak_behavior_m_mode(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_handler_triggered = 0;
  *g_expect_ebreak     = 1;

  __asm__ volatile ( R"(
    .option push
    .option norvc
    ebreak
    .option pop
  )");
  test_fail += (*g_ebreak_fail || !*g_handler_triggered);
  if (ABORT_ON_ERROR_IMMEDIATE) { assert(test_fail == 0); }
  if (*g_ebreak_fail) {
    cvprintf(V_MEDIUM, "ebreak behavior incorrect\n");
  }
  *g_ebreak_fail = 0;

  *g_handler_triggered = 0;
  *g_expect_ebreak     = 1;
  __asm__ volatile ( R"( c.ebreak )" :::);
  test_fail += (*g_ebreak_fail || !*g_handler_triggered);
  if (ABORT_ON_ERROR_IMMEDIATE) { assert(test_fail == 0); }
  if (*g_ebreak_fail) {
    cvprintf(V_MEDIUM, "c.ebreak behavior incorrect\n");
  }

  *g_ebreak_fail       = 0;
  *g_handler_triggered = 0;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t request_hw_debugger(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 200
  };

  *g_debug_test_num = 1;
  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;
  while (!*g_debug_status) {
    ;;
  }

  test_fail += *g_debug_status > 1 ? 1 : 0;
  *g_debug_status = 0;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t request_ebreak_3x(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 200
  };

  *g_debug_status = 0;
  *g_debug_test_num = 2;
  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  while (*g_debug_status < 3) {
    ;;
  }
  if (*g_debug_status != *g_debug_status_prev) {
    cvprintf(V_MEDIUM, "Debug status: %0ld\n", *g_debug_status);
  }
  *g_debug_status_prev = *g_debug_status;

  test_fail += *g_debug_status == 4 ? 0 : 1;
  *g_debug_status = 0;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t push_haltreq(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 15
  };

  *g_debug_test_num = 19;
  *g_debug_status = 0;
  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  __asm__ volatile(
    R"(
      # Save old "sp"
      mv t0, sp

      # Setup temporary "sp"
      la sp, g_pushpop_area
      addi sp, sp, 64

      # Push to temporary "sp"
      cm.push {x1, x8-x9, x18-x27}, -64

      # Restore old "sp"
      mv sp, t0
    )"::: "t0"
  );

  test_fail += *g_debug_status == 1 ? 0 : 1;
  *g_debug_status = 0;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}


// -----------------------------------------------------------------------------

uint32_t pop_haltreq(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 25
  };

  *g_debug_test_num = 20;
  *g_debug_status = 0;
  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  __asm__ volatile(
    R"(
        # Save old "sp" and GPRs
      cm.push {x1, x8-x9}, -16
      mv t0, sp

      # Setup temporary "sp"
      la sp, g_pushpop_area

      # Pop from temporary "sp"
      cm.pop {x1, x8-x9, x18-x27}, 64

      # Restore old "sp" and GPRs
      mv sp, t0
      cm.pop {x1, x8-x9}, 16
    )"::: "t0"
  );

  test_fail += *g_debug_status == 1 ? 0 : 1;
  *g_debug_status = 0;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}
// -----------------------------------------------------------------------------

__attribute__((naked)) void m_fast14_irq_handler(void) {

  __asm__ volatile ( R"(

    # Push saved regs and allocate space for the remaining 16 regs
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

    # Get test number
    lw s1, g_debug_test_num
    lw s1, 0(s1)

    addi s0, zero, 11
    bne s0, s1, 1f
    lw s0, g_debug_status
    lw s1, 0(s0)
    addi s1, zero, 1
    sw s1, 0(s0)

    1:

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

// ---------------------------------------------------------------

__attribute__((naked)) void u_sw_irq_handler(void) {

  __asm__ volatile ( R"(
    # Push saved regs and allocate space for the remaining 16 regs
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

    # Get test number
    lw s1, g_debug_test_num
    lw s1, 0(s1)

    # Jump to test specific code
    addi s0, zero, 8
    beq s0, s1, 8f
    addi s0, zero, 9
    beq s0, s1, 9f
    addi s0, zero, 11
    beq s0, s1, 11f

    beq zero, zero, 98f

    8:
    c.ebreak
    beq zero, zero, 99f

    9:
    lw s1, g_debug_status
    lw s0, 0(s1)
    addi s0, zero, 1
    sw s0, 0(s1)
    beq zero, zero, 99f

    11:
    call check_irq_handler
    beq zero, zero, 99f

    98:
    call u_sw_irq_handler_default
    beq zero, zero, 99f # Added to prevent omission if adding further cases

    99:
    # increment mepc by appropriate amount
    add a0, zero, zero
    call increment_mepc

    # set g_handler_triggered
    lw s0, g_handler_triggered
    addi s1, zero, 1
    sw s1, 0(s0)

    # clear g_expect_ebreak
    lw s0, g_expect_ebreak
    addi s1, zero, 0
    sw s1, 0(s0)

    # clear g_expect_illegal
    lw s0, g_expect_illegal
    addi s1, zero, 0
    sw s1, 0(s0)

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

// ---------------------------------------------------------------

void u_sw_irq_handler_default(void) {
  volatile mcause_t mcause = { 0 };

  // Fields to clear;
  // Exists in both clic and clint, no need to have
  // special consideration for clic/clint.
  // Clearing all bits as for clint would break clic
  // mpp behavior
  mcause.clic.interrupt = 0x1;
  mcause.clic.exccode = 0x7FF;

  __asm__ volatile ( R"(
     csrrc %[mc], mcause, %[mc]
     )"
     : [mc] "=r"(mcause.raw)
     :
  );

  if (mcause.clint.interrupt == 0 || mcause.clic.interrupt == 0) {
    if (mcause.clint.exccode == MCAUSE_ILLEGAL || mcause.clic.exccode == MCAUSE_ILLEGAL) {
      if (!*g_expect_illegal) {
        *g_illegal_fail = 1;
      }
    }
    else if (mcause.clint.exccode == MCAUSE_BREAKPT || mcause.clic.exccode == MCAUSE_BREAKPT) {
      if (!*g_expect_ebreak) {
        *g_ebreak_fail = 1;
      }
    }
    else {
      if (*g_expect_illegal) {
        *g_illegal_fail = 1;
      }
      if (*g_expect_ebreak) {
        *g_ebreak_fail = 1;
      }
    }
  }
  return;
}

// -----------------------------------------------------------------------------

// Main debug code, note that all test sections triggered inside
// this function are suffixed with _dbg.
void __attribute__((naked)) _debugger_start(void) {
  __asm__ volatile ( R"(

    # Setup debug stack and save sp, gp
    csrrw zero, dscratch0, sp
    1:auipc sp, %pcrel_hi(__debugger_stack_start)
    addi sp, sp, %pcrel_lo(1b)

    # Push saved regs and allocate space for the remaining 16 regs
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

    # Save mcycle/minstret
    csrrs s0, mcycle, zero
    lw s1, g_mcycle_cnt
    sw s0, 0(s1)

    csrrs s0, minstret, zero
    lw s1, g_minstret_cnt
    sw s0, 0(s1)

    call disable_debug_req

    # Get current test number
    addi s1, zero, 0
    addi s0, zero, 0
    lw s1, g_debug_test_num
    lw s1, 0(s1)

    # Jump to correct test
    addi s0, zero, 1
    beq s0, s1, 1f
    addi s0, zero, 2
    beq s0, s1, 2f
    addi s0, zero, 3
    beq s0, s1, 3f
    addi s0, zero, 4
    beq s0, s1, 4f
    addi s0, zero, 5
    beq s0, s1, 5f
    addi s0, zero, 6
    beq s0, s1, 6f
    addi s0, zero, 7
    beq s0, s1, 7f
    addi s0, zero, 8
    beq s0, s1, 8f
    addi s0, zero, 10
    beq s0, s1, 10f
    addi s0, zero, 12
    beq s0, s1, 12f
    addi s0, zero, 13
    beq s0, s1, 13f
    addi s0, zero, 14
    beq s0, s1, 14f
    addi s0, zero, 18
    beq s0, s1, 18f
    addi s0, zero, 19
    beq s0, s1, 19f
    addi s0, zero, 20
    beq s0, s1, 20f

    # no match, exit
    beq zero, zero, 99f

    1: call request_hw_debugger_dbg
    beq zero, zero, 99f

    2: call request_ebreak_3x_dbg
    beq zero, zero, 99f

    3: call csr_access_default_val_dbg
    beq zero, zero, 99f

    4: call mmode_ebreakm_ebreak_executes_debug_code_dbg
    beq zero, zero, 99f

    5: call illegal_csr_in_dmode_dbg
    beq zero, zero, 99f

    6: call ecall_in_dmode_dbg
    beq zero, zero, 99f

    7: call mret_in_dmode_dbg
    beq zero, zero, 99f

    8: call exception_enters_debug_mode_dbg
    beq zero, zero, 99f

    10: call wfi_before_dmode_dbg
    beq zero, zero, 99f

    12: call check_stopcnt_bits_dbg
    beq zero, zero, 99f

    13: call single_step_dbg
    beq zero, zero, 99f

    14: call mprv_dret_to_umode_dbg
    beq zero, zero, 99f

    18: call cover_known_iss_mismatches_dbg
    beq zero, zero, 99f

    19: call request_hw_debugger_dbg
    beq zero, zero, 99f

    20: call request_hw_debugger_dbg
    beq zero, zero, 99f

    99: call _debugger_end
    dret

  )");
}

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

void __attribute__((__noinline__)) request_hw_debugger_dbg(void) {
  volatile dcsr_t dcsr;

  __asm__ volatile ( R"( csrrs %[dcsr], dcsr, zero)" : [dcsr] "=r"(dcsr.raw) : : );
  cvprintf(V_MEDIUM, "dcsr cause: %0x\n", dcsr.fields.cause);

  if (dcsr.fields.cause != DCAUSE_HALTREQ) {
    *g_debug_status = 99;
  } else {
    *g_debug_status = 1;
  }

}

// -----------------------------------------------------------------------------

void __attribute__((naked)) request_ebreak_3x_dbg(void) {
  __asm__ volatile ( R"(
    call get_dcsr_cause
    add s2, zero, a0

    addi s3, zero, 3
    bne s2, s3, 1f

    lw s4, g_debug_status
    add a0, s4, zero
    call incr_val
    sw a0, 0(s4)

    beq zero, zero, 2f

    1:
    lw a0, g_debug_status
    addi a1, zero, 99
    call set_val
    add s4, a0, zero

    2:
    lw s4, 0(s4)
    # switch(g_debug_status)
    # case 1:
    addi s5, zero, 1
    beq s4, s5, 1f

    # case 2:
    addi s5, zero, 2
    beq s4, s5, 2f

    # case 3:
    addi s5, zero, 3
    beq s4, s5, 1f

    # default:
    beq zero, zero, 3f

    1:
    # pop stack

    ### la s5, e2
    1:auipc s5, %pcrel_hi(e1)
    addi s5, s5, %pcrel_lo(1b)
    csrrw zero, dscratch1, s5

    ### jal zero, _debugger_restore_stack
    99: auipc s11, %pcrel_hi(_debugger_restore_stack)
    addi s11, s11, %pcrel_lo(99b)
    jalr zero, 0(s11)

    e1: csrrw s5, dscratch1, zero

    # force uncompressed ebreak
    .option push
    .option norvc
    ebreak
    .option pop

    2:
    addi s5, zero, 2
    bne s4, s5, 1f

    # pop stack

    ### la s5, e2
    1:auipc s5, %pcrel_hi(e2)
    addi s5, s5, %pcrel_lo(1b)

    csrrw zero, dscratch1, s5

    ### j _debugger_restore_stack
    99: auipc s11, %pcrel_hi(_debugger_restore_stack)
    addi s11, s11, %pcrel_lo(99b)
    jalr zero, 0(s11)

    e2: csrrw s5, dscratch1, zero

    c.ebreak

    # return if we are done
    3:
    csrrw zero, dscratch1, zero
    99: auipc s11, %pcrel_hi(_debugger_end)
    addi s11, s11, %pcrel_lo(99b)
    jalr zero, 0(s11)

  )");
}

// -----------------------------------------------------------------------------

// Csr access test entry
uint32_t csr_access_default_val(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_debug_status   = 0;
  *g_debug_test_num = 3;

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 200
  };

  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  while (*g_debug_status == 0) {
    ;;
  }

  test_fail += (*g_debug_status == 1) ? 0 : 1;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

// Debug portion of csr access test
void csr_access_default_val_dbg(void) {
  volatile uint32_t mvendorid;
  volatile uint32_t marchid;
  volatile uint32_t mimpid;
  volatile uint32_t mhartid;
  volatile uint32_t mstatus;
  volatile uint32_t misa;
  volatile uint32_t mie;
  volatile uint32_t mtvec;
  volatile uint32_t mtval;
  volatile uint32_t mscratch;
  volatile uint32_t mepc;
  volatile uint32_t mcause;
  volatile uint32_t mip;
  volatile dcsr_t dcsr;
  volatile dcsr_t dcsr_default;
  volatile uint32_t dpc;
  volatile uint32_t tdata1;
  volatile uint32_t tdata2;

  __asm__ volatile ( R"(
    # access
    csrrs %[mvendorid], mvendorid, zero
    csrrs %[marchid], marchid, zero
    csrrs %[mimpid], mimpid, zero
    csrrs %[mhartid], mhartid, zero
    csrrs %[mstatus], mstatus, zero
    csrrs %[misa], misa, zero
    csrrs %[mie], mie, zero
    csrrs %[mtvec], mtvec, zero
    csrrs %[mtval], mtval, zero
    csrrs %[mscratch], mscratch, zero
    csrrs %[mepc], mepc, zero
    csrrs %[mcause], mcause, zero
    csrrs %[mip], mip, zero

    # default values
    csrrs %[dcsr], dcsr, zero
    csrrs %[dpc], dpc, zero
    csrrs %[tdata1], tdata1, zero
    csrrs %[tdata2], tdata2, zero
  )"
  : [mvendorid] "=r"(mvendorid),
    [marchid]   "=r"(marchid),
    [mimpid]    "=r"(mimpid),
    [mhartid]   "=r"(mhartid),
    [mstatus]   "=r"(mstatus),
    [misa]      "=r"(misa),
    [mie]       "=r"(mie),
    [mtvec]     "=r"(mtvec),
    [mtval]     "=r"(mtval),
    [mscratch]  "=r"(mscratch),
    [mepc]      "=r"(mepc),
    [mcause]    "=r"(mcause),
    [mip]       "=r"(mip),
    [dcsr]      "=r"(dcsr.raw),
    [dpc]       "=r"(dpc),
    [tdata1]    "=r"(tdata1),
    [tdata2]    "=r"(tdata2)
  ::);

  dcsr_default.raw = 0x00000000;
  dcsr_default = (dcsr_t){
    .fields.xdebugver = 4,
    .fields.stopcount = 1,
    .fields.cause     = DCAUSE_HALTREQ,
    .fields.mprven    = 1,
    .fields.prv       = MODE_MACHINE };

  if (dcsr.raw != dcsr_default.raw) {
    cvprintf(V_MEDIUM, "dcsr default value wrong, expected: 0x%08lx, got 0x%08lx\n", dcsr.raw, dcsr_default.raw);
    *g_debug_status = 99;
  }

  if (dpc == 0x00000000) {
    cvprintf(V_MEDIUM, "dpc should not be zero\n");
    *g_debug_status = 99;
  }

  dcsr.raw = 0x00000000;

  dcsr = (dcsr_t){
    .fields.xdebugver = 4,
    .fields.cause     = DCAUSE_HALTREQ,
    .fields.prv       = MODE_MACHINE,
    .fields.ebreakm   = 1
  };

  // Enable ebreakm
  __asm__ volatile ( R"(
    csrrw zero, dcsr, %[dcsr]
    csrrw zero, dscratch1, zero
  )"
     : [dcsr] "=r"(dcsr.raw)
  ::);

  if (*g_debug_status != 99) {
    *g_debug_status = 1;
  }
}

// -----------------------------------------------------------------------------

// Test ebreak entry to debug mode, flags that we successfully
// entered debug.
void mmode_ebreakm_ebreak_executes_debug_code_dbg(void) {
  volatile uint32_t dpc;
  *g_debug_status += 1;

  __asm__ volatile ( R"(
    csrrs %[dpc], dpc, zero
    addi %[dpc], %[dpc], 4
    csrrw zero, dpc, %[dpc]
  )" : [dpc] "+r"(dpc) :: );
}

// -----------------------------------------------------------------------------

// Machine mode section of ebreak->debug mode test
uint32_t mmode_ebreakm_ebreak_executes_debug_code(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_debug_status   = 0;
  *g_debug_test_num = 4;

  __asm__ volatile ( R"(
    .option push
    .option norvc
    ebreak
    .option pop
  )");

  test_fail += (*g_debug_status == 1) ? 0 : 1;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

// Illegal csr in dmode test entry
uint32_t illegal_csr_in_dmode(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_debug_status   = 0;
  *g_debug_test_num = 5;

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 200
  };

  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  while (*g_debug_status == 0) {
    ;;
  }

  test_fail += (*g_debug_status == 1) ? 0 : 1;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

// Illegal csr in dmode debug code
void __attribute__((naked)) illegal_csr_in_dmode_dbg(void) {
  __asm__ volatile ( R"(
    csrrw s10, 0xeaf, s10
  )");
}

// -----------------------------------------------------------------------------

// Ecall in dmode test entry
uint32_t ecall_in_dmode(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_debug_status   = 0;
  *g_debug_test_num = 6;

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 200
  };

  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  while (*g_debug_status == 0) {
    ;;
  }

  test_fail += (*g_debug_status == 1) ? 0 : 1;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

// Debug mode ecall
void ecall_in_dmode_dbg(void) {
  __asm__ volatile ( R"(
    ecall
  )");
}

// -----------------------------------------------------------------------------

// Mret in dmode test entry
uint32_t mret_in_dmode(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_debug_status   = 0;
  *g_debug_test_num = 7;

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 200
  };

  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  while (*g_debug_status == 0) {
    ;;
  }

  test_fail += (*g_debug_status == 1) ? 0 : 1;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

// Mret in debug mode, debug portion
// This does technically not need to be in a function
// but for test structure and readability keeps the
// structure used for other tests.
void mret_in_dmode_dbg(void) {
  __asm__ volatile ( R"(
    mret
  )");
}

// -----------------------------------------------------------------------------

// Exception to dmode test entry
uint32_t exception_enters_debug_mode(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_debug_status   = 0;
  *g_debug_test_num = 8;

  __asm__ volatile (R"(csrrs s11, dcsr, zero)");

  while (*g_debug_status == 0) {
    ;;
  }

  test_fail += (*g_debug_status == 1) ? 0 : 1;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

// Debug portion of exception -> debug entry test
void exception_enters_debug_mode_dbg(void) {
  volatile uint32_t dpc;

  *g_debug_status = 1;
  __asm__ volatile ( R"(
    csrrs %[dpc], dpc, zero
    addi %[dpc], %[dpc], 2
    csrrw zero, dpc, %[dpc]
  )": [dpc] "+r"(dpc));
}

// -----------------------------------------------------------------------------

// Dret in m-mode test entry
uint32_t dret_in_mmode(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_debug_status   = 0;
  *g_debug_test_num = 9;

  __asm__ volatile (R"(dret)");

  test_fail += *g_debug_status ? 0 : 1;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

// Wfi prior to dmode test entry
uint32_t wfi_before_dmode(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_debug_status   = 0;
  *g_debug_test_num = 10;

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 200
  };

  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;
  __asm__ volatile (R"(wfi)");

  while (*g_debug_status == 0) {
    ;;
  }


  test_fail += *g_debug_status ? 0 : 1;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

// Wfi before dmode debug portion
void wfi_before_dmode_dbg(void) {
  *g_debug_status = 1;
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

uint32_t check_irq(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_debug_status   = 0;
  *g_debug_test_num = 11;

  clint_mie_enable(30);
  *g_expect_irq = 1;
  assert_irq();

  while (!(*g_debug_status)) {
    ;;
  }

  test_fail += *g_debug_status ? 0 : 1;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

void check_irq_handler(void) {
  volatile mcause_t mcause = { 0 };

  // Fields to clear;
  // Exists in both clic and clint, no need to have
  // special consideration for clic/clint.
  // Clearing all bits as for clint would break clic
  // mpp behavior
  mcause.clic.interrupt = 0x1;
  mcause.clic.exccode = 0x7FF;

  __asm__ volatile ( R"(
     csrrc %[mc], mcause, %[mc]
     )"
     : [mc] "+r"(mcause.raw)
     :
  );

  cvprintf(V_LOW, "mcause.exccode: %0d, mcause.interrupt: %0d\n", mcause.clic.exccode, mcause.clic.interrupt);
  // we use same id for clic and clint for simplicity
  if (((mcause.clint.interrupt == 1) &&
      (mcause.clint.exccode == 30)) ||
      (mcause.clic.interrupt == 1 &&
       mcause.clic.exccode == 30)) {
    *g_debug_status = 1;
    // No effect for clic
    clint_mie_disable(30);
    deassert_irq();
  }
  else {
    *g_debug_status = 0;
    // No effect for clic
    clint_mie_disable(30);
    deassert_irq();
  }
}

// -----------------------------------------------------------------------------

uint32_t check_stopcnt_bits(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_debug_status   = 0;
  *g_debug_test_num = 12;

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 200
  };

  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  while (!(*g_debug_status)) {
    ;;
  }
  test_fail += *g_debug_status ? 0 : 1;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

void check_stopcnt_bits_dbg(void) {
  volatile dcsr_t dcsr;
  dcsr.raw = 0;
  dcsr.fields.stopcount = 1;

  __asm__ volatile (R"(
    csrrs zero, dcsr, %[dcsr]
    csrrw zero, dscratch1, zero
    )"
      : [dcsr] "=r"(dcsr.raw)
  );

  // Set ok, this will be cleared by _debugger end if
  // the counters have incremented
  *g_debug_status = 1;
}


// ---------------------------------------------------------------
// single_step
//
// Main test initiator for single step tests, follows the common
// test template
// ---------------------------------------------------------------
uint32_t single_step(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_illegal_fail   = 0;
  *g_debug_status   = 0;
  *g_debug_test_num = 13;

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 200
  };

  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  while (!(*g_single_step_status)) {
    ;;
  }

  single_step_code();

  test_fail += get_single_step_result(*g_debug_status) ? 0 : 1;
  // Also check for some failures during certain checkpoints
  // that is not necessarily connected to specific subtest -
  // the log should contain the actual error location.
  test_fail += *g_single_step_unspec_err ? 1 : 0;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// ---------------------------------------------------------------
// single_step_code
//
// Main regular code to be single stepped in M-mode, is a set
// of subtests in itself, each test/function initialized with a
// dashed comment line and a label to ease debugging.
// Note: These labels are not used by the code itself.
// ---------------------------------------------------------------
void __attribute__((naked)) single_step_code(void) {
  __asm__ volatile (R"(
    cm.push {ra, s0-s11}, -64

    # ----------------
    ebreak_into_debug_mode_cause_1:

    add s2, zero, zero
    # Enter debug mode to execute cause=1
    c.ebreak
    # Load value to s3 to verify correct dpc increment
    addi s2, zero, 1

    # add a few nops, to avoid missing setting fail
    # in case of minor increment errors
    c.nop
    c.nop
    c.nop
    c.nop

    bne s2, zero, 1f
    # first single step checkpoint, set bit 1 if fail
    addi a0, zero, 1 << 1
    call set_debug_status

    1: # continue
    # ----------------
    # single_step_status is updated in debug mode here
    # unlike the following tests
    wfi_should_nop_in_single_step:
    wfi

    # Not setting an error bit here if fail, test will hang if
    # a wfi is not treated as nop in single_step

    # ----------------
    addi a0, zero, 3
    call set_single_step_status

    illegal_instr_handle:
    add s2, zero, zero

    # illegal csr instruction (dcsr access in m-mode)
    csrrs s2, dcsr, zero
    # illegal instruction (dret in m-mode)
    dret

    # If number of invalid instructions mismatch, set status
    # bit 3

    # Expect two illegal instructions
    lw s3, g_illegal_fail
    lw s4, 0(s3)
    addi s4, s4, -2
    bne s4, zero, ss_fail_3
    # Expect no change to s2, as instruction should not retire
    beq s2, zero, 1f

    ss_fail_3:
    addi a0, zero, 1 << 3
    call set_debug_status

    1: # Continue
    # ----------------

    trigger_match_setup_reason_4:
    # Trigger match setup
    addi a0, zero, 4
    call set_single_step_status
    addi s3, zero, 0

    .global trigger_loc
    .global trigger_exit

    add s3, zero, zero

    trigger_loc:
    addi s3, zero, 1 # This instruction should be skipped due to trigger
    trigger_exit:
    addi s3, s3, 2 # Thus we should end up with 2, not 3 in s3

    # wait here for one instruction to let debug mode attempt
    # trigger match inside debug mode

    addi s3, s3, -2

    # trigger skipped correctly, continue
    bne s3, zero, 2f
    beq zero, zero, 1f

    2:
    # we observed exactly one cause = trigger, continue
    # g_trigger matched should == 2 as we also use this to
    # signal debug mode to attempt trigger in debug
    lw s4, g_trigger_matched
    lw s5, 0(s4)
    addi s5, s5, -3
    beq s5, zero, 1f

    # one of the above conditions failed
    addi a0, zero, 1 << 4
    call set_debug_status

    1: # Continue
    # ----------------
    step_with_interrupt_with_stepie_reason_5:
    addi a0, zero, 30
    call clint_mie_enable
    addi a0, zero, 5
    call set_single_step_status
    lw s3, g_expect_irq
    addi s4, zero, 1
    sw s4, 0(s3)
    call assert_irq
    call wait_irq

    lw s4, 0(s3)
    beq s4, zero, 1f
    addi a0, zero, 1 << 5
    call set_debug_status

    1: # Continue
    # ----------------
    step_with_interrupt_without_stepie_reason_6:
    addi a0, zero, 30
    call clint_mie_enable
    addi a0, zero, 6
    call set_single_step_status
    call assert_irq
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    call deassert_irq
    nop
    nop

    lw s3, g_unexpected_irq
    lw s4, 0(s3)
    beq s4, zero, 1f
    sw zero, 0(s3)
    addi a0, zero, 1 << 6
    call set_debug_status
    # TODO need this many NOPs?

    1: # Continue
    # ----------------
    step_with_c_ebreak_reason_7:
    lw s3, g_ebreak_fail
    sw zero, 0(s3)

    addi a0, zero, 7
    call set_single_step_status
    c.ebreak

    lw s4, 0(s3)
    beq s4, zero, 1f
    addi a0, zero, 1 << 7
    call set_debug_status

    1: # Continue
    # ----------------
    step_with_ebreak_reason_8:
    lw s3, g_ebreak_fail
    sw zero, 0(s3)
    addi a0, zero, 8
    call set_single_step_status
    # force noncompressed ebreak
    .option push
    .option norvc
    ebreak
    .option pop

    lw s4, 0(s3)
    beq s4, zero, 1f
    addi a0, zero, 1 << 8
    call set_debug_status

    1: # Continue
    # ----------------
    step_with_ebreak_without_dcsr_ebreakm_reason_9:
    addi a0, zero, 9
    call set_single_step_status

    lw s0, g_expect_ebreak
    addi s1, zero, 1
    sw s1, 0(s0)

    # force noncompressed ebreak
    .option push
    .option norvc
    ebreak
    .option pop

    lw s1, 0(s0)
    beq s1, zero, 1f

    addi a0, zero, 1
    slli a0, a0, 9
    call set_debug_status

    1: # Continue
    # ----------------
    step_with_cebreak_without_dcsr_ebreakm_reason_10:
    addi a0, zero, 10
    call set_single_step_status

    lw s0, g_expect_ebreak
    addi s1, zero, 1
    sw s1, 0(s0)

    c.ebreak

    lw s1, 0(s0)
    beq s1, zero, 1f

    addi a0, zero, 1
    slli a0, a0, 10
    call set_debug_status

    1: # Continue
    # ----------------
    # disable single step
    addi a0, zero, 11
    call set_single_step_status
    ecall

    99: cm.pop {ra, s0-s11}, 64

    # return
    jalr zero, 0(ra)
  )");
}

// -----------------------------------------------------------------------------

// Wrappers to support both clic/clint
void assert_irq(void) {
  volatile clic_t clic_vector = { 0 };
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

void wait_irq(void) {
  while (*g_expect_irq) {
    ;;
  }
}

// -----------------------------------------------------------------------------
// Single step support functions
// -----------------------------------------------------------------------------

void increment_single_step_status(void) {
  *g_single_step_status += 1;
}

// -----------------------------------------------------------------------------

void set_debug_status(volatile uint32_t status) {
  *g_debug_status |= status;
}

// -----------------------------------------------------------------------------

void set_single_step_status(volatile uint32_t status) {
  *g_single_step_status = status;
}

// -----------------------------------------------------------------------------

void print_single_step_status(void) {
  if (*g_single_step_status != *g_single_step_status_prev) {
    cvprintf(V_DEBUG, "status: %0d\n", *g_single_step_status);
  }
  *g_single_step_status_prev = *g_single_step_status;
}

// -----------------------------------------------------------------------------

void ebreakm_set_dbg(void) {
  volatile dcsr_t dcsr;
  dcsr.raw = 0;

  dcsr.fields.ebreakm = 1;

  __asm__ volatile ( R"(
    csrrs zero, dcsr, %[dcsr]
    )":: [dcsr] "r"(dcsr.raw)
  );
}

// -----------------------------------------------------------------------------

void single_step_dbg(void) {
  // Check for single step exceptions and handle correct return addr
  // Use this function to handle exceptions and verify correct
  // pc after taking exceptions/interrupts while in single step
  // to avoid having to single step through exception code with
  // excessive test run times.
  exception_status_dbg();

  print_single_step_status();
  __asm__ volatile ( R"(
    csrrs %[dpc], dpc, zero
  )" : [dpc] "=r"(*g_previous_dpc));

  switch (*g_single_step_status) {
    case 0:
      ebreakm_set_dbg();
      increment_single_step_status();
      break;
    case 1:
      single_step_enable_dbg();
      increment_single_step_status();
      break;
    case 2:
      ;; // Not used, kept for consistency
      break;
    case 3:
      single_step_basic_dbg();
      break;
    case 4:
      single_step_trigger_setup_dbg();
      single_step_basic_dbg();
      break;
    case 5:
      single_step_stepie_enable_dbg();
      break;
    case 6:
      single_step_stepie_disable_dbg();
      break;
    case 7:
      single_step_c_ebreak_dbg();
      break;
    case 8:
      single_step_ebreak_dbg();
      break;
    case 9:
      single_step_ebreak_exception_dbg();
      break;
    case 10:
      single_step_c_ebreak_exception_dbg();
      break;
    case 11:
      single_step_disable_dbg();
      break;
    default: break;
  }

  *g_single_step_cnt += 1;
}

// -----------------------------------------------------------------------------
// Handle execptions and interupts inside debug mode instead of single stepping
// through the entire handler to speed up the process - we still verify that
// we actually entered the handler, and then handle it here
// -----------------------------------------------------------------------------

void exception_status_dbg(void) {
  volatile uint32_t dpc = 0;
  volatile uint32_t mtvec = 0;
  volatile uint32_t mepc = 0;
  volatile mcause_t mcause = { 0 };
  volatile dcsr_t   dcsr;
  volatile uint32_t temp;
  volatile mcontrol_t mcontrol = { 0 };
  volatile mcontrol_t mcontrol_backup = { 0 };
  volatile uint32_t tdata2_backup;

  // Fields to clear;
  // Exists in both clic and clint, no need to have
  // special consideration for clic/clint.
  // Clearing all bits as for clint would break clic
  // mpp behavior
  mcause.clic.interrupt = 0x1;
  mcause.clic.exccode = 0x7FF;

  __asm__ volatile ( R"(
    csrrs %[dpc], dpc, zero
    csrrs %[mtvec], mtvec, zero
    csrrc %[mcause], mcause, %[mcause]
    csrrs %[dcsr], dcsr, zero
    csrrs %[mepc], mepc, zero
  )" : [dpc]   "=r"(dpc),
       [mtvec] "=r"(mtvec),
       [mcause]"+r"(mcause.raw),
       [dcsr]  "=r"(dcsr.raw),
       [mepc]  "=r"(mepc));

  if (mcause.clint.interrupt == 1 || mcause.clic.interrupt == 1) {
    // Disable interrupt
    deassert_irq();
    if (*g_expect_irq) {
      *g_expect_irq = 0;
    } else {
      *g_unexpected_irq = 1;
      single_step_fail(5);
      cvprintf(V_LOW, "mcause.interrupt: %0d, mcause.exccode: %0d\n", mcause.clint.interrupt, mcause.clint.exccode);
    }
  } else if (*g_single_step_status == 4) {

    if (*g_trigger_matched == 1) {

      *g_trigger_matched += 1;
      mcontrol = (mcontrol_t) {
        .fields.type    = 2,
        .fields.dmode   = 1,
        .fields.action  = 1,
        .fields.m       = 1,
        .fields.execute = 1
      };

      __asm__ volatile ( R"(
        .global trigger_loc_dbg
        csrrw %[tdata2_backup], tdata2, %[trigger_loc_dbg]
        csrrw %[mcontrol_backup], tdata1, %[mcontrol]

        trigger_loc_dbg:
        addi %[temp], zero, 5
        nop
      )" : [temp]            "=r"(temp),
           [mcontrol_backup] "=r"(mcontrol_backup.raw),
           [tdata2_backup]   "=r"(tdata2_backup)
         : [trigger_loc_dbg] "r"(&trigger_loc_dbg),
           [mcontrol]        "r"(mcontrol.raw));

      if (temp == 5) {
        // Correctly executed trigger address
        *g_trigger_matched += 1;
      } else {
        // Triggered, should not happen
        *g_trigger_matched += 10;
      }
      // Restore previous value
      __asm__ volatile ( R"(
        csrrw zero, tdata1, %[mcontrol_backup]
        csrrw zero, tdata2, %[tdata2_backup]
      )" :: [mcontrol_backup] "r"(mcontrol_backup.raw),
            [tdata2_backup]   "r"(&tdata2_backup)
          );
    }

    *g_trigger_matched += (dcsr.fields.cause == DCAUSE_TRIGGER) ? 1 : 0;

  }
  else  {
    if ( (dcsr.fields.cause == DCAUSE_EBREAK)
      && (*g_single_step_status == 7
      ||  *g_single_step_status == 8) ) {
        *g_ebreak_fail += (mcause.clint.exccode == MCAUSE_BREAKPT) ? 1 : 0;
    }
    if (dpc == (mtvec & ~0x3UL)) {
      if (   *g_single_step_status == 3
          || *g_single_step_status == 9
          || *g_single_step_status == 10
          ) {
        // Count illegal instructions in single step test section 3
        *g_illegal_fail += ((*g_single_step_status == 3) && (mcause.clint.exccode == MCAUSE_ILLEGAL));
        // Check for ebreak with correct cause as we ended up in handler.
        // If this code branch gets bypassed the check against g_expect_ebreak will fail
        *g_expect_ebreak  -= ( (*g_single_step_status == 9 || *g_single_step_status == 10)
                             && mcause.clint.exccode == MCAUSE_BREAKPT) ? 1 : 0;
        increment_mepc(0);
        __asm__ volatile ( R"(
          csrrs %[mepc], mepc, zero
          csrrw zero, dpc, %[mepc]
        )" : [mepc] "+r"(mepc));
        cvprintf(V_MEDIUM, "Single step trap: mtvec: %08lx, dpc: %08lx, return addr: %08lx, mcause: %08lx, dcsr: %08lx\n", mtvec & ~0x3UL, dpc, mepc, mcause.raw, dcsr.raw);
        }
     }
  }
}

// -----------------------------------------------------------------------------

void single_step_trigger_setup_dbg(void) {
  volatile mcontrol_t mcontrol     = { 0 };
  volatile mcontrol_t mcontrol_exp = { 0 };

  mcontrol_exp = (mcontrol_t) {
    .fields.type    = 2,
    .fields.dmode   = 1,
    .fields.action  = 1,
    .fields.m       = 1,
    .fields.execute = 1
  };

  __asm__ volatile ( R"(
    csrrw zero, tdata2, %[trigger_loc]
    csrrw zero, tdata1, %[mcontrol_exp]
    csrrs %[mcontrol], tdata1, zero

  )" :
       [mcontrol] "=r"(mcontrol.raw)
     : [mcontrol_exp] "r"(mcontrol_exp.raw),
       [trigger_loc] "r"(&trigger_loc)
     );

  if (mcontrol.raw != mcontrol_exp.raw) {
    single_step_fail(6);
    cvprintf(V_LOW, "ERROR: mcontrol readback wrong value\n");
    print_tdata1(V_LOW, (tdata1_t *)&mcontrol);
  }
}

// -----------------------------------------------------------------------------

void single_step_trigger_entry_dbg(void) {
  set_dpc((uint32_t)(&trigger_exit));
}

// -----------------------------------------------------------------------------

void single_step_fail(uint32_t cause) {
  cvprintf(V_LOW, "Single step failure, cause: %0d\n", cause);
  *g_single_step_unspec_err |= 1 << cause;
}

// -----------------------------------------------------------------------------

void single_step_stepie_enable_dbg(void) {
  volatile dcsr_t dcsr = { 0 };

  dcsr.fields.stepie = 1;

  __asm__ volatile ( R"(
    csrrs zero, dcsr, %[dcsr]
  )" :: [dcsr] "r"(dcsr.raw));
}

// -----------------------------------------------------------------------------

void single_step_stepie_disable_dbg(void) {
  volatile dcsr_t dcsr = { 0 };
  dcsr.fields.stepie = 1;

  __asm__ volatile ( R"(
    csrrc zero, dcsr, %[dcsr]
  )" :: [dcsr] "r"(dcsr.raw));
}

// -----------------------------------------------------------------------------

void single_step_c_ebreak_dbg(void) {
  volatile dcsr_t   dcsr = { 0 };
  volatile uint32_t dpc  = 0;

  __asm__ volatile ( R"(
    csrrs %[dcsr], dcsr, zero
    csrrs %[dpc],  dpc,  zero
  )" : [dcsr] "=r"(dcsr.raw),
       [dpc]  "=r"(dpc));

  if (dcsr.fields.cause == DCAUSE_EBREAK) {
    increment_dpc(2);
  }
}

// -----------------------------------------------------------------------------

void single_step_ebreak_dbg(void) {
  volatile dcsr_t   dcsr = { 0 };
  volatile uint32_t dpc  = 0;

  __asm__ volatile ( R"(
    csrrs %[dcsr], dcsr, zero
    csrrs %[dpc],  dpc,  zero
  )" : [dcsr] "=r"(dcsr.raw),
       [dpc]  "=r"(dpc));

  if (dcsr.fields.cause == DCAUSE_EBREAK) {
    increment_dpc(4);
  }
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

void single_step_ebreak_exception_dbg(void) {
  volatile dcsr_t dcsr = { 0 };

  dcsr.fields.ebreakm = 1;

  __asm__ volatile ( R"(
    csrrc zero, dcsr, %[dcsr]
  )" : [dcsr] "=r"(dcsr.raw));
}

// -----------------------------------------------------------------------------

void single_step_c_ebreak_exception_dbg(void) {
  volatile dcsr_t dcsr  = { 0 };

  // The actual check happens on entry to debug,
  // when reaching this point it is safe to assume
  // that we can reenable dcsr.ebreakm again

  dcsr.fields.ebreakm = 1;

  __asm__ volatile ( R"(
    csrrc zero, dcsr, %[dcsr]
  )" :: [dcsr] "r"(dcsr.raw));
}

// -----------------------------------------------------------------------------

void single_step_disable_dbg(void) {
  volatile dcsr_t dcsr;
  dcsr.raw = 0;
  dcsr.fields.step = 1;

  __asm__ volatile ( R"(
    csrrc zero, dcsr, %[dcsr]
  )" :: [dcsr] "r"(dcsr.raw));

  cvprintf(V_LOW, "Disable single step\n");
}

// -----------------------------------------------------------------------------

void single_step_enable_dbg(void) {
  volatile dcsr_t dcsr;

  dcsr.raw = 0;
  dcsr.fields.step = 1;

  __asm__ volatile ( R"(
    csrrs zero, dcsr, %[dcsr]
  )" :: [dcsr] "r"(dcsr.raw)
  );

  // Entered ebreak with c.ebreak, increment
  increment_dpc(2);
}

// -----------------------------------------------------------------------------

void single_step_basic_dbg(void) {
  volatile dcsr_t dcsr;
  volatile dcsr_t dcsr_exp;
  volatile uint32_t mtval;
  volatile uint32_t dpc;

  dcsr_exp = (dcsr_t){
    .fields.xdebugver = 4,
    .fields.ebreakm   = 1,
    .fields.stopcount = 1,
    .fields.cause     = 2, // trigger
    .fields.mprven    = 1,
    .fields.step      = 1,
    .fields.prv       = 3
  };

  __asm__ volatile (R"(
    csrrs %[dcsr], dcsr, zero
  )" : [dcsr] "=r"(dcsr.raw)
  );

  if (dcsr.raw == dcsr_exp.raw) {
    single_step_trigger_entry_dbg();
  } else {
    // Check that mtval is always zero
    __asm__ volatile (R"(
      csrrs %[mtval], mtval, zero
    )": [mtval] "=r"(mtval)
    :);

    if (mtval != 0) {
      single_step_fail(1);
    }

    dcsr_exp = (dcsr_t){
      .fields.xdebugver = 4,
      .fields.ebreakm   = 1,
      .fields.stopcount = 1,
      .fields.cause     = DCAUSE_STEP,
      .fields.mprven    = 1,
      .fields.step      = 1,
      .fields.prv       = MODE_MACHINE
    };

    if (dcsr.raw != dcsr_exp.raw) {
      single_step_fail(2);
    }

    __asm__ volatile (R"(
      csrrs %[dpc], dpc, zero
    )": [dpc] "=r"(dpc)
    );

    if ( (dpc == (*g_previous_dpc + 2)) || (dpc == (*g_previous_dpc + 4)) ) {
      single_step_fail(3);
    }
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

  // CV32E40X does not support PMP, skip test
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

uint32_t mprv_dret_to_umode(uint32_t index, uint8_t report_name) {
  volatile uint32_t test_fail;
  volatile uint32_t pmpaddr = 0xffffffff;
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_debug_test_num = 14;
  *g_debug_status   = 0;

  // Check if there are configured pmp-regions:
  if (!has_pmp_configured()) {
    cvprintf(V_LOW, "Skipping test: 0 PMP regions or PMP not supported, cannot enter user mode\n");
    return 0;
  }

  // Setup PMP access for u-mode (otherwise all deny)
  set_mseccfg((mseccfg_t){
      .fields.mml           = 0,
      .fields.mmwp          = 0,
      .fields.rlb           = 1,
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

  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 200
  };

  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  // Debug mode, dret to user mode
  while ((*g_debug_status & 0x7UL) == 0) {
    ;;
  }

  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  // Debug mode, dret back to machine mode
  while ((*g_debug_status & 0x7UL) == 1) {
    ;;
  }

  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  // Debug mode, dret back to user mode
  while ((*g_debug_status & 0x7UL) == 2) {
    ;;
  }

  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;

  // Debug mode, dret back to machine mode
  while ((*g_debug_status & 0x7UL) == 3) {
    ;;
  }

  test_fail = (*g_debug_status == 4) ? 0 : 1;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

void mprv_dret_to_umode_dbg(void) {
  volatile dcsr_t dcsr = { 0 };
  volatile dcsr_t dcsr_readback = { 0 };
  volatile mstatus_t mstatus = { 0 };

  dcsr.fields.prv = MODE_MACHINE;

  // Enter user mode first, set mstatus.mprv and expect it to be cleared
  if (*g_debug_status == 0) {
    mstatus.clint.mprv = 1;
    __asm__ volatile ( R"(
      csrrs zero, mstatus, %[mstatus]
      csrrc %[dcsr_readback], dcsr, %[dcsr]
    )" : [dcsr_readback] "=r"(dcsr_readback.raw)
       : [mstatus] "r"(mstatus.raw),
         [dcsr]    "r"(dcsr.raw));
    *g_debug_status += 1;
    if (dcsr_readback.fields.prv != MODE_MACHINE) {
      *g_debug_status = (*g_debug_status | 0x01000000);
    }
  }

  // Enter machine mode when reentering debug mode, readback mstatus.mprv and clear it
  else if (*g_debug_status == 1) {
    mstatus.clint.mprv = 1;
    __asm__ volatile ( R"(
      csrrc %[mstatus], mstatus, %[mstatus]
      csrrs %[dcsr_readback], dcsr, %[dcsr]
    )" : [mstatus] "+r"(mstatus.raw),
         [dcsr_readback] "=r"(dcsr_readback.raw)
       : [dcsr]    "r"(dcsr.raw));
    if (mstatus.clint.mprv != 0) {
      cvprintf(V_LOW, "readback: mprv not cleared correctly\n");
      *g_debug_status = (*g_debug_status | 0x40000000);
    }
    if (dcsr_readback.fields.prv != 0x0) {
      *g_debug_status = (*g_debug_status | 0x02000000);
    }
    *g_debug_status += 1;
  }

  // Enter debug mode again, this time with mstatus.mprv cleared
  else if (*g_debug_status == 2) {
    mstatus.clint.mprv = 1;
    __asm__ volatile ( R"(
      csrrc zero, mstatus, %[mstatus]
      csrrc %[dcsr_readback], dcsr, %[dcsr]
    )" :[dcsr_readback] "=r"(dcsr_readback.raw)
       :[mstatus] "r"(mstatus.raw),
        [dcsr] "r"(dcsr.raw));
    *g_debug_status += 1;
    if (dcsr_readback.fields.prv != MODE_MACHINE) {
      *g_debug_status = (*g_debug_status | 0x04000000);
    }
  }

  // Return to machine mode, check that mstatus.mprv i still cleared
  else if (*g_debug_status == 3) {
    mstatus.clint.mprv = 1;
    __asm__ volatile ( R"(
      csrrs %[mstatus], mstatus, %[mstatus]
      csrrs %[dcsr_readback], dcsr, %[dcsr]
    )": [mstatus] "+r"(mstatus.raw),
        [dcsr_readback] "=r"(dcsr_readback.raw)
      : [dcsr]    "r"(dcsr.raw));
    if (mstatus.clint.mprv != 0) {
      cvprintf(V_LOW, "readback: mprv not cleared correctly\n");
      *g_debug_status = (*g_debug_status | 0x80000000);
    }
    if (dcsr_readback.fields.prv != 0x0) {
      *g_debug_status = (*g_debug_status | 0x08000000);
    }
    *g_debug_status += 1;
  }

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

uint32_t __attribute__((__noinline__)) get_dcsr_cause(void) {
  volatile dcsr_t dcsr;
  __asm__ volatile ( R"( csrrs %[dcsr], dcsr, zero )" : [dcsr] "=r"(dcsr.raw) : :);
  cvprintf (V_MEDIUM, "get_dcsr_cause: %0x\n", dcsr.fields.cause);
  return (uint32_t)dcsr.fields.cause;
}

// -----------------------------------------------------------------------------

void __attribute__((naked)) _debugger_end(void) {
  __asm__ volatile ( R"(
    lw a0, debug_exit_msg
    lw s1, g_debug_test_num
    lw a1, 0(s1)

    call check_mcycle_minstret

    # clear stopcount bit if set by test
    addi s2, zero, 12
    bne s1, s2, clear_stopcount_skip
    addi s2, zero, 1 << 10
    csrrc zero, dcsr, s2

    clear_stopcount_skip:
    csrrw zero, dscratch1, zero

    1: auipc s11, %pcrel_hi(_debugger_restore_stack)
    addi s11, s11, %pcrel_lo(1b)
    jalr zero, 0(s11)

    .globl _debugger_restore_stack_end
    _debugger_restore_stack_end:
    dret
  )");
}

// -----------------------------------------------------------------------------

void __attribute__((__noinline__)) check_mcycle_minstret(void) {
  volatile uint32_t minstret_end_cnt;
  volatile uint32_t mcycle_end_cnt;

  __asm__ volatile ( R"(
    csrrs %[minstret], minstret, zero
    csrrs %[mcycle], mcycle, zero
  )": [minstret] "=r"(minstret_end_cnt),
      [mcycle] "=r"(mcycle_end_cnt)
  );
  if ((minstret_end_cnt != *g_minstret_cnt) ||
      (mcycle_end_cnt != *g_mcycle_cnt)) {
    *g_debug_status = 0;
  }
}

// -----------------------------------------------------------------------------

void __attribute__((naked)) _debugger_restore_stack(void) {
  __asm__ volatile ( R"(
    # Keep return address, remember to recover after return

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

    # Restore debug stack ptr
    addi sp, sp, 12
    cm.pop {ra, s0-s11}, 112

    # restore s0, s1
    csrrs sp, dscratch0, zero
    csrrw s0, dscratch1, s0

    bne zero, s0, 2f

    csrrw s0, dscratch1, s0
    1: auipc s11, %pcrel_hi(_debugger_restore_stack_end)
    addi s11, s11, %pcrel_lo(1b)
    jalr zero, 0(s11)

    2:
    jalr zero, 0(s0)
  )");
}

// -----------------------------------------------------------------------------

void __attribute__((naked)) _debugger_exception(void) {
  __asm__ volatile ( R"(
    call debug_exception_handler

    1: auipc s11, %pcrel_hi(_debugger_end)
    addi s11, s11, %pcrel_lo(1b)
    jalr zero, 0(s11)
  )");
}

// -----------------------------------------------------------------------------

void debug_exception_handler(void) {
  volatile dcsr_t dcsr;

  __asm__ volatile ( R"(
    csrrs %[dcsr], dcsr, zero
  )"
      : [dcsr] "=r"(dcsr.raw) : :);

  switch (*g_debug_test_num) {
    case 5:
      *g_debug_status = 1;
      __asm__ volatile ( R"(csrrw zero, dscratch1, zero)");
      break;
    case 6:
      *g_debug_status = 1;
      break;
    case 7:
      *g_debug_status = 1;
      break;
    case 13:
      if (dcsr.fields.cause == DCAUSE_TRIGGER) {
        single_step_disable_dbg();
      }
    default :
      break;
  }

  cvprintf(V_MEDIUM, "dcsr cause: %0x\n", dcsr.fields.cause);
  return;
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

void setup_clic(void) {
  if (*g_has_clic == 1) {
    __asm__ volatile ( R"(
      csrrw zero, 0x307, %[mtvt_table]
    )" :: [mtvt_table] "r"(&mtvt_table));
  }
}

// -----------------------------------------------------------------------------

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

// This function should cover corner cases encountered by broken code during
// test development that made the ISS and RTL deviate. After resolving issues,
// leave this function in place to ensure that these issues do not return.
uint32_t cover_known_iss_mismatches(uint32_t index, uint8_t report_name) {
  volatile clic_t clic_vector = { 0 };
  volatile debug_req_control_t debug_req_ctrl;

  SET_FUNC_INFO


  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // 1. Mismatch when an interrupt is asserted without its
  // irq bit set (clic only)
  if (*g_has_clic == 1) {
    // Make the vc provoke the clic signals, but not set clic.irq
    clic_vector = (clic_t){
      .fields.reserved_31_22 = 0x1FF,
      .fields.irq            = 0x0,
      .fields.id             = 0X7FF,
      .fields.level          = 0xFF,
      .fields.priv           = MODE_MACHINE,
      .fields.shv            = 0x1,
    };

    vp_assert_irq(clic_vector.raw, 2);

    // Give the interrupt signals some time
    for (volatile int i = 0; i < 20; i++) {
      __asm__ volatile ( R"(nop)");
    }

    deassert_irq();
  }

  // 2. dpc lower bit writable
  debug_req_ctrl = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1,
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 0x1fff,
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 200
  };

  *g_debug_status       = 0;
  *g_debug_test_num     = 18;
  DEBUG_REQ_CONTROL_REG = debug_req_ctrl.raw;
  while (!*g_debug_status) {
    ;;
  }

  // Don't flag this test as pass fail, only needs ISS check

  cvprintf(V_LOW, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

void cover_known_iss_mismatches_dbg(void) {
  volatile uint32_t temp;
  volatile dcsr_t dcsr_backup = { 0 };

  __asm__ volatile ( R"(
    add %[temp], zero, zero
    csrrw %[dcsr_bu], dcsr, %[temp]
    addi %[temp], zero, -1
    csrrw %[temp], dcsr, %[temp]
    csrrw %[temp], dcsr, %[dcsr_bu]
  )": [temp] "+r"(temp),
      [dcsr_bu] "+r"(dcsr_backup.raw)
  );

  *g_debug_status = 1;
}
