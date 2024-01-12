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
// CLIC CSR directed access tests
// - Tests proper mirroring of mpp/mpie
// - Tests mtvt/mtvec handling with shv pointer fetch exception
// - Tests read/write access, side effects of mnxti with and without interrupts
// - Tests read/write access to mscratchcsw*
// - Tests mintthresh settings with random interrupts
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
#define NUM_TESTS 25
// Set which test index to start testing at (for quickly running specific tests during development)
#define START_TEST_IDX 0
// Abort test at first self-check fail, useful for debugging.
#define ABORT_ON_ERROR_IMMEDIATE 0
#define CLIC_ID_WIDTH 5
#define CLIC_LVL_WIDTH 8
#define MTVEC_ALIGN_BITS 7

#define NUM_INTERRUPTS (1 << CLIC_ID_WIDTH)
#define NUM_INTERRUPT_LVLS (1 << CLIC_LVL_WIDTH)

// Addresses of VP interrupt control registers
#define TIMER_REG_ADDR       ((volatile uint32_t * volatile ) (CV_VP_INTR_TIMER_BASE))
#define TIMER_VAL_ADDR       ((volatile uint32_t * volatile ) (CV_VP_INTR_TIMER_BASE + 4))
#define RANDOM_NUM_ADDR      ((volatile uint32_t * volatile ) (CV_VP_RANDOM_NUM_BASE))

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

#define MSTATUS_MPP(v) \
   ((v & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET)

#define MSTATUS_MPIE(v) \
   ((v & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET)

#define MCAUSE_MPP(v) \
   ((v & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET)

#define MCAUSE_MPIE(v) \
   ((v & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET)

// Verbosity levels (Akin to the uvm verbosity concept)
typedef enum {
  V_OFF    = 0,
  V_LOW    = 1,
  V_MEDIUM = 2,
  V_HIGH   = 3,
  V_DEBUG  = 4
} verbosity_t;

typedef enum {
  OFF = 0,
  TOR = 1,
  NA4 = 2,
  NAPOT = 3
} pmp_mode_t;

typedef struct {
  volatile uint8_t reg_no;
  volatile uint8_t lock;
  volatile pmp_mode_t mode;
  volatile uint8_t execute;
  volatile uint8_t write;
  volatile uint8_t read;
} pmpcfg_t;

typedef struct {
  volatile uint8_t rlb;
  volatile uint8_t mmwp;
  volatile uint8_t mml;
} mseccfg_t;

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
    volatile uint32_t uil            : 8;
    volatile uint32_t sil            : 8;
    volatile uint32_t reserved_23_16 : 8;
    volatile uint32_t mil            : 8;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw : 32;
} __attribute__((packed)) mintstatus_t;

typedef union {
  struct {
    volatile uint32_t th            : 8;
    volatile uint32_t reserved_31_8 : 24;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw : 32;
} __attribute__((packed)) mintthresh_t;

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
  } volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) mstatus_t;

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
} __attribute__((packed)) clic_t;

// ---------------------------------------------------------------
// Global variables
// ---------------------------------------------------------------
// Bitfield offsets for mpp and mpie
const uint32_t MSTATUS_MPP_OFFSET  = 11;
const uint32_t MSTATUS_MPIE_OFFSET = 7;
const uint32_t MCAUSE_MPP_OFFSET   = 28;
const uint32_t MCAUSE_MPIE_OFFSET  = 27;

// Bitfield masks for mpp and mpie
const uint32_t MSTATUS_MPP_MASK  = 0x3 << MSTATUS_MPP_OFFSET;
const uint32_t MSTATUS_MPIE_MASK = 0x1 << MSTATUS_MPIE_OFFSET;
const uint32_t MCAUSE_MPP_MASK   = 0x3 << MCAUSE_MPP_OFFSET;
const uint32_t MCAUSE_MPIE_MASK  = 0x1 << MCAUSE_MPIE_OFFSET;

// Print verbosity, consider implementing this as a virtual
// peripheral setting to be controlled from UVM.
volatile verbosity_t global_verbosity = V_LOW;

extern volatile uint32_t mtvt_table;
extern volatile uint32_t mtvt_table_mret;
extern volatile uint32_t mtvt_table_mret_dest;
extern volatile uint32_t recovery_pt;
extern volatile uint32_t recovery_pt_mret;
extern volatile uint32_t recovery_pt_mret_ptr;

volatile uint32_t test_fail_asm;

volatile uint32_t * volatile g_expect_illegal;
volatile uint32_t * volatile g_special_handler_idx;
volatile uint32_t * volatile g_asserted_irq_idx;
volatile uint32_t * volatile g_asserted_irq_lvl;
volatile uint32_t * volatile g_irq_handler_reported_error;
volatile uint32_t * volatile g_mepc_triggered;
volatile uint32_t * volatile g_recovery_enable;
volatile uint32_t * volatile g_checker;

// ---------------------------------------------------------------
// Test prototypes - should match
// uint32_t <name>(uint32_t index, uint8_t report_name)
//
// Use template below for implementation
// ---------------------------------------------------------------
uint32_t mcause_mstatus_mirror_init(uint32_t index, uint8_t report_name);
uint32_t w_mcause_mpp_r_mstatus_mpp(uint32_t index, uint8_t report_name);
uint32_t w_mstatus_mpp_r_mcause_mpp(uint32_t index, uint8_t report_name);
uint32_t w_mcause_mpie_r_mstatus_mpie(uint32_t index, uint8_t report_name);
uint32_t w_mstatus_mpie_r_mcause_mpie(uint32_t index, uint8_t report_name);
uint32_t w_mie_notrap_r_zero(uint32_t index, uint8_t report_name);
uint32_t w_mip_notrap_r_zero(uint32_t index, uint8_t report_name);
uint32_t w_mtvt_rd_alignment(uint32_t index, uint8_t report_name);
uint32_t w_mtvec_rd_alignment(uint32_t index, uint8_t report_name);
uint32_t invalid_mtvt_ptr_exec(uint32_t index, uint8_t report_name);
uint32_t invalid_mtvt_ptr_exec_mret(uint32_t index, uint8_t report_name);
uint32_t r_mnxti_without_irq(uint32_t index, uint8_t report_name);
uint32_t rw_mnxti_without_irq_illegal(uint32_t index, uint8_t report_name);
uint32_t r_mnxti_with_pending_irq(uint32_t index, uint8_t report_name);
uint32_t r_mnxti_with_lower_lvl_pending_irq(uint32_t index, uint8_t report_name);
uint32_t w_mnxti_side_effects(uint32_t index, uint8_t report_name);
uint32_t rw_mscratchcsw(uint32_t index, uint8_t report_name);
uint32_t rw_mscratchcsw_illegal(uint32_t index, uint8_t report_name);
uint32_t rw_mscratchcswl(uint32_t index, uint8_t report_name);
uint32_t rw_mscratchcswl_illegal(uint32_t index, uint8_t report_name);
uint32_t mret_with_minhv(uint32_t index, uint8_t report_name);
uint32_t mintthresh_higher(uint32_t index, uint8_t report_name);
uint32_t mintthresh_lower(uint32_t index, uint8_t report_name);
uint32_t mintthresh_equal(uint32_t index, uint8_t report_name);
uint32_t mret_with_minhv_and_unaligned_mepc(uint32_t index, uint8_t report_name);

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
 * max
 *
 * returns maxval of a and b
 */
uint32_t max(uint32_t a, uint32_t b);

/*
 * cvprintf
 *
 * verbosity controlled printf
 * use as printf, but with an added verbosity-level setting
 *
 */
int cvprintf(verbosity_t verbosity, const char *format, ...);

/*
 * vp_assert_irq
 *
 * Notify clic_interrupt_agent vp to assert given
 * clic interrupt
 */
void vp_assert_irq(uint32_t mask, uint32_t cycle_delay);

/*
 * set_pmpcfg
 *
 * Sets up pmp configuration for a given region
 * (defined in pmpcfg_t object)
 */
void set_pmpcfg(pmpcfg_t pmpcfg);

/*
 * set_mseccfg
 *
 * Sets up mseccfg with the provided
 * mseccfg_t object
 */
void set_mseccfg(mseccfg_t mseccfg);

/*
 * increment_mepc
 *
 * Increments mepc,
 * incr_val 0 = auto detect
 *          2 = halfword
 *          4 = word
 */
void increment_mepc(uint32_t incr_val);

/*
 * reset_cpu_interrupt_lvl
 *
 * Resets core internal interrupt level (as reported by mintsstatus.mil)
 */
void reset_cpu_interrupt_lvl(void);

// ---------------------------------------------------------------
// Test entry point
// ---------------------------------------------------------------
int main(int argc, char **argv){

  volatile uint32_t (* volatile tests[NUM_TESTS])(volatile uint32_t, volatile uint8_t);

  volatile uint32_t test_res = 0x1;
  volatile int      retval   = 0;

  g_expect_illegal             = calloc(1, sizeof(uint32_t));
  g_special_handler_idx        = calloc(1, sizeof(uint32_t));
  g_asserted_irq_idx           = calloc(1, sizeof(uint32_t));
  g_asserted_irq_lvl           = calloc(1, sizeof(uint32_t));
  g_irq_handler_reported_error = calloc(1, sizeof(uint32_t));
  g_mepc_triggered             = calloc(1, sizeof(uint32_t));
  g_recovery_enable            = calloc(1, sizeof(uint32_t));
  g_checker                    = calloc(1, sizeof(uint32_t));

  // Add function pointers to new tests here
  tests[0]  = mcause_mstatus_mirror_init;
  tests[1]  = w_mcause_mpp_r_mstatus_mpp;
  tests[2]  = w_mstatus_mpp_r_mcause_mpp;
  tests[3]  = w_mcause_mpie_r_mstatus_mpie;
  tests[4]  = w_mstatus_mpie_r_mcause_mpie;
  tests[5]  = w_mie_notrap_r_zero;
  tests[6]  = w_mip_notrap_r_zero;
  tests[7]  = w_mtvt_rd_alignment;
  tests[8]  = w_mtvec_rd_alignment;
  tests[9]  = invalid_mtvt_ptr_exec;
  tests[10] = invalid_mtvt_ptr_exec_mret;
  tests[11] = r_mnxti_without_irq;
  tests[12] = rw_mnxti_without_irq_illegal;
  tests[13] = r_mnxti_with_pending_irq;
  tests[14] = r_mnxti_with_lower_lvl_pending_irq;
  tests[15] = w_mnxti_side_effects;
  tests[16] = rw_mscratchcsw;
  tests[17] = rw_mscratchcsw_illegal;
  tests[18] = rw_mscratchcswl;
  tests[19] = rw_mscratchcswl_illegal;
  tests[20] = mret_with_minhv;
  tests[21] = mintthresh_lower;
  tests[22] = mintthresh_higher;
  tests[23] = mintthresh_equal;
  tests[24] = mret_with_minhv_and_unaligned_mepc;

  // Run all tests in list above
  cvprintf(V_LOW, "\nCLIC Test start\n\n");
  for (volatile int i = START_TEST_IDX; i < NUM_TESTS; i++) {
    test_res = set_test_status(tests[i](i, (volatile uint32_t)(0)), test_res);
  }

  // Report failures
  retval = get_result(test_res, tests);

  free((void *)g_expect_illegal            );
  free((void *)g_special_handler_idx       );
  free((void *)g_asserted_irq_idx          );
  free((void *)g_asserted_irq_lvl          );
  free((void *)g_irq_handler_reported_error);
  free((void *)g_mepc_triggered            );
  free((void *)g_recovery_enable           );
  free((void *)g_checker                   );
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

uint32_t max(uint32_t a, uint32_t b) {
  return a > b ? a : b;
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

uint32_t get_random_interrupt_number(uint32_t min, uint32_t max) {
  volatile uint32_t num;
  num = ((*RANDOM_NUM_ADDR) % ((NUM_INTERRUPTS > max ? max : NUM_INTERRUPTS) - min)) + min;
  return num;
}

// -----------------------------------------------------------------------------

uint32_t get_random_interrupt_level(uint32_t min, uint32_t max) {
  volatile uint32_t num;
  num = ((*RANDOM_NUM_ADDR) % ((NUM_INTERRUPT_LVLS > max ? max : NUM_INTERRUPT_LVLS) - min)) + min;
  return num;
}

// -----------------------------------------------------------------------------

void increment_mepc(uint32_t incr_val) {
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

void set_mseccfg(mseccfg_t mseccfg){
  volatile uint32_t mseccfg_vector = 0x0;

  mseccfg_vector = (
      ((mseccfg.rlb  << 2) & 0x4) |
      ((mseccfg.mmwp << 1) & 0x2) |
      ((mseccfg.mml  << 0) & 0x1));

  __asm__ volatile ( R"(
    csrrs x0, mseccfg, %[cfg_vec]
  )"
      :
      : [cfg_vec] "r"(mseccfg_vector)
      :);

  cvprintf(V_DEBUG, "Wrote mseccfg: 0x%08lx\n", mseccfg_vector);
}

void set_pmpcfg(pmpcfg_t pmpcfg){
  volatile uint32_t pmpcfg_vector = 0x0;
  volatile uint32_t temp = 0;

  pmpcfg_vector = (
      ((pmpcfg.lock    << 7) & 0x80) |
      ((pmpcfg.mode    << 3) & 0x18) |
      ((pmpcfg.execute << 2) & 0x4 ) |
      ((pmpcfg.write   << 1) & 0x2 ) |
      ((pmpcfg.read    << 0) & 0x1 )) << ((pmpcfg.reg_no % 4)*8);

  temp = 0xff << ((pmpcfg.reg_no % 4)*8);

  switch (pmpcfg.reg_no / 4) {
    case 0:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg0, t0
        csrrs %[cfg_vec], pmpcfg0, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 1:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg1, t0
        csrrs %[cfg_vec], pmpcfg1, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 2:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg2, t0
        csrrs %[cfg_vec], pmpcfg2, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 3:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg3, t0
        csrrs %[cfg_vec], pmpcfg3, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 4:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg4, t0
        csrrs %[cfg_vec], pmpcfg4, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    case 5:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg5, t0
        csrrs %[cfg_vec], pmpcfg5, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 6:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg6, t0
        csrrs %[cfg_vec], pmpcfg6, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 7:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg7, t0
        csrrs %[cfg_vec], pmpcfg7, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 8:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg8, t0
        csrrs %[cfg_vec], pmpcfg8, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 9:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg9, t0
        csrrs %[cfg_vec], pmpcfg9, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 10:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg10, t0
        csrrs %[cfg_vec], pmpcfg10, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 11:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg11, t0
        csrrs %[cfg_vec], pmpcfg11, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 12:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg12, t0
        csrrs %[cfg_vec], pmpcfg12, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 13:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg13, t0
        csrrs %[cfg_vec], pmpcfg13, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 14:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg14, t0
        csrrs %[cfg_vec], pmpcfg14, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
    case 15:
      __asm__ volatile ( R"(
        add t0, x0, %[tmp]
        csrrc x0, pmpcfg15, t0
        csrrs %[cfg_vec], pmpcfg15, %[cfg_vec]
        )"
          : [cfg_vec] "+r"(pmpcfg_vector)
          : [tmp] "r"(temp)
          : "t0"
          );
    break;
  }

  cvprintf(V_DEBUG, "Wrote pmpcfg_vector: 0x%08lx\n", pmpcfg_vector);
  return;
}

// -----------------------------------------------------------------------------

void vp_assert_irq(uint32_t mask, uint32_t cycle_delay){
  *TIMER_REG_ADDR = mask;
  *TIMER_VAL_ADDR = 1 + cycle_delay;
}

// -----------------------------------------------------------------------------

_Pragma("GCC push_options")
_Pragma("GCC optimize (\"O0\")")

// -----------------------------------------------------------------------------

uint32_t mcause_mstatus_mirror_init(uint32_t index, uint8_t report_name){
  volatile uint8_t test_fail = 0;
  volatile uint32_t readback_val_mcause = 0x0;
  volatile uint32_t readback_val_mstatus = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  cvprintf(V_MEDIUM, "\nTesting mirroring of mcause.mpp/mpie and mstatus.mpp/mpie without write\n");
  __asm__ volatile ( R"(
    csrrs %[mc], mcause, x0
    csrrs %[ms], mstatus, x0
  )"
      : [mc] "=r"(readback_val_mcause),
        [ms] "=r"(readback_val_mstatus)
      :
      :
      );
  test_fail += MCAUSE_MPP(readback_val_mcause) != MSTATUS_MPP(readback_val_mstatus);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  test_fail += MCAUSE_MPIE(readback_val_mcause) != MSTATUS_MPIE(readback_val_mstatus);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t w_mcause_mpp_r_mstatus_mpp(uint32_t index, uint8_t report_name){

  volatile uint8_t  test_fail = 0;
  volatile uint32_t readback_val = 0x0;
  volatile uint32_t mcause_initial_val = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  cvprintf(V_MEDIUM, "\nTesting write to mcause.mpp, read from mstatus.mpp\n");
  // Backup mcause
  __asm__ volatile ( R"(
      csrrs %[mc], mcause, x0
  )"
      : [mc] "=r"(mcause_initial_val)
      :
      :
      );
  cvprintf(V_HIGH, "Initial value mcause.mpp: %0lx\n", ((mcause_initial_val & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET));

  // Bit set and read back
  __asm__ volatile ( R"(
      csrrs x0, mcause, %[mc]
      csrrs %[rb], mstatus, x0
  )"
      : [rb] "=r"(readback_val)
      : [mc] "r"(MCAUSE_MPP_MASK)
      :
      );

  test_fail += MSTATUS_MPP(readback_val) != 0x3;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mstatus.mpp after setting bits: %0lx\n", ((readback_val & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET));

  // Bit clear and read back
  __asm__ volatile ( R"(
      csrrc x0, mcause, %[mc]
      csrrc %[rb], mstatus, x0
  )"
      : [rb] "=r"(readback_val)
      : [mc] "r"(MCAUSE_MPP_MASK)
      :
      );

  test_fail += MSTATUS_MPP(readback_val) != 0x0;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mstatus.mpp after clearing bits: %0lx\n", ((readback_val & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET));

  // Restore value and read back
  __asm__ volatile ( R"(
      csrrw x0, mcause, %[mc]
      csrrw %[rb], mstatus, x0
  )"
      : [rb] "=r"(readback_val)
      : [mc] "r"(mcause_initial_val)
      :
      );

  test_fail += MSTATUS_MPP(readback_val) != MCAUSE_MPP(mcause_initial_val);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mstatus.mpp after restore: %0lx\n", ((readback_val & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET));

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t w_mstatus_mpp_r_mcause_mpp(uint32_t index, uint8_t report_name){

  volatile uint8_t  test_fail = 0;
  volatile uint32_t readback_val = 0x0;
  volatile uint32_t mstatus_initial_val = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  cvprintf(V_MEDIUM, "\nTesting write to mstatus.mpp, read from mcause.mpp\n");

  // Backup mstatus
  __asm__ volatile ( R"(
      csrrs %[ms], mstatus, x0
  )"
      : [ms] "=r"(mstatus_initial_val)
      :
      :
      );

  cvprintf(V_HIGH, "Initial value mstatus.mpp: %0lx\n", ((mstatus_initial_val & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET));

  // Bit set and read back
  __asm__ volatile ( R"(
      csrrs x0, mstatus, %[ms]
      csrrs %[rb], mcause, x0
  )"
      : [rb] "=r"(readback_val)
      : [ms] "r"(MSTATUS_MPP_MASK)
      :
      );

  test_fail += MCAUSE_MPP(readback_val) != 0x3;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mcause.mpp after setting bits: %0lx\n", ((readback_val & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET));

  // Bit clear and read back
  __asm__ volatile ( R"(
      csrrc x0, mstatus, %[ms]
      csrrc %[rb], mcause, x0
  )"
      : [rb] "=r"(readback_val)
      : [ms] "r"(MSTATUS_MPP_MASK)
      :
      );

  test_fail += MCAUSE_MPP(readback_val) != 0x0;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mcause.mpp after clearing bits: %0lx\n", ((readback_val & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET));

  // Restore value and read back
  __asm__ volatile ( R"(
      csrrw x0, mstatus, %[ms]
      csrrw %[rb], mcause, x0
  )"
      : [rb] "=r"(readback_val)
      : [ms] "r"(mstatus_initial_val)
      :
      );

  test_fail += MCAUSE_MPP(readback_val) != MSTATUS_MPP(mstatus_initial_val);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mcause.mpp after restore: %0lx\n", ((readback_val & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET));

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t w_mcause_mpie_r_mstatus_mpie(uint32_t index, uint8_t report_name){

  volatile uint8_t  test_fail = 0;
  volatile uint32_t readback_val = 0x0;
  volatile uint32_t mcause_initial_val = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  cvprintf(V_MEDIUM, "\nTesting write to mcause.mpie, read from mstatus.mpie\n");
  // Backup mcause
  __asm__ volatile ( R"(
      csrrs %[mc], mcause, x0
  )"
      : [mc] "=r"(mcause_initial_val)
      :
      :
      );

  cvprintf(V_HIGH, "Initial value mcause.mpie: %0lx\n", ((mcause_initial_val & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET));

  // Bit set and read back
  __asm__ volatile ( R"(
      csrrs x0, mcause, %[mc]
      csrrs %[rb], mstatus, x0
  )"
      : [rb] "=r"(readback_val)
      : [mc] "r"(MCAUSE_MPIE_MASK)
      :
      );

  test_fail += MSTATUS_MPIE(readback_val) != 0x1;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mstatus.mpie after setting bits: %0lx\n", ((readback_val & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET));

  // Bit clear and read back
  __asm__ volatile ( R"(
      csrrc x0, mcause, %[mc]
      csrrc %[rb], mstatus, x0
  )"
      : [rb] "=r"(readback_val)
      : [mc] "r"(MCAUSE_MPIE_MASK)
      :
      );

  test_fail += MSTATUS_MPIE(readback_val) != 0x0;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mstatus.mpie after clearing bits: %0lx\n", ((readback_val & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET));
  // Restore value and read back
  __asm__ volatile ( R"(
      csrrw x0, mcause, %[mc]
      csrrw %[rb], mstatus, x0
  )"
      : [rb] "=r"(readback_val)
      : [mc] "r"(mcause_initial_val)
      :
      );

  test_fail += MSTATUS_MPIE(readback_val) != MCAUSE_MPIE(mcause_initial_val);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
    cvprintf(V_HIGH, "Read back mcause.mpie after restore: %0lx\n", ((readback_val & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET));

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t w_mstatus_mpie_r_mcause_mpie(uint32_t index, uint8_t report_name){

  volatile uint8_t  test_fail = 0;
  volatile uint32_t readback_val = 0x0;
  volatile uint32_t mstatus_initial_val = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  cvprintf(V_MEDIUM, "\nTesting write to mstatus.mpie, read from mcause.mpie\n");

  // Backup mstatus
  __asm__ volatile ( R"(
      csrrs %[ms], mstatus, x0
  )"
      : [ms] "=r"(mstatus_initial_val)
      :
      :
      );

  cvprintf(V_HIGH, "Initial value mstatus.mpie: %0lx\n", ((mstatus_initial_val & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET));

  // Bit set and read back
  __asm__ volatile ( R"(
      csrrs x0, mstatus, %[ms]
      csrrs %[rb], mcause, x0
  )"
      : [rb] "=r"(readback_val)
      : [ms] "r"(MSTATUS_MPIE_MASK)
      :
      );

  test_fail += MCAUSE_MPIE(readback_val) != 0x1;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mcause.mpie after setting bits: %0lx\n", ((readback_val & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET));

  // Bit clear and read back
  __asm__ volatile ( R"(
      csrrc x0, mstatus, %[ms]
      csrrc %[rb], mcause, x0
  )"
      : [rb] "=r"(readback_val)
      : [ms] "r"(MSTATUS_MPIE_MASK)
      :
      );

  test_fail += MCAUSE_MPIE(readback_val) != 0x0;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mcause.mpie after clearing bits: %0lx\n", ((readback_val & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET));

  // Restore value and read back
  __asm__ volatile ( R"(
      csrrw x0, mstatus, %[ms]
      csrrw %[rb], mcause, x0
  )"
      : [rb] "=r"(readback_val)
      : [ms] "r"(mstatus_initial_val)
      :
      );

  test_fail += MCAUSE_MPIE(readback_val) != MSTATUS_MPIE(mstatus_initial_val);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mcause.mpie after restore: %0lx\n", ((readback_val & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET));

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

_Pragma("GCC pop_options")

// -----------------------------------------------------------------------------

uint32_t w_mie_notrap_r_zero(uint32_t index, uint8_t report_name){
  volatile uint8_t test_fail = 0;
  volatile uint32_t readback_val_mepc = 0x0;
  volatile uint32_t readback_val_mie = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  cvprintf(V_MEDIUM, "\nTesting write to mie, should not trap and readback 0\n");
  __asm__ volatile ( R"(
      addi t0, x0, -1
      csrrw x0, mepc, t0
      csrrw x0, mie, t0
      csrrw %[mie], mie, x0
      csrrw %[mepc], mepc, x0
  )"
      : [mepc] "=r"(readback_val_mepc), [mie] "=r"(readback_val_mie)
      :
      : "t0"
      );

  test_fail = (readback_val_mepc != 0xfffffffe) || (readback_val_mie != 0);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!un", name);
    cvprintf(V_MEDIUM, "\nMIE: 0x%08lx, MEPC: 0x%08lx\n", readback_val_mie, readback_val_mepc);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t w_mip_notrap_r_zero(uint32_t index, uint8_t report_name){
  volatile uint8_t test_fail = 0;
  volatile uint32_t readback_val_mepc = 0x0;
  volatile uint32_t readback_val_mip = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  cvprintf(V_MEDIUM, "\nTesting write to mip, should not trap and readback 0\n");
  __asm__ volatile ( R"(
      addi t0, x0, -1
      csrrw x0, mepc, t0
      csrrw x0, mip, t0
      csrrw %[mip], mip, x0
      csrrw %[mepc], mepc, x0
  )"
      : [mepc] "=r"(readback_val_mepc), [mip] "=r"(readback_val_mip)
      :
      : "t0"
      );

  // Expect all bits of mepc to remain as written (sans the last bit that is cleared by hw)
  // mip should read all zeroes after writing all f's
  test_fail = (readback_val_mepc != 0xfffffffe) || ( readback_val_mip != 0);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    cvprintf(V_MEDIUM, "\nMIP: 0x%08lx, MEPC: 0x%08lx\n", readback_val_mip, readback_val_mepc);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t w_mtvt_rd_alignment(uint32_t index, uint8_t report_name){
  volatile uint8_t test_fail = 0;
  volatile uint32_t mtvt_initial_val = 0x0;
  volatile uint32_t readback_val_mtvt = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  cvprintf(V_MEDIUM, "\nTesting mtvt alignment\n");

  // Clear mtvt
  __asm__ volatile ( R"(
      csrrw %[mtvt_init], 0x307, x0
      csrrw %[mtvt_rb], 0x307, %[mtvt_init]
  )"
      : [mtvt_init] "=r"(mtvt_initial_val), [mtvt_rb] "+r"(readback_val_mtvt)
      :
      :
      );

  // All bits should be zeroed
  test_fail += readback_val_mtvt;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  __asm__ volatile ( R"(
      addi t0, x0, -1
      csrrw %[mtvt_init], 0x307, t0
      csrrw %[mtvt_rb], 0x307, %[mtvt_init]
  )"
      : [mtvt_init] "=r"(mtvt_initial_val), [mtvt_rb] "=r"(readback_val_mtvt)
      :
      :
      );

  // Check for correct alignment
  test_fail += ~(readback_val_mtvt >> max(CLIC_ID_WIDTH+2, 6));
  if (ABORT_ON_ERROR_IMMEDIATE) assert (test_fail == 0);
  cvprintf(V_HIGH, "\nmtvt readback after 0xffff_ffff write: 0x%08lx\n", readback_val_mtvt);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t w_mtvec_rd_alignment(uint32_t index, uint8_t report_name){
  volatile uint8_t test_fail = 0;
  volatile uint32_t mtvec_initial_val = 0x0;
  volatile uint32_t readback_val_mtvec = 0x0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  cvprintf(V_MEDIUM, "\nTesting mtvec alignment\n");

  // Clear mtvec
  __asm__ volatile ( R"(
      csrrw %[mtvec_init], mtvec, x0
      csrrw %[mtvec_rb], mtvec, %[mtvec_init]
  )"
      : [mtvec_init] "=r"(mtvec_initial_val),
        [mtvec_rb] "=r"(readback_val_mtvec)
      :
      :
      );

  // All bits above 2 should be zeroed
  test_fail += (readback_val_mtvec >> 2);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  __asm__ volatile ( R"(
      addi t0, x0, -1
      csrrw %[mtvec_init], mtvec, t0
      csrrw %[mtvec_rb], mtvec, %[mtvec_init]
  )"
      : [mtvec_init] "=r"(mtvec_initial_val),
        [mtvec_rb] "=r"(readback_val_mtvec)
      :
      :
      );

  // upper bits all writeable
  test_fail += ~(readback_val_mtvec >> MTVEC_ALIGN_BITS);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  // lower [MTVEC_ALIGN_BITS-1:2] bits not updated
  test_fail += ((readback_val_mtvec << (32 - MTVEC_ALIGN_BITS)) >> 2);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  cvprintf(V_HIGH, "\nmtvec readback after 0xffff_ffff write: 0x%08lx\n", readback_val_mtvec);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------
_Pragma("GCC push_options")
_Pragma("GCC optimize (\"O0\")")
// -----------------------------------------------------------------------------

__attribute__((naked)) void mtvt_code(void) {
    __asm__ volatile ( R"(
      .global mtvt_table
      .align 7
      mtvt_table:   .long . + 4096
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
    )"
    );
}

// -----------------------------------------------------------------------------

__attribute__((naked)) void mtvt_code_destination_blocked(void) {
    __asm__ volatile ( R"(
      .global mtvt_table_mret
      .global mtvt_table_mret_dest
      .align 7
      mtvt_table_mret:   .long . + 4096
      mtvt_table_mret_1: .long . + 4092
      mtvt_table_mret_2: .long . + 4088
      mtvt_table_mret_3: .long . + 4084
      mtvt_table_mret_4: .long . + 4080
      .space 100, 0x0
      mtvt_table_mret_30: .long . + 3976
      mtvt_table_mret_31: .long . + 3972
      mtvt_table_mret_32: .long . + 3968
      .space 3952, 0x0
      mtvt_table_mret_1021: .long . + 12
      mtvt_table_mret_1022: .long . + 8
      mtvt_table_mret_1023: .long . + 4

      mtvt_table_mret_dest: jal zero, m_fast14_irq_handler
    )"
    );
}

// -----------------------------------------------------------------------------
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

    # Turn off interrupt request
    add a0, zero, zero
    add a1, zero, zero
    call vp_assert_irq

    # Store g_mepc_triggered
    lw s0, g_mepc_triggered
    csrrs s1, mepc, zero
    sw s1, 0(s0)

    # Check if we should skip jump to recovery code
    lw s0, g_recovery_enable
    lw s1, 0(s0)
    beq s1, zero, 5f

    addi s2, zero, 1
    beq s1, s2, 1f

    addi s2, zero, 2
    beq s1, s2, 2f

    addi s2, zero, 3
    beq s1, s2, 3f

    # First test with recovery_pt
    1: add s1, zero, zero
    sw s1, 0(s0)
    # Get recovery mepc and replace mepc
    la s1, recovery_pt
    csrrw zero, mepc, s1
    jal zero, 4f

    # Second test with recovery_pt_mret
    2: add s1, zero, zero
    sw s1, 0(s0)
    # Get recovery mepc and replace mepc
    la s1, recovery_pt_mret
    csrrw zero, mepc, s1
    jal zero, 4f

    # Third test with recovery_pt_mret_ptr
    3: add s1, zero, zero
    sw s1, 0(s0)
    # Get recovery mepc and replace mepc
    la s1, recovery_pt_mret_ptr
    csrrw zero, mepc, s1

    # clear mcause, set mpp
    4: lui s1, 0x30000
    csrrw zero, mcause, s1

    5:
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

// -----------------------------------------------------------------------------

uint32_t invalid_mtvt_ptr_exec(uint32_t index, uint8_t report_name) {

  volatile uint8_t test_fail = 0;

  // These needs to be volatile to prevent loop optimization
  //volatile uint8_t never = 0;
  volatile uint32_t no_timeout_threshold = 10;
  //volatile uint32_t mepc_triggered = 0x0;
  volatile uint32_t addr = 0x0;
  //volatile uint32_t clic_vector = 0x0;
  volatile clic_t clic_vector = { 0 };

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Write table location to mtvt and enable interrupts
  __asm__ volatile ( R"(
    csrrw x0, 0x307, %[mtvt]
    csrrsi x0, mstatus, 0x8
  )"
      :
      : [mtvt] "r"(&mtvt_table)
      :
      );

  // Pre-PMP setting, sanity check
  cvprintf(V_DEBUG, "mtvt: %08x, %08x\n", &mtvt_table, (uint32_t *)mtvt_table);
  clic_vector = (clic_t){
                  .fields.irq = 0x1,
                  .fields.id    = 0x3,
                  .fields.level = 0x81,
                  .fields.priv  = 0x3,
                  .fields.shv   = 0x1
  };

  no_timeout_threshold = 10;
  *g_mepc_triggered = 0;
  // Instruct clic_interrupt_vp to assert interrupt declared above
  vp_assert_irq(clic_vector.raw, 0);

  // Wait for interrupt
  while (no_timeout_threshold) {
    no_timeout_threshold--;
  }
  test_fail += (*g_mepc_triggered ? 0 : 1);
  cvprintf(V_MEDIUM, "Expect non-zero mepc, MEPC = 0x%08lx\n", *g_mepc_triggered);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(*g_mepc_triggered != 0);

  clic_vector = (clic_t){
                  .fields.irq = 0x1,
                  .fields.id    = (0x1 << CLIC_ID_WIDTH) - 1,
                  .fields.level = 0xff,
                  .fields.priv  = 0x3,
                  .fields.shv   = 0x1
  };

  no_timeout_threshold = 10;
  *g_mepc_triggered = 0;
  // Instruct clic_interrupt_vp to assert interrupt declared above
  vp_assert_irq(clic_vector.raw, 0);

  // Wait for interrupt
  while (no_timeout_threshold) {
    no_timeout_threshold--;
  }
  test_fail += (*g_mepc_triggered ? 0 : 1);
  cvprintf(V_MEDIUM, "Expect non-zero mepc, MEPC = 0x%08lx\n", *g_mepc_triggered);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(*g_mepc_triggered != 0);

  // Set PMP configuration
  __asm__ volatile ( R"(
    la %[addr], mtvt_table;
    srli %[addr], %[addr], 2
    csrrw x0, pmpaddr0, %[addr]
    la %[addr], mtvt_table + 128*4
    srli %[addr], %[addr], 2
    csrrw x0, pmpaddr1, %[addr]
    addi %[addr], x0, -1
    csrrw x0, pmpaddr2, %[addr]
  )"
      : [addr] "+r"(addr)
      :
      : "t0"
      );

  set_mseccfg((mseccfg_t){
      .rlb  = 1,
      .mmwp = 0,
      .mml  = 0
    });

  set_pmpcfg((pmpcfg_t){
      .reg_no = 0,
      .lock = 0,
      .mode = TOR,
      .execute = 1,
      .write = 1,
      .read = 1
    });

  set_pmpcfg((pmpcfg_t){
      .reg_no = 1,
      .lock = 1,
      .mode = TOR,
      .execute = 0,
      .write = 0,
      .read = 0
    });

  set_pmpcfg((pmpcfg_t){
      .reg_no = 2,
      .lock = 0,
      .mode = TOR,
      .execute = 1,
      .write = 1,
      .read = 1
    });

  clic_vector = (clic_t){
                      .fields.irq   = 0x1,
                      .fields.id    = 0x4,
                      .fields.level = 0x55,
                      .fields.priv  = 0x3,
                      .fields.shv   = 0x1
                };

  no_timeout_threshold = 10;
  *g_mepc_triggered = 0;
  *g_recovery_enable = 1;
  test_fail_asm = 0;
  // Instruct clic_interrupt_vp to assert interrupt declared above
  vp_assert_irq(clic_vector.raw, 0);

  // Wait for interrupt
  while (no_timeout_threshold) {
    no_timeout_threshold--;
  }

  __asm__ volatile ( R"(
    .extern test_fail_asm
    # This should never execute (deliberate dead code)
    la t0, test_fail_asm
    lw t1, 0(t0)
    addi t1, t1, 1
    sw t1, 0(t0)
    # Execution should continue here
    .global recovery_pt
    recovery_pt: add x0, x0, x0
  )":::);

  __asm__ volatile ( R"(
    lui t0, 0x40000
    csrrc zero, mcause, t0
  )" ::: "t0");

  cvprintf(V_LOW, "Entered recovery point, due to unrecoverable clic ptr trap, mepc: %08x, expected: %08x\n", *g_mepc_triggered, (uint32_t)(&mtvt_table + 4));
  test_fail += test_fail_asm || *g_mepc_triggered != (uint32_t)(&mtvt_table + 4);


  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t invalid_mtvt_ptr_exec_mret(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;

  volatile uint32_t addr = 0x0;

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Set PMP configuration
  __asm__ volatile ( R"(
    la %[addr], mtvt_table_mret_dest
    srli %[addr], %[addr], 2
    csrrw x0, pmpaddr0, %[addr]
    la %[addr], mtvt_table_mret_dest + 4
    srli %[addr], %[addr], 2
    csrrw x0, pmpaddr1, %[addr]
    addi %[addr], x0, -1
    csrrw x0, pmpaddr2, %[addr]
  )"
      : [addr] "+r"(addr)
      :
      : "t0"
      );

  set_mseccfg((mseccfg_t){
      .rlb  = 1,
      .mmwp = 0,
      .mml  = 0
    });

  set_pmpcfg((pmpcfg_t){
      .reg_no = 0,
      .lock = 0,
      .mode = TOR,
      .execute = 1,
      .write = 1,
      .read = 1
    });

  set_pmpcfg((pmpcfg_t){
      .reg_no = 1,
      .lock = 1,
      .mode = TOR,
      .execute = 0,
      .write = 0,
      .read = 0
    });

  set_pmpcfg((pmpcfg_t){
      .reg_no = 2,
      .lock = 0,
      .mode = TOR,
      .execute = 1,
      .write = 1,
      .read = 1
    });

  *g_mepc_triggered = 0;
  *g_recovery_enable = 2;
  test_fail_asm = 0;

  __asm__ volatile ( R"(
    la t0, mtvt_table_mret_4
    csrrw zero, mepc, t0
    # set minhv and mpp = M
    lui t0, 0x70000
    csrrs zero, mcause, t0
  )"::: "t0");

  __asm__ volatile ( R"(
    mret
  )":::);

  __asm__ volatile ( R"(
    .extern test_fail_asm
    # This should never execute (deliberate dead code)
    la t0, test_fail_asm
    lw t1, 0(t0)
    addi t1, t1, 1
    sw t1, 0(t0)
    # Execution should continue here
    .global recovery_pt_mret
    recovery_pt_mret: add x0, x0, x0
  )":::);

  __asm__ volatile ( R"(
    lui t0, 0x40000
    csrrc zero, mcause, t0
  )" ::: "t0");

  cvprintf(V_LOW, "Entered recovery point, due to unrecoverable mret ptr dest. trap, mepc: %08x, expected: %08x\n", *g_mepc_triggered, (uint32_t)(&mtvt_table_mret_dest));
  test_fail += test_fail_asm || *g_mepc_triggered != (uint32_t)(&mtvt_table_mret_dest);

  // Set PMP configuration
  __asm__ volatile ( R"(
    la %[addr], mtvt_table_mret_3
    srli %[addr], %[addr], 2
    csrrw x0, pmpaddr0, %[addr]
    la %[addr], mtvt_table_mret_4
    srli %[addr], %[addr], 2
    csrrw x0, pmpaddr1, %[addr]
    addi %[addr], x0, -1
    csrrw x0, pmpaddr2, %[addr]
  )"
      : [addr] "+r"(addr)
      :
      : "t0"
      );

  set_mseccfg((mseccfg_t){
      .rlb  = 1,
      .mmwp = 0,
      .mml  = 0
    });

  set_pmpcfg((pmpcfg_t){
      .reg_no = 0,
      .lock = 0,
      .mode = TOR,
      .execute = 1,
      .write = 1,
      .read = 1
    });

  set_pmpcfg((pmpcfg_t){
      .reg_no = 1,
      .lock = 1,
      .mode = TOR,
      .execute = 0,
      .write = 0,
      .read = 0
    });

  set_pmpcfg((pmpcfg_t){
      .reg_no = 2,
      .lock = 0,
      .mode = TOR,
      .execute = 1,
      .write = 1,
      .read = 1
    });

  *g_mepc_triggered = 0;
  *g_recovery_enable = 3;
  test_fail_asm = 0;

  __asm__ volatile ( R"(
    la t0, mtvt_table_mret_3
    csrrw zero, mepc, t0
    # set minhv and mpp = M
    lui t0, 0x70000
    csrrs zero, mcause, t0
  )"::: "t0");

  __asm__ volatile ( R"(
    mret
  )":::);

  __asm__ volatile ( R"(
    .extern test_fail_asm
    # This should never execute (deliberate dead code)
    la t0, test_fail_asm
    lw t1, 0(t0)
    addi t1, t1, 1
    sw t1, 0(t0)
    # Execution should continue here
    .global recovery_pt_mret_ptr
    recovery_pt_mret_ptr: add x0, x0, x0
  )":::);

  __asm__ volatile ( R"(
    lui t0, 0x40000
    csrrc zero, mcause, t0
  )" ::: "t0");

  cvprintf(V_LOW, "Entered recovery point, due to unrecoverable mret ptr trap, mepc: %08x, expected: %08x\n", *g_mepc_triggered, (uint32_t)(&mtvt_table_mret + 3));
  test_fail += test_fail_asm || *g_mepc_triggered != (uint32_t)(&mtvt_table_mret + 3);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t r_mnxti_without_irq(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile uint32_t mnxti_rval = 0;

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // CSRRS ro
  __asm__ volatile ( R"(
    csrrs %[rd], 0x345, x0
  )":[rd] "=r"(mnxti_rval)
    ::
  );

  test_fail += (uint8_t)(mnxti_rval ? 1 : 0);  // rval should be zero

  // CSRRSI ro
  __asm__ volatile ( R"(
    csrrsi %[rd], 0x345, 0
  )":[rd] "=r"(mnxti_rval)
    ::
  );

  test_fail += (uint8_t)(mnxti_rval ? 1 : 0);  // rval should be zero

  // CSRRCI ro
  __asm__ volatile ( R"(
    csrrci %[rd], 0x345, 0
  )":[rd] "=r"(mnxti_rval)
    ::
  );

  test_fail += (uint8_t)(mnxti_rval ? 1 : 0);  // rval should be zero

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t rw_mnxti_without_irq_illegal(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile uint32_t mnxti_rval = 0;

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // CSRRC rw - use sp as that is non-zero to ensure that we actually try clearing (illegal)
  *g_expect_illegal = 1;
  __asm__ volatile ( R"(
    .option push
    .option norvc
    csrrc %[rd], 0x345, sp
    nop
    .option pop
  )":[rd] "=r"(mnxti_rval)
    ::
  );

  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  // CSRRC rw - use zero to do no clear operation (illegal)
  *g_expect_illegal = 1;
  __asm__ volatile ( R"(
    .option push
    .option norvc
    csrrc %[rd], 0x345, zero
    nop
    .option pop
  )":[rd] "=r"(mnxti_rval)
    ::
  );

  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));


  // CSRRW rw - use sp as that is non-zero to ensure that we actually try writing (illegal)
  *g_expect_illegal = 1;
  __asm__ volatile ( R"(
    .option push
    .option norvc
    csrrw %[rd], 0x345, sp
    nop
    .option pop
  )":[rd] "=r"(mnxti_rval)
    ::
  );

  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  // CSRRW rw - use zero to ensure that we actually try writing all zeros (illegal)
  *g_expect_illegal = 1;
  __asm__ volatile ( R"(
    .option push
    .option norvc
    csrrw %[rd], 0x345, sp
    nop
    .option pop
  )":[rd] "=r"(mnxti_rval)
    ::
  );

  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  // CSRRWI rw - use all ones to ensure that we actually try writing (illegal)
  *g_expect_illegal = 1;
  __asm__ volatile ( R"(
    .option push
    .option norvc
    csrrwi %[rd], 0x345, 0x1f
    nop
    .option pop
  )":[rd] "=r"(mnxti_rval)
    ::
  );

  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  // CSRRWI rw - use all zeroes to ensure that we actually try clearing the register (illegal)
  *g_expect_illegal = 1;
  __asm__ volatile ( R"(
    .option push
    .option norvc
    csrrwi %[rd], 0x345, 0x0
    nop
    .option pop
  )":[rd] "=r"(mnxti_rval)
    ::
  );

  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  // CSRRS with rs1 != x0 - illegal
  *g_expect_illegal = 31;
  __asm__ volatile ( R"(
    .option push
    .option norvc
    csrrs %[rd], 0x345, x1
    csrrs %[rd], 0x345, x2
    csrrs %[rd], 0x345, x3
    csrrs %[rd], 0x345, x4
    csrrs %[rd], 0x345, x5
    csrrs %[rd], 0x345, x6
    csrrs %[rd], 0x345, x7
    csrrs %[rd], 0x345, x8
    csrrs %[rd], 0x345, x9
    csrrs %[rd], 0x345, x10
    csrrs %[rd], 0x345, x11
    csrrs %[rd], 0x345, x12
    csrrs %[rd], 0x345, x13
    csrrs %[rd], 0x345, x14
    csrrs %[rd], 0x345, x15
    csrrs %[rd], 0x345, x16
    csrrs %[rd], 0x345, x17
    csrrs %[rd], 0x345, x18
    csrrs %[rd], 0x345, x19
    csrrs %[rd], 0x345, x20
    csrrs %[rd], 0x345, x21
    csrrs %[rd], 0x345, x22
    csrrs %[rd], 0x345, x23
    csrrs %[rd], 0x345, x24
    csrrs %[rd], 0x345, x25
    csrrs %[rd], 0x345, x26
    csrrs %[rd], 0x345, x27
    csrrs %[rd], 0x345, x28
    csrrs %[rd], 0x345, x29
    csrrs %[rd], 0x345, x30
    csrrs %[rd], 0x345, x31
    nop
    .option pop
  )":[rd] "=r"(mnxti_rval)
    ::
  );

  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  // CSRRSI with imm[0, 2, 4] = 1 - illegal
  *g_expect_illegal = 11;
  __asm__ volatile ( R"(
    .option push
    .option norvc
    # bit 0, 2, 4
    csrrsi %[rd], 0x345, 1 << 0 | 1 << 2 | 1 << 4
    # bit 0
    csrrsi %[rd], 0x345, 1 << 0
    # bit 2
    csrrsi %[rd], 0x345, 1 << 2
    # bit 4
    csrrsi %[rd], 0x345, 1 << 4
    # all bits
    csrrsi %[rd], 0x345, 0x1f
    # all bits without bit 0 and 2
    csrrsi %[rd], 0x345, 0x1f & ~(1 << 0) & ~(1 << 2)
    # all bits without bit 2 and 4
    csrrsi %[rd], 0x345, 0x1f & ~(1 << 2) & ~(1 << 4)
    # all bits without bit 0 and 4
    csrrsi %[rd], 0x345, 0x1f & ~(1 << 0) & ~(1 << 4)
    # all bits without 0
    csrrsi %[rd], 0x345, 0x1f & ~(1 << 0)
    # all bits without 2
    csrrsi %[rd], 0x345, 0x1f & ~(1 << 2)
    # all bits without 4
    csrrsi %[rd], 0x345, 0x1f & ~(1 << 4)
    nop
    .option pop
  )":[rd] "=r"(mnxti_rval)
    ::
  );

  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t r_mnxti_with_pending_irq(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile clic_t clic_irq_vector = { 0 };
  volatile uint32_t no_timeout_threshold = 1000;

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_special_handler_idx = 3;
  // Need an mret to clear out mintstatus -> take an interrupt and return
  __asm__ volatile ( R"(
   csrrsi zero, 0x345, 0x8
  )":::);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = 0x1,
    .fields.level = 0xff,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  vp_assert_irq(clic_irq_vector.raw, 0);

  // Enable interrupts
  __asm__ volatile (R"(
    csrrsi x0, 0x345, 0x8
  )":::);

  *g_special_handler_idx = 1;

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = 0x1,
    .fields.level = 0x1,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  // Instruct clic_interrupt_vp to assert interrupt declared above
  vp_assert_irq(clic_irq_vector.raw, 1);

  // Wait for interrupt
  no_timeout_threshold = 100;
  while (no_timeout_threshold) {
    no_timeout_threshold--;
  }

  vp_assert_irq(0, 0);
  test_fail += *g_irq_handler_reported_error;

  *g_special_handler_idx = 1;
  vp_assert_irq(clic_irq_vector.raw, 1);
  // Wait for interrupt
  no_timeout_threshold = 100;
  while (no_timeout_threshold) {
    no_timeout_threshold--;
  }

  vp_assert_irq(0, 0);
  test_fail += *g_irq_handler_reported_error;

  *g_special_handler_idx = 1;
  vp_assert_irq(clic_irq_vector.raw, 1);
  // Wait for interrupt
  no_timeout_threshold = 100;
  while (no_timeout_threshold) {
    no_timeout_threshold--;
  }

  vp_assert_irq(0, 0);
  test_fail += *g_irq_handler_reported_error;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t r_mnxti_with_irq_handler(uint32_t min_id, uint32_t max_id, uint32_t min_lvl, uint32_t max_lvl) {
  volatile clic_t clic_irq_vector = { 0 };
  volatile uint32_t mnxti_rval = 0;
  volatile mintstatus_t mintstatus_rval = { 0 };
  volatile mcause_t mcause_rval = { 0 };

  *g_asserted_irq_idx = get_random_interrupt_number(min_id, max_id);
  *g_asserted_irq_lvl = get_random_interrupt_level(min_lvl, max_lvl);
  cvprintf(V_DEBUG, "called r_mnxti_with_irq_handler, irq: %08x, lvl: %08x\n", *g_asserted_irq_idx, *g_asserted_irq_lvl);

  // Write mnxti to trigger mcause updates, get minstatus.mil and mcause.mpil for manual update
  __asm__ volatile ( R"(
    csrrci %[rd1], 0x345, 0x8
    csrrs  %[rd2], 0xfb1, zero
    csrrs  %[rd3], mcause, zero
  )":[rd1] "=r"(mnxti_rval),
     [rd2] "=r"(mintstatus_rval.raw),
     [rd3] "=r"(mcause_rval.raw)
    ::
  );

  cvprintf(V_DEBUG, "Read mnxti (oic): %08x, mintstatus.mil: %02x, mcause.mpil: %02x\n", mnxti_rval, mintstatus_rval.fields.mil, mcause_rval.clic.mpil);

  // Update mcause.mpil (instead of nesting interrupts), store previous value
  mcause_rval.clic.mpil = mintstatus_rval.fields.mil;

  __asm__ volatile ( R"(
    csrrw %[rd2], mcause, %[rd2]
  )":[rd2] "+r"(mcause_rval.raw)
    ::
  );

  // Assert new interrupt within specified parameters
  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = *g_asserted_irq_idx,
    .fields.level = *g_asserted_irq_lvl,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  vp_assert_irq(clic_irq_vector.raw, 0);

  // Read mnxti to check if correct value can be read
  // then
  // Revert mcause.mpil to reset mpil prior to mret to restore original interrupt context

  __asm__ volatile ( R"(
    csrrci %[rd1], 0x345, 0
    csrrw %[rd2], mcause, %[rd2]
  )":[rd1] "=r"(mnxti_rval),
     [rd2] "+r"(mcause_rval.raw)
    ::
  );

  cvprintf(V_DEBUG, "Read mnxti (nic): %08x\n", mnxti_rval);

  return mnxti_rval;
}

// -----------------------------------------------------------------------------

uint32_t r_mnxti_with_lower_lvl_pending_irq(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile clic_t clic_irq_vector = { 0 };
  volatile uint32_t no_timeout_threshold = 100;

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_special_handler_idx = 2;
  // Enable interrupts
  __asm__ volatile (R"(
    csrrsi x0, mstatus, 0x8
  )":::);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = 0x1,
    .fields.level = 0xff,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  no_timeout_threshold = 100;
  // Instruct clic_interrupt_vp to assert interrupt declared above
  vp_assert_irq(clic_irq_vector.raw, 1);

  // Wait for interrupt
  while (no_timeout_threshold) {
    no_timeout_threshold--;
  }

  test_fail += *g_irq_handler_reported_error;

  *g_special_handler_idx = 2;
  vp_assert_irq(clic_irq_vector.raw, 1);
  // Wait for interrupt
  no_timeout_threshold = 100;
  while (no_timeout_threshold) {
    no_timeout_threshold--;
  }

  test_fail += *g_irq_handler_reported_error;

  *g_special_handler_idx = 2;
  vp_assert_irq(clic_irq_vector.raw, 1);
  // Wait for interrupt
  no_timeout_threshold = 100;
  while (no_timeout_threshold) {
    no_timeout_threshold--;
  }

  test_fail += *g_irq_handler_reported_error;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t w_mnxti_side_effects(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile uint32_t previous_lvl = 0;
  volatile uint32_t previous_idx = 0;
  volatile mcause_t mcause_rval = { 0 };
  volatile mintstatus_t mintstatus_rval = { 0 };
  volatile clic_t clic_irq_vector = { 0 };

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  vp_assert_irq(0, 0);
  *g_special_handler_idx = 3;
  // Need an mret to clear out mintstatus -> take an interrupt and return
  __asm__ volatile ( R"(
   csrrsi zero, 0x345, 0x8
  )":::);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = 0x1,
    .fields.level = 0xff,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  vp_assert_irq(clic_irq_vector.raw, 0);

  // Disable interrupts
  __asm__ volatile ( R"(
   csrrci zero, 0x345, 0x8
  )":::);

  // Disable interrupts (write side-effects should occur):
  __asm__ volatile (R"(
    csrrci zero, 0x345, 0x8
    csrrs %[rd1], 0xfb1, zero
    csrrs %[rd2], mcause, zero
  )":[rd1] "=r"(mintstatus_rval.raw),
     [rd2] "=r"(mcause_rval.raw)
    ::);

  test_fail += mcause_rval.clic.interrupt != 0;
  test_fail += mcause_rval.clic.exccode   != 0;
  test_fail += mintstatus_rval.fields.mil != 0;

  *g_asserted_irq_idx = get_random_interrupt_number(0, NUM_INTERRUPTS);
  *g_asserted_irq_lvl = get_random_interrupt_level(0, NUM_INTERRUPT_LVLS);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = *g_asserted_irq_idx,
    .fields.level = *g_asserted_irq_lvl,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  // asserted interrupt should not be taken (not enabled)
  vp_assert_irq(clic_irq_vector.raw, 0);

  __asm__ volatile (R"(
    csrrci zero, 0x345, 0x8
    csrrs %[rd1], 0xfb1, zero
    csrrs %[rd2], mcause, zero
  )":[rd1] "=r"(mintstatus_rval.raw),
     [rd2] "=r"(mcause_rval.raw)
    ::);

  cvprintf(V_DEBUG, "mintstatus.mil: %02x, mcause.exccode: %08x, expected: lvl %02x, id %08x\n", mintstatus_rval.fields.mil, mcause_rval.clic.exccode, *g_asserted_irq_lvl, *g_asserted_irq_idx);

  test_fail += mcause_rval.clic.interrupt != 1;
  test_fail += mcause_rval.clic.exccode   != *g_asserted_irq_idx;
  test_fail += mintstatus_rval.fields.mil != *g_asserted_irq_lvl;

  // Higher lvl than previously set
  *g_asserted_irq_idx = get_random_interrupt_number(*g_asserted_irq_idx, NUM_INTERRUPTS);
  *g_asserted_irq_lvl = get_random_interrupt_level(*g_asserted_irq_lvl, NUM_INTERRUPT_LVLS);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = *g_asserted_irq_idx,
    .fields.level = *g_asserted_irq_lvl,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  // asserted interrupt should not be taken (not enabled)
  vp_assert_irq(clic_irq_vector.raw, 0);

  __asm__ volatile (R"(
    csrrci zero, 0x345, 0x8
    csrrs %[rd1], 0xfb1, zero
    csrrs %[rd2], mcause, zero
  )":[rd1] "=r"(mintstatus_rval.raw),
     [rd2] "=r"(mcause_rval.raw)
    ::);

  cvprintf(V_DEBUG, "mintstatus.mil: %02x, mcause.exccode: %08x, expected: lvl %02x, id %08x\n", mintstatus_rval.fields.mil, mcause_rval.clic.exccode, *g_asserted_irq_lvl, *g_asserted_irq_idx);

  if (*g_asserted_irq_idx < NUM_INTERRUPTS && *g_asserted_irq_lvl < NUM_INTERRUPT_LVLS) {
    test_fail += mcause_rval.clic.interrupt != 1;
    test_fail += mcause_rval.clic.exccode   != *g_asserted_irq_idx;
    test_fail += mintstatus_rval.fields.mil != *g_asserted_irq_lvl;
  } else {
    test_fail += mcause_rval.clic.interrupt != 0;
    test_fail += mcause_rval.clic.exccode   != 0;
    test_fail += mintstatus_rval.fields.mil != 0;
  }

  // Lower lvl than previously set
  previous_idx = *g_asserted_irq_idx;
  previous_lvl = *g_asserted_irq_lvl;
  *g_asserted_irq_idx = get_random_interrupt_number(0, previous_idx-1);
  *g_asserted_irq_lvl = get_random_interrupt_level(0, previous_lvl-1);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = *g_asserted_irq_idx,
    .fields.level = *g_asserted_irq_lvl,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  // asserted interrupt should not be taken (not enabled)
  vp_assert_irq(clic_irq_vector.raw, 0);

  cvprintf(V_DEBUG, "mintstatus.mil: %02x, mcause.exccode: %08x, expected: lvl %02x, id %08x\n", mintstatus_rval.fields.mil, mcause_rval.clic.exccode, previous_lvl, previous_idx);
  test_fail += mcause_rval.clic.interrupt != 1;
  test_fail += mcause_rval.clic.exccode   != previous_idx;
  test_fail += mintstatus_rval.fields.mil != previous_lvl;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;

}

// -----------------------------------------------------------------------------

uint32_t rw_mscratchcsw(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile uint32_t reg_backup_1 = 0;
  volatile uint32_t reg_backup_2 = 0;
  volatile mstatus_t mstatus_rval = { 0 };
  volatile uint32_t mscratch = 0;

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  __asm__ volatile (R"(
    csrrs %[rd1], mstatus, zero
  )":[rd1] "=r"(mstatus_rval.raw)
    ::);

  mstatus_rval.fields.mpp = 0x0;

  // Set mpp to zero and attempt swap
  __asm__ volatile (R"(
    csrrw %[rd1], mstatus, %[rd1]
    add   %[rd2], sp, zero
    csrrw %[rd3], 0x348, sp
    csrrs %[rd4], mscratch, zero
    csrrw sp, 0x348, %[rd3]
    add   %[rd3], sp, zero
    csrrw zero, mscratch, zero
  )":[rd1] "+r"(mstatus_rval.raw),
     [rd2] "=r"(reg_backup_1),
     [rd3] "+r"(reg_backup_2),
     [rd4] "=r"(mscratch)
    ::);

  cvprintf(V_DEBUG, "Reg1 read: %08x, mscratchcsw swap result: %08x, mscratch: %08x\n", reg_backup_1, reg_backup_2, mscratch);
  test_fail += reg_backup_1 != reg_backup_2 || reg_backup_1 != mscratch;

  mstatus_rval.fields.mpp = 0x3;
  // Set mpp to 0x3 and attempt swap
  __asm__ volatile (R"(
    csrrw %[rd1], mstatus, %[rd1]
    add   %[rd2], sp, zero
    csrrw %[rd3], 0x348, sp
    csrrs %[rd4], mscratch, zero
    csrrw sp, 0x348, %[rd3]
  )":[rd1] "+r"(mstatus_rval.raw),
     [rd2] "=r"(reg_backup_1),
     [rd3] "=r"(reg_backup_2),
     [rd4] "=r"(mscratch)
    ::);

  cvprintf(V_DEBUG, "Reg1 read: %08x, mscratchcsw swap result: %08x, mscratch: %08x\n", reg_backup_1, reg_backup_2, mscratch);
  test_fail += reg_backup_1 != reg_backup_2 || mscratch != 0;

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t rw_mscratchcsw_illegal(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile uint32_t reg_backup_1 = 0;
  volatile mstatus_t mstatus_rval = { 0 };

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Set mpp to 0x3 and attempt swap
  mstatus_rval.fields.mpp = 0x3;
  __asm__ volatile (R"( csrrs zero, mstatus, %[rs1])"
    :: [rs1] "r"(mstatus_rval.raw):);

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrs  %[rd], 0x348, sp)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrs  zero,  0x348, sp)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrc  %[rd], 0x348, sp)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrc  zero,  0x348, sp)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrs  %[rd], 0x348, zero)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrs  zero,  0x348, zero)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrc  %[rd], 0x348, zero)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrc  zero,  0x348, zero)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrsi %[rd], 0x348, 0x1f)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrsi zero,  0x348, 0x1f)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrsi %[rd], 0x348, 0x0)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrsi zero,  0x348, 0x0)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrci %[rd], 0x348, 0x1f)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrci zero,  0x348, 0x1f)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrci %[rd], 0x348, 0x0)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrci zero,  0x348, 0x0)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrw  zero,  0x348, %[rs1])"
      :: [rs1] "r"(reg_backup_1) :);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrw  zero,  0x348, zero)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrw  %[rd], 0x348, 0x0)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  // Set mpp to 0x0 and attempt swap
  mstatus_rval.fields.mpp = 0x3;
  __asm__ volatile (R"( csrrc zero, mstatus, %[rs1])"
    :: [rs1] "r"(mstatus_rval.raw):);

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrs  %[rd], 0x348, sp)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrs  zero,  0x348, sp)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrc  %[rd], 0x348, sp)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrc  zero,  0x348, sp)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrs  %[rd], 0x348, zero)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrs  zero,  0x348, zero)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrc  %[rd], 0x348, zero)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrc  zero,  0x348, zero)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrsi %[rd], 0x348, 0x1f)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrsi zero,  0x348, 0x1f)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrsi %[rd], 0x348, 0x0)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrsi zero,  0x348, 0x0)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrci %[rd], 0x348, 0x1f)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrci zero,  0x348, 0x1f)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrci %[rd], 0x348, 0x0)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrci zero,  0x348, 0x0)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrw  zero,  0x348, %[rs1])"
      :: [rs1] "r"(reg_backup_1) :);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrw  zero,  0x348, zero)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrw  %[rd], 0x348, 0x0)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t rw_mscratchcswl(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile uint32_t reg_backup_1 = 0;
  volatile uint32_t reg_backup_2 = 0;
  volatile uint32_t mscratch = 0;
  volatile mcause_t mcause_rval = { 0 };
  volatile clic_t clic_irq_vector = { 0 };
  volatile mintstatus_t mintstatus_rval = { 0 };

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Need an mret to clear out mintstatus due to previous tests -> take an interrupt and return
  *g_special_handler_idx = 3;
  mcause_rval.clic.mpil = 0;
  __asm__ volatile ( R"(
   csrrw zero, mcause, %[rs1]
   csrrsi zero, 0x345, 0x8
  )":
   :[rs1] "r"(mcause_rval.raw)
   :);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = 0x1,
    .fields.level = 0xff,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  vp_assert_irq(clic_irq_vector.raw, 0);

  // Case 1:
  // No pending interrupt, mpil zero - no swap
  vp_assert_irq(0, 0);

  __asm__ volatile ( R"(
    csrrw zero, mscratch, zero
    add   %[rd1], sp, zero
    csrrw %[rd2], 0x349, sp
    csrrs %[rd3], mscratch, zero

    csrrs %[rd4], mcause, zero
    csrrs %[rd5], 0xfb1, zero
  )":[rd1] "=r"(reg_backup_1),
     [rd2] "=r"(reg_backup_2),
     [rd3] "=r"(mscratch),
     [rd4] "=r"(mcause_rval.raw),
     [rd5] "=r"(mintstatus_rval.raw)
    ::);

  cvprintf(V_DEBUG, "Reg1 read: %08x, mscratchcswl swap result: %08x, mscratch: %08x, mcause.mpil: %01x, minstatus.mil: %01x\n", reg_backup_1, reg_backup_2, mscratch, mcause_rval.clic.mpil, mintstatus_rval.fields.mil);
  test_fail += reg_backup_1 != reg_backup_2 || mscratch != 0;

  // Case 2:
  // Pending interrupt, mpil zero - swap

  // Disable interrupts with mnxti (write side-effects could occur):
  __asm__ volatile (R"(
    csrrci zero, 0x345, 0x8
  )":::);

  *g_asserted_irq_idx = get_random_interrupt_number(1, NUM_INTERRUPTS);
  *g_asserted_irq_lvl = get_random_interrupt_level(1, NUM_INTERRUPT_LVLS);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = *g_asserted_irq_idx,
    .fields.level = *g_asserted_irq_lvl,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  // asserted interrupt should not be taken (not enabled)
  vp_assert_irq(clic_irq_vector.raw, 0);

  // Disable interrupts with mnxti (write side-effects should occur):
  if (*g_asserted_irq_lvl != 0) {
    __asm__ volatile (R"(
      csrrw zero, mscratch, zero
      csrrci zero, 0x345, 0x8
      csrrs %[rd1], 0xfb1, zero
      csrrs %[rd2], mcause, zero
      add   %[rd3], sp, zero

      csrrw %[rd4], 0x349, sp
      csrrs %[rd5], mscratch, zero
      csrrw sp, 0x349, %[rd4]

      add   %[rd4], sp, zero
      csrrw zero, mscratch, zero
    )":[rd1] "=r"(mintstatus_rval.raw),
       [rd2] "=r"(mcause_rval.raw),
       [rd3] "=r"(reg_backup_1),
       [rd4] "=r"(reg_backup_2),
       [rd5] "=r"(mscratch)
      ::);
  }

  cvprintf(V_DEBUG, "Reg1 read: %08x, mscratchcswl swap result: %08x, mscratch: %08x, mcause.mpil: %01x, minstatus.mil: %01x\n", reg_backup_1, reg_backup_2, mscratch, mcause_rval.clic.mpil, mintstatus_rval.fields.mil);
  test_fail += reg_backup_1 != reg_backup_2 || reg_backup_1 != mscratch;
  vp_assert_irq(0, 0);

  // Case 3:
  // No pending interrupt, mpil non-zero - swap

  // Need an mret to clear out mintstatus -> take an interrupt and return
  *g_special_handler_idx = 3;
  mcause_rval.clic.mpil = 0;
  __asm__ volatile ( R"(
   csrrw zero, mcause, %[rs1]
   csrrsi zero, 0x345, 0x8
  )":
   :[rs1] "r"(mcause_rval.raw)
   :);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = 0x1,
    .fields.level = 0xff,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  vp_assert_irq(clic_irq_vector.raw, 0);

  vp_assert_irq(0, 0);

  mcause_rval.clic.mpil = get_random_interrupt_level(1, NUM_INTERRUPT_LVLS);

  // clear mscratch, update mintstatus.mil with mnxti, write nonzero value to mcause.mpil then run test
  __asm__ volatile ( R"(
    csrrw zero, mscratch, zero
    csrrci zero, 0x345, 0x8
    csrrw zero, mcause, %[rs1]
    csrrs %[rd5], 0xfb1, zero
    add   %[rd2], sp, zero

    csrrw %[rd3], 0x349, sp
    csrrs %[rd4], mscratch, zero
    csrrw sp, 0x349, %[rd3]

    add   %[rd3], sp, zero
    csrrw zero, mscratch, zero
  )":[rd2] "=r"(reg_backup_2),
     [rd3] "+r"(reg_backup_1),
     [rd4] "=r"(mscratch),
     [rd5] "=r"(mintstatus_rval.raw)
    :[rs1] "r"(mcause_rval.raw)
    :);

  cvprintf(V_DEBUG, "Reg1 read: %08x, mscratchcswl swap result: %08x, mscratch: %08x, mcause.mpil: %01x, mintstatus.mil: %01x\n", reg_backup_1, reg_backup_2, mscratch, mcause_rval.clic.mpil, mintstatus_rval.fields.mil);
  test_fail += reg_backup_1 != reg_backup_2 || reg_backup_1 != mscratch;

  // Case 4:
  // Pending interrupt, mpil non-zero - no swap

  // Need an mret to clear out mintstatus -> take an interrupt and return
  *g_special_handler_idx = 3;
  mcause_rval.clic.mpil = 0;
  __asm__ volatile ( R"(
   csrrw zero, mcause, %[rs1]
   csrrsi zero, 0x345, 0x8
  )":
   :[rs1] "r"(mcause_rval.raw)
   :);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = 0x1,
    .fields.level = 0xff,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  vp_assert_irq(clic_irq_vector.raw, 0);

  vp_assert_irq(0, 0);

  *g_asserted_irq_idx = get_random_interrupt_number(1, NUM_INTERRUPTS);
  *g_asserted_irq_lvl = get_random_interrupt_level(1, NUM_INTERRUPT_LVLS);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = *g_asserted_irq_idx,
    .fields.level = *g_asserted_irq_lvl,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  // asserted interrupt should not be taken (not enabled)
  vp_assert_irq(clic_irq_vector.raw, 0);
  mcause_rval.clic.mpil = get_random_interrupt_level(1, NUM_INTERRUPT_LVLS);

  __asm__ volatile ( R"(
    csrrw zero, mscratch, zero
    csrrci zero, 0x345, 0x8
    csrrw zero, mcause, %[rd2]

    csrrs %[rd1], 0xfb1, zero
    csrrs %[rd2], mcause, zero

    add   %[rd3], zero, sp

    csrrw %[rd4], 0x349, sp
    csrrs %[rd5], mscratch, zero
    csrrw sp, 0x349, %[rd4]

    add   %[rd4], sp, zero
    csrrw zero, mscratch, zero
  )":[rd1] "=r"(mintstatus_rval.raw),
     [rd2] "+r"(mcause_rval.raw),
     [rd3] "=r"(reg_backup_1),
     [rd4] "+r"(reg_backup_2),
     [rd5] "=r"(mscratch)
    ::);

  cvprintf(V_DEBUG, "Reg1 read: %08x, mscratchcswl swap result: %08x, mscratch: %08x, mcause.mpil: %01x, mintstatus.mil: %01x\n", reg_backup_1, reg_backup_2, mscratch, mcause_rval.clic.mpil, mintstatus_rval.fields.mil);
  test_fail += reg_backup_1 != reg_backup_2 || mscratch != 0;
  vp_assert_irq(0, 0);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t rw_mscratchcswl_illegal(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile uint32_t reg_backup_1 = 0;

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrs  %[rd], 0x349, sp)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrs  zero,  0x349, sp)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrc  %[rd], 0x349, sp)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrc  zero,  0x349, sp)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrs  %[rd], 0x349, zero)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrs  zero,  0x349, zero)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrc  %[rd], 0x349, zero)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrc  zero,  0x349, zero)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrsi %[rd], 0x349, 0x1f)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrsi zero,  0x349, 0x1f)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrsi %[rd], 0x349, 0x0)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrsi zero,  0x349, 0x0)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrci %[rd], 0x349, 0x1f)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrci zero,  0x349, 0x1f)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrci %[rd], 0x349, 0x0)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrci zero,  0x349, 0x0)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrw  zero,  0x349, %[rs1])"
      :: [rs1] "r"(reg_backup_1) :);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrw  zero,  0x349, zero)":::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  *g_expect_illegal = 1;
  __asm__ volatile (R"( csrrw  %[rd], 0x349, 0x0)"
      : [rd] "=r"(reg_backup_1) ::);
  test_fail += (uint8_t)((*g_expect_illegal ? 1 : 0));

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t mret_with_minhv(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail  = 0;
  volatile mcause_t mcause    = { 0 };
  volatile uint32_t check_val = 0;
  volatile uint32_t result    = 0;

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  __asm__ volatile ( R"(
    csrrs %[rd1], mcause, zero
  )":[rd1] "=r"(mcause.raw)
    ::);

  mcause.clic.minhv = 1;
  mcause.clic.mpp = 0x3;
  mcause.clic.mpie = 0;

  __asm__ volatile (R"(
    csrrw zero, mcause, %[mcause]
    la t0, 1f
    csrrw zero, mepc, t0
    mret
    addi %[check_val], zero, 42
    jal zero, 2f
    .align 4
    1: .word(2f)
    .space 0x100, 0x0
    2: addi %[result], %[check_val], 0
  )":[check_val] "+r"(check_val),
     [result] "=r"(result)
    :[mcause] "r"(mcause.raw)
    :"t0");

  // Clear minhv-bit
  mcause.clic.minhv = 0;

  __asm__ volatile (R"(
    csrrw zero, mcause, %[mcause]
  )"::[mcause] "r"(mcause.raw));

  test_fail += (result != 0);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

void reset_cpu_interrupt_lvl(void) {
  volatile mcause_t mcause = { 0 };
  volatile mstatus_t mstatus = { 0 };
  volatile uint32_t  pc = 0;

  __asm__ volatile ( R"(
    csrrs %[mstatus], mstatus, zero
    csrrs %[mcause], mcause, zero
  )":[mstatus] "=r"(mstatus.raw),
     [mcause] "=r"(mcause.raw)
    ::);

  mcause.clic.mpil = 0;
  mcause.clic.mpie = mstatus.fields.mie;
  mcause.clic.mpp = 0x3;
  mcause.clic.minhv = 0;

  __asm__ volatile ( R"(
    la %[pc], continued
    csrrw zero, mcause, %[mcause]
    csrrw zero, mepc, %[pc]
    mret
    continued:
    nop
  )":[pc] "+r"(pc)
    :[mcause] "r"(mcause.raw)
    :);
  return;
}

// -----------------------------------------------------------------------------

uint32_t mintthresh_lower(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile mintthresh_t mintthresh = { 0 };
  volatile mintstatus_t mintstatus = { 0 };
  volatile uint32_t mnxti_rval = 0;
  volatile clic_t clic_irq_vector = { 0 };

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  mintthresh.fields.th = 0xff;
  *g_special_handler_idx = 4;

  __asm__ volatile (R"(csrrs %[rd], 0xfb1, zero)":[rd] "=r"(mintstatus.raw));
  // To be potentially set by handler if incorrectly entered
  *g_irq_handler_reported_error = 0;

  *g_asserted_irq_idx = get_random_interrupt_number(0, NUM_INTERRUPTS);

  // Random interrupt with higher level than core, but lower than mintthresh;
  *g_asserted_irq_lvl = get_random_interrupt_level(mintstatus.fields.mil + 1, NUM_INTERRUPT_LVLS-1);

  if (*g_asserted_irq_lvl <= mintstatus.fields.mil) {
    // Reset cpu interrupt level, as we cannot not reach our desired test case
    reset_cpu_interrupt_lvl();
  }

  cvprintf(V_DEBUG, "mintthresh.th: %01x, interrupt: %02x, level: %02x\n", mintthresh.fields.th, *g_asserted_irq_idx, *g_asserted_irq_lvl);

  __asm__ volatile ( R"(
    csrrw zero, 0x347, %[rs1]
    csrrsi zero, 0x345, 0x8
  )":
    :[rs1] "r"(mintthresh.raw)
    :);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = *g_asserted_irq_idx,
    .fields.level = *g_asserted_irq_lvl,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  // asserted interrupt should not be taken (mintthresh.th too high)
  vp_assert_irq(clic_irq_vector.raw, 0);

  __asm__ volatile ( R"(
    csrrci %[rd1], 0x345, 0x8
  )":[rd1] "=r"(mnxti_rval)
    :
    :);

  cvprintf(V_DEBUG, "mnxti rval: %08x\n", mnxti_rval);

  // Mnxti should have read zero
  test_fail += mnxti_rval ? 1 : 0;
  // Interrupt should not have been taken
  test_fail += *g_irq_handler_reported_error;
  vp_assert_irq(0, 0);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t mintthresh_higher(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile uint32_t mnxti_rval = 0;
  volatile uint32_t mtvt = 0;
  volatile mintthresh_t mintthresh = { 0 };
  volatile mintstatus_t mintstatus = { 0 };
  volatile clic_t clic_irq_vector = { 0 };

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_special_handler_idx = 5;

  __asm__ volatile (R"(csrrs %[rd], 0xfb1, zero)":[rd] "=r"(mintstatus.raw));

  // To be cleared by handler
  *g_irq_handler_reported_error = 1;
  mintthresh.fields.th = get_random_interrupt_level(1, NUM_INTERRUPT_LVLS-1);
  *g_asserted_irq_idx = get_random_interrupt_number(1, NUM_INTERRUPTS);
  *g_asserted_irq_lvl = get_random_interrupt_level(mintthresh.fields.th + 1, NUM_INTERRUPT_LVLS);

  if (*g_asserted_irq_lvl <= mintstatus.fields.mil) {
    // Reset cpu interrupt level, as we cannot not reach our desired test case
    reset_cpu_interrupt_lvl();
  }

  cvprintf(V_DEBUG, "mintthresh.th: %01x, interrupt: %02x, level: %02x\n", mintthresh.fields.th, *g_asserted_irq_idx, *g_asserted_irq_lvl);

  vp_assert_irq(0, 0);
  __asm__ volatile ( R"(
    csrrw zero, 0x347, %[rs1]
    csrrsi %[rd1], 0x345, 0x8
  )":[rd1] "=r"(mnxti_rval)
    :[rs1] "r"(mintthresh.raw)
    :);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = *g_asserted_irq_idx,
    .fields.level = *g_asserted_irq_lvl,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  // asserted interrupt should be taken (mintthresh.th low enough)
  vp_assert_irq(clic_irq_vector.raw, 0);

  __asm__ volatile ( R"(
    csrrci %[rd1], 0x345, 0x8
    csrrs  %[rd2], 0x307, zero
  )":[rd1] "=r"(mnxti_rval),
     [rd2] "=r"(mtvt)
    :
    :);

  cvprintf(V_DEBUG, "mnxti rval: %08x\n", mnxti_rval);

  test_fail += *g_irq_handler_reported_error;
  test_fail += (mnxti_rval != mtvt + (*g_asserted_irq_idx * 4));

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t mintthresh_equal(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail = 0;
  volatile uint32_t mnxti_rval = 0;
  volatile mintthresh_t mintthresh = { 0 };
  volatile mintstatus_t mintstatus = { 0 };
  volatile clic_t clic_irq_vector = { 0 };

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_special_handler_idx = 6;

  __asm__ volatile (R"(csrrs %[rd], 0xfb1, zero)":[rd] "=r"(mintstatus.raw));

  // To be set by handler in case of entry
  *g_irq_handler_reported_error = 0;
  mintthresh.fields.th = get_random_interrupt_level(1, NUM_INTERRUPT_LVLS);
  *g_asserted_irq_idx = get_random_interrupt_number(1, NUM_INTERRUPTS);
  *g_asserted_irq_lvl = mintthresh.fields.th;

  if (*g_asserted_irq_lvl <= mintstatus.fields.mil) {
    // Reset cpu interrupt level, as we cannot not reach our desired test case
    reset_cpu_interrupt_lvl();
  }

  cvprintf(V_DEBUG, "mintthresh.th: %01x, interrupt: %02x, level: %02x\n", mintthresh.fields.th, *g_asserted_irq_idx, *g_asserted_irq_lvl);

  vp_assert_irq(0, 0);
  __asm__ volatile ( R"(
    csrrw zero, 0x347, %[rs1]
    csrrsi %[rd1], 0x345, 0x8
  )":[rd1] "=r"(mnxti_rval)
    :[rs1] "r"(mintthresh.raw)
    :);

  clic_irq_vector = (clic_t){
    .fields.irq   = 0x1,
    .fields.id    = *g_asserted_irq_idx,
    .fields.level = *g_asserted_irq_lvl,
    .fields.priv  = 0x3,
    .fields.shv   = 0x0
  };

  // asserted interrupt should not be taken (mintthresh.th too high)
  vp_assert_irq(clic_irq_vector.raw, 0);

  __asm__ volatile ( R"(
    csrrci %[rd1], 0x345, 0x8
  )":[rd1] "=r"(mnxti_rval)
    :
    :);

  cvprintf(V_DEBUG, "mnxti rval: %08x\n", mnxti_rval);

  test_fail += *g_irq_handler_reported_error;
  test_fail += (mnxti_rval != 0);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// This function should cover corner cases encountered by broken code during
// test development that made the ISS and RTL deviate. After resolving issues,
// leave this function in place to ensure that these issues do not return.
uint32_t mret_with_minhv_and_unaligned_mepc(uint32_t index, uint8_t report_name) {
  volatile uint8_t test_fail  = 0;
  volatile mcause_t mcause    = { 0 };
  volatile uint32_t result    = 0;
  volatile uint32_t all_set   = 0xFFFFFFFF;

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  *g_special_handler_idx = 7;

  __asm__ volatile ( R"(
    csrrs %[rd1], mcause, zero
  )":[rd1] "=r"(mcause.raw)
    ::);

  mcause.clic.minhv = 1;
  mcause.clic.mpp = 0x3;
  mcause.clic.mpie = 0;

  *g_checker = 0;

  __asm__ volatile (R"(
    csrrw zero, mcause, %[mcause]
    la t0, 1f
    lw t1, (t0)
    csrrw zero, mepc, t0
    # Store instruction mepc aims to execute in mscratch register.
    csrrw zero, mscratch, t1
    mret

    # Write 0xFFFF_FFFF to where g_checker points.
    lw t2, g_checker
    sw %[all_set], 0(t2)

    jal zero, 2f
    .align 4
    .byte(0xFF)
    .byte(0xFF)
    1: .word(2f)
    .space 0x100, 0x0

    2:
    # Fetch the value g_checker points to.
    lw t2, g_checker
    lw t2, 0(t2)

    addi %[result], t2, 0

  )":[result] "=r"(result)
    :[mcause] "r"(mcause.raw), [all_set] "r"(all_set)
    :"t0", "t1", "t2");

  test_fail += (result != 0);

  if (test_fail) {
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------
// Note that the following interrupt/exception handler is not generic and specific
// to this test.

__attribute__((interrupt("machine"))) void u_sw_irq_handler(void) {
  volatile uint32_t mepc;
  volatile uint32_t result = 0;
  volatile uint32_t mtvt = 0;
  volatile mcause_t mcause = { 0 };

  // RWX !L & MODE OFF
  volatile const uint32_t pmp_enable_access_all = 0x07070707;

  __asm__ volatile ( R"(
     csrrs %[mc], mcause, x0
     csrrs %[mp], mepc, x0
     csrrs %[mtvt], 0x307, x0
     )"
     : [mc] "=r"(mcause.raw),
       [mp] "=r"(mepc),
       [mtvt] "=r"(mtvt)
     :
     :
     );

  cvprintf(V_DEBUG, "In handler, mepc: 0x%08lx, mcause: 0x%08lx\n", mepc, mcause.raw);

  switch (*g_special_handler_idx) {
    case 1:
      result = r_mnxti_with_irq_handler(0, NUM_INTERRUPTS, 2, NUM_INTERRUPT_LVLS);
      if (result != (mtvt + (*g_asserted_irq_idx) * 4)) {
        cvprintf(V_DEBUG, "Mismatch, expected: 0x%08lx, actual: 0x%08lx\n", mtvt + ((*g_asserted_irq_idx) * 4), result);
        *g_irq_handler_reported_error = 1;
      } else {
        *g_irq_handler_reported_error = 0;
      }
      vp_assert_irq(0, 0);
      *g_special_handler_idx = 0;
      return;
      break;
    case 2:
      result = r_mnxti_with_irq_handler(0, NUM_INTERRUPTS, 0, NUM_INTERRUPT_LVLS);
      if (result != 0) {
        cvprintf(V_DEBUG, "Mismatch, expected: 0x%08lx, actual: 0x%08lx\n", 0, result);
        *g_irq_handler_reported_error = 1;
      } else {
        *g_irq_handler_reported_error = 0;
      }
      vp_assert_irq(0, 0);
      *g_special_handler_idx = 0;
      return;
      break;
    case 3:
      mcause.raw = 0;
      mcause.clic.mpp  = 0x3;
      mcause.clic.mpil = 0;
      mcause.clic.mpie = 0;
      __asm__ volatile ( R"(
        csrrw zero, mcause, %[rs1]
      )"::[rs1] "r"(mcause.raw):);
      *g_special_handler_idx = 0;
      vp_assert_irq(0, 0);
      return;
      break;
    case 4:
      *g_irq_handler_reported_error = 1;
      vp_assert_irq(0, 0);
      return;
      break;
    case 5:
      *g_irq_handler_reported_error = 0;
      mcause.clic.mpp  = 0x3;
      mcause.clic.mpil = 0;
      mcause.clic.mpie = 0;
      __asm__ volatile ( R"(
        csrrw zero, mcause, %[rs1]
      )"::[rs1] "r"(mcause.raw):);
      return;
      break;
    case 6:
      *g_irq_handler_reported_error = 1;
      vp_assert_irq(0, 0);
      *g_special_handler_idx = 0;
      return;
      break;
    case 7:
    *g_special_handler_idx = 0;
    //Write mscratch value to mepc
    __asm__ volatile ( R"(
      csrrw t0, mscratch, zero
      csrrw zero, mepc, t0
    )"::: "t0");
      return;
      break;
  }

  if (mcause.clic.interrupt == 0 && mcause.clic.exccode == 2) {
    (*g_expect_illegal)--;
    increment_mepc(0);
    return;
  }

  switch (mcause.clic.interrupt) {
    case 0:
      switch (mcause.clic.exccode) {
        case 0x1: cvprintf(V_LOW, "Instruction access fault at 0x%08lx minhv: %0d\n", mepc, mcause.clic.minhv);
                  break;
        case 0x2: cvprintf(V_LOW, "Invalid instruction fault at 0x%08lx\n", mepc);
                  break;
      }
      break;
    case 1:
      cvprintf(V_LOW, "Interrupt, ID: 0x%08lx, minhv status: %0d\n", mcause.clic.exccode, mcause.clic.minhv);
      vp_assert_irq(0, 0);
      break;
  }

  // check if address is locked, then unlock
  // let test be responsible for cleaning up addr-regs to
  // not clutter code here
  if ( mcause.clic.exccode == 1 ) {
    cvprintf(V_LOW, "Encountered read access fault, trying to enable pmp access\n");
    __asm__ volatile ( R"(
      csrrw x0, pmpcfg0,  %[access_ena]
      csrrw x0, pmpcfg1,  %[access_ena]
      csrrw x0, pmpcfg2,  %[access_ena]
      csrrw x0, pmpcfg3,  %[access_ena]
      csrrw x0, pmpcfg4,  %[access_ena]
      csrrw x0, pmpcfg5,  %[access_ena]
      csrrw x0, pmpcfg6,  %[access_ena]
      csrrw x0, pmpcfg7,  %[access_ena]
      csrrw x0, pmpcfg8,  %[access_ena]
      csrrw x0, pmpcfg9,  %[access_ena]
      csrrw x0, pmpcfg10, %[access_ena]
      csrrw x0, pmpcfg11, %[access_ena]
      csrrw x0, pmpcfg12, %[access_ena]
      csrrw x0, pmpcfg13, %[access_ena]
      csrrw x0, pmpcfg14, %[access_ena]
      csrrw x0, pmpcfg15, %[access_ena]
    )"
    :
    : [access_ena] "r" (pmp_enable_access_all)
    :
      );
  }

  return;
}
// -----------------------------------------------------------------------------
_Pragma("GCC pop_options")
// -----------------------------------------------------------------------------

