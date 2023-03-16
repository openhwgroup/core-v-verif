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
#define NUM_TESTS 10
// Abort test at first self-check fail, useful for debugging.
#define ABORT_ON_ERROR_IMMEDIATE 0
#define CLIC_ID_WIDTH 5
#define MTVEC_ALIGN_BITS 7

// Addresses of VP interrupt control registers
#define TIMER_REG_ADDR       ((volatile uint32_t *) (CV_VP_INTR_TIMER_BASE))
#define TIMER_VAL_ADDR       ((volatile uint32_t *) (CV_VP_INTR_TIMER_BASE + 4))

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

typedef struct {
  uint8_t  irq;
  uint16_t id;
  uint8_t  level;
  uint8_t  priv;
  uint8_t  shv;
} clic_t;

typedef enum {
  OFF = 0,
  TOR = 1,
  NA4 = 2,
  NAPOT = 3
} pmp_mode_t;

typedef struct {
  uint8_t reg_no;
  uint8_t lock;
  pmp_mode_t mode;
  uint8_t execute;
  uint8_t write;
  uint8_t read;
} pmpcfg_t;

typedef struct {
  uint8_t rlb;
  uint8_t mmwp;
  uint8_t mml;
} mseccfg_t;

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
extern volatile uint32_t recovery_pt;
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
 * set_clic_assert
 *
 * Prepare suitable data structure for clic interrupt
 * with the given clic_t object
 */
uint32_t set_clic_assert_val(clic_t clic);

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

// ---------------------------------------------------------------
// Test entry point
// ---------------------------------------------------------------
int main(int argc, char **argv){

  volatile uint32_t (* volatile tests[NUM_TESTS])(volatile uint32_t, volatile uint8_t);

  volatile uint32_t test_res = 0x1;
  volatile int      retval   = 0;

  // Add function pointers to new tests here
  tests[0] = mcause_mstatus_mirror_init;
  tests[1] = w_mcause_mpp_r_mstatus_mpp;
  tests[2] = w_mstatus_mpp_r_mcause_mpp;
  tests[3] = w_mcause_mpie_r_mstatus_mpie;
  tests[4] = w_mstatus_mpie_r_mcause_mpie;
  tests[5] = w_mie_notrap_r_zero;
  tests[6] = w_mip_notrap_r_zero;
  tests[7] = w_mtvt_rd_alignment;
  tests[8] = w_mtvec_rd_alignment;
  tests[9] = invalid_mtvt_ptr_exec;

  // Run all tests in list above
  cvprintf(V_LOW, "\nCLIC Test start\n\n");
  for (volatile int i = 0; i < NUM_TESTS; i++) {
    test_res = set_test_status(tests[i](i, (volatile uint32_t)(0)), test_res);
  }

  // Report failures
  retval = get_result(test_res, tests);
  return retval; // Nonzero for failing tests
}

// -----------------------------------------------------------------------------

int cvprintf(verbosity_t verbosity, const char *format, ...){
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
  for (int i = 0; i < NUM_TESTS; i++){
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

uint32_t set_clic_assert_val(clic_t clic){
  volatile uint32_t clic_vector = 0x0;

  clic_vector = (clic_vector & ~(0x007FFFFF))
                | (clic.irq   << 22)
                | (clic.id    << 11)
                | (clic.level << 3)
                | (clic.priv  << 1)
                | (clic.shv);
  cvprintf(V_DEBUG, "clic_vector: %08x\n", clic_vector);

  return clic_vector;
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

  //__asm__ volatile ( R"( csrrs %[pmpvec], pmpcfg0, x0)" : [pmpvec] "+r"(pmpcfg_vector): :);
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
      : [mc] "=r"(readback_val_mcause), [ms] "=r"(readback_val_mstatus)
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

uint32_t invalid_mtvt_ptr_exec(uint32_t index, uint8_t report_name) {

  volatile uint8_t test_fail = 1;

  // These needs to be volatile to prevent loop optimization
  volatile uint8_t never = 0;
  volatile uint32_t no_timeout_threshold = 1000;
  volatile uint32_t mepc_triggered = 0x0;
  volatile uint32_t addr = 0x0;
  uint32_t clic_vector = 0x0;

  SET_FUNC_INFO
  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // The following if-block implements a 1024-entry mtvt table
  // note that only certain pointers are actually implemented,
  // and they all point to the code following the table. The
  // non-implemented entries point to 0x0 (mtvec)
  //
  // Normal code flow should never reach this code,
  // thus we have to use a volatile condition parameter
  // to avoid compiler optimizing the table away
  if (never) {
    // Create mtvt table, add empty space to be able to use
    // id 1021-1023, id 30-32
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
      addi %[to_th], x0, 1
      csrrs %[mepc], mepc, x0
    )" : [to_th] "+r"(no_timeout_threshold), [mepc] "+r"(mepc_triggered)
       :
       : "memory"
       );

    // Initially there was a split here to ensure that the above
    // variables were properly updated before proceeding to mret
    // as the compiler will need to insert some housekeeping code
    // to keep things in check. This is now kept to make a convenient
    // debug print statement available.

    cvprintf(V_DEBUG, "mepc: 0x%08lx\n", mepc_triggered);

    __asm__ volatile ( R"(
      csrrw x0, mepc, %[mepc]
      addi t0, x0, 0
      lui t0, 0x30000
      csrrs x0, mcause, t0
    )" :
       : [mepc] "r"(mepc_triggered)
       :);

    // Check that we actually ended up at the correct place after
    // clic ptr fetch failed, and get the code back to the intended
    // execution flow to complete the test properly.
    // If code does not reach this part, then test_fail will be non-
    // zero upon completion.
    if (mepc_triggered == (uint32_t)&mtvt_table + 4096) {
      test_fail = 0;
      cvprintf(V_LOW, "(Intentional) Unrecoverable pointer fetch exception occurred,\njumping to safe recovery point for test termination\n");
      mepc_triggered = (uint32_t)&recovery_pt;
      __asm__ volatile ( R"(
        csrrw x0, mepc, %[mepc]
        )"
          :
          : [mepc] "r"(mepc_triggered)
          :);
    }

    __asm__ volatile ( R"( mret )":::);

    // Fallback fail check
    test_fail++;
    cvprintf(V_LOW, "Triggered unreachable code, this should not happen!\n");
    // At this point, there is no knowning what the state of the cpu is,
    // abort and fail test here to avoid spurious results
    assert(0);
  }

  __asm__ volatile ( R"(csrrw x0, mtvec, x0)":::);

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
  clic_vector = set_clic_assert_val((clic_t){
                                    .irq   = 0x1,
                                    .id    = 0x3,
                                    .level = 0x81,
                                    .priv  = 0x3,
                                    .shv   = 0x1
                                    });

  no_timeout_threshold = 1000;
  mepc_triggered = 0;
  // Instruct clic_interrupt_vp to assert interrupt declared above
  vp_assert_irq(clic_vector, 10);

  // Wait for interrupt
  while (no_timeout_threshold) {
    no_timeout_threshold--;
  }
  cvprintf(V_MEDIUM, "Expect non-zero mepc, MEPC = 0x%08lx\n", mepc_triggered);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(mepc_triggered != 0);

  clic_vector = set_clic_assert_val((clic_t){
                                    .irq = 0x1,
                                    .id  = (0x1 << CLIC_ID_WIDTH)-1,
                                    .level = 0xFF,
                                    .priv  = 0x3,
                                    .shv   = 0x1
                                    });

  no_timeout_threshold = 1000;
  mepc_triggered = 0;
  // Instruct clic_interrupt_vp to assert interrupt declared above
  vp_assert_irq(clic_vector, 10);

  // Wait for interrupt
  while (no_timeout_threshold) {
    no_timeout_threshold--;
  }
  cvprintf(V_MEDIUM, "Expect non-zero mepc, MEPC = 0x%08lx\n", mepc_triggered);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(mepc_triggered != 0);

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

  clic_vector = set_clic_assert_val((clic_t){
                                    .irq   = 0x1,
                                    .id    = 0x4,
                                    .level = 0x55,
                                    .priv  = 0x3,
                                    .shv   = 0x1
                                    });

  no_timeout_threshold = 1000;
  mepc_triggered = 0;
  // Instruct clic_interrupt_vp to assert interrupt declared above
  vp_assert_irq(clic_vector, 10);

  // Wait for interrupt
  while (no_timeout_threshold) {
    no_timeout_threshold--;
  }

  __asm__ volatile ( R"(
    .global recovery_pt
    recovery_pt: add x0, x0, x0
  )":::);


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
  volatile uint32_t mcause;

  // RWX !L & MODE OFF
  const uint32_t pmp_enable_access_all = 0x07070707;

  __asm__ volatile ( R"(
     csrrs %[mc], mcause, x0
     csrrs %[mp], mepc, x0
     )"
     : [mc] "=r"(mcause), [mp] "=r"(mepc)
     :
     :
     );

  cvprintf(V_DEBUG, "In handler, mepc: 0x%08lx, mcause: 0x%08lx\n", mepc, mcause);

  switch ((mcause & 0x80000000) >> 31) {
    case 0:
      switch (mcause & 0xFFF) {
        case 0x1: cvprintf(V_LOW, "Instruction access fault at 0x%08lx\n", mepc);
                  break;
        case 0x2: cvprintf(V_LOW, "Invalid instruction fault at 0x%08lx\n", mepc);
                  break;
      }
      break;
    case 1:
      cvprintf(V_LOW, "Interrupt, ID: 0x%08lx, minhv status: %0d\n", mcause & 0xFFF, (mcause & 0x40000000) >> 30);
      break;
  }

  // check if address is locked, then unlock
  // let test be responsible for cleaning up addr-regs to
  // not clutter code here
  if ((mcause & 0x80000001) == 0x1 && ((mcause & 0x40000000) >> 30) == 0x1) {
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
      csrrs t0, mcause, x0
      1: csrrs t0, mepc, x0
      lw t0, 0(t0)
      add t1, x0, x0
      lui t1, 0x40000
      csrrc x0, mcause, t1
      csrrw x0, mepc, t0
    )"
    :
    : [access_ena] "r" (pmp_enable_access_all)
    : "t0", "t1"
      );
  }

  return;
}
// -----------------------------------------------------------------------------
_Pragma("GCC pop_options")
// -----------------------------------------------------------------------------

