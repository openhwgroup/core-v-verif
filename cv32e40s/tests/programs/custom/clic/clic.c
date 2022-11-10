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
// CLIC CSR access tests
//
/////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdarg.h>
#include <assert.h>

// MUST be 31 or less
#define NUM_TESTS 9
#define ABORT_ON_ERROR_IMMEDIATE 0
#define SMCLIC_ID_WIDTH 5
#define MTVEC_ALIGN_BITS 7

#define SET_FUNC_INFO \
  _Pragma("GCC diagnostic push") \
  _Pragma("GCC diagnostic ignored \"-Wpedantic\"") \
  const char * name = __FUNCTION__; \
  _Pragma("GCC diagnostic pop")

// Bitfield offsets
const uint32_t MSTATUS_MPP_OFFSET  = 11;
const uint32_t MSTATUS_MPIE_OFFSET = 7;
const uint32_t MCAUSE_MPP_OFFSET   = 28;
const uint32_t MCAUSE_MPIE_OFFSET  = 27;

// Bitfield masks
const uint32_t MSTATUS_MPP_MASK  = 0x3 << MSTATUS_MPP_OFFSET;
const uint32_t MSTATUS_MPIE_MASK = 0x1 << MSTATUS_MPIE_OFFSET;
const uint32_t MCAUSE_MPP_MASK   = 0x3 << MCAUSE_MPP_OFFSET;
const uint32_t MCAUSE_MPIE_MASK  = 0x1 << MCAUSE_MPIE_OFFSET;

typedef enum {
  V_OFF    = 0,
  V_LOW    = 1,
  V_MEDIUM = 2,
  V_HIGH   = 3,
  V_DEBUG  = 4
} verbosity_t;

const verbosity_t global_verbosity = V_LOW;

// ---------------------------------------------------------------
// Test prototypes - should match
// uint32_t <name>(uint32_t index, uint8_t report_name)
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

// Helper functions
/*
 * set_test_status
 *
 * Sets the pass/fail criteria for a given tests and updates
 * the 32bit test status variable
 */
uint32_t set_test_status(uint32_t test_no, uint32_t val_prev);

/*
 * get_result
 *
 * Reports result of self checking tests
 */
int get_result(uint32_t res, uint32_t (*ptr[])(uint32_t, uint8_t));

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
 */
int cvprintf(verbosity_t verbosity, const char *format, ...);

// ---------------------------------------------------------------
// Test entry point
// ---------------------------------------------------------------
int main(int argc, char **argv){

  uint32_t (*tests[NUM_TESTS])(uint32_t, uint8_t);
  uint32_t test_res = 0x1;
  int      retval   = 0;

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

  // Run all tests in list above
  cvprintf(V_LOW, "\nCLIC Test start\n\n");
  for (int i = 0; i < NUM_TESTS; i++) {
    test_res = set_test_status(tests[i](i, 0), test_res);
  }

  // Report failures
  retval = get_result(test_res, tests);
  return retval; // Nonzero for failing tests
}

// -----------------------------------------------------------------------------

int cvprintf(verbosity_t verbosity, const char *format, ...){
  va_list args;
  int retval = 0;

  va_start(args, format);

  if (verbosity <= global_verbosity){
    retval = vprintf(format, args);
  }
  va_end(args);
  return retval;
}

// -----------------------------------------------------------------------------

uint32_t set_test_status(uint32_t test_no, uint32_t val_prev){
  uint32_t res;
  res = val_prev | (1 << test_no);
  return res;
}

// -----------------------------------------------------------------------------

uint32_t max(uint32_t a, uint32_t b) {
  return a > b ? a : b;
}

// -----------------------------------------------------------------------------

int get_result(uint32_t res, uint32_t (*ptr[])(uint32_t, uint8_t)){
  if (res == 1) {
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
  return res;
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
    csrrs %0, mcause, x0
    csrrs %1, mstatus, x0
  )"
      : "=r"(readback_val_mcause), "=r"(readback_val_mstatus)
      :
      :
      );
  test_fail += (  ((readback_val_mcause & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET)
               != ((readback_val_mstatus & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET));
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  test_fail += (  ((readback_val_mcause & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET)
               != ((readback_val_mstatus & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET));

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
      csrrs %0, mcause, x0
  )"
      : "=r"(mcause_initial_val)
      :
      :
      );
  cvprintf(V_HIGH, "Initial value mcause.mpp: %0lx\n", ((mcause_initial_val & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET));

  // Bit set and read back
  __asm__ volatile ( R"(
      csrrs x0, mcause, %0
      csrrs %0, mstatus, x0
  )"
      : "=r"(readback_val)
      : "r"(MCAUSE_MPP_MASK)
      :
      );

  test_fail += (((readback_val & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET) != 0x3);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mstatus.mpp after setting bits: %0lx\n", ((readback_val & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET));

  // Bit clear and read back
  __asm__ volatile ( R"(
      csrrc x0, mcause, %0
      csrrc %0, mstatus, x0
  )"
      : "=r"(readback_val)
      : "r"(MCAUSE_MPP_MASK)
      :
      );

  test_fail += (((readback_val & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET) != 0x0);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mstatus.mpp after clearing bits: %0lx\n", ((readback_val & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET));

  // Restore value and read back
  __asm__ volatile ( R"(
      csrrw x0, mcause, %0
      csrrw %0, mstatus, x0
  )"
      : "=r"(readback_val)
      : "r"(mcause_initial_val)
      :
      );

  test_fail += (  ((readback_val & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET)
               != ((mcause_initial_val & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET));
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
      csrrs %0, mstatus, x0
  )"
      : "=r"(mstatus_initial_val)
      :
      :
      );

  cvprintf(V_HIGH, "Initial value mstatus.mpp: %0lx\n", ((mstatus_initial_val & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET));

  // Bit set and read back
  __asm__ volatile ( R"(
      csrrs x0, mstatus, %0
      csrrs %0, mcause, x0
  )"
      : "=r"(readback_val)
      : "r"(MSTATUS_MPP_MASK)
      :
      );

  test_fail += (((readback_val & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET) != 0x3);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mcause.mpp after setting bits: %0lx\n", ((readback_val & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET));

  // Bit clear and read back
  __asm__ volatile ( R"(
      csrrc x0, mstatus, %0
      csrrc %0, mcause, x0
  )"
      : "=r"(readback_val)
      : "r"(MSTATUS_MPP_MASK)
      :
      );

  test_fail += (((readback_val & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET) != 0x0);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mcause.mpp after clearing bits: %0lx\n", ((readback_val & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET));

  // Restore value and read back
  __asm__ volatile ( R"(
      csrrw x0, mstatus, %0
      csrrw %0, mcause, x0
  )"
      : "=r"(readback_val)
      : "r"(mstatus_initial_val)
      :
      );

  test_fail += (  ((readback_val & MCAUSE_MPP_MASK) >> MCAUSE_MPP_OFFSET)
               != ((mstatus_initial_val & MSTATUS_MPP_MASK) >> MSTATUS_MPP_OFFSET));
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
      csrrs %0, mcause, x0
  )"
      : "=r"(mcause_initial_val)
      :
      :
      );

  cvprintf(V_HIGH, "Initial value mcause.mpie: %0lx\n", ((mcause_initial_val & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET));

  // Bit set and read back
  __asm__ volatile ( R"(
      csrrs x0, mcause, %0
      csrrs %0, mstatus, x0
  )"
      : "=r"(readback_val)
      : "r"(MCAUSE_MPIE_MASK)
      :
      );

  test_fail += (((readback_val & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET) != 0x1);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mstatus.mpie after setting bits: %0lx\n", ((readback_val & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET));

  // Bit clear and read back
  __asm__ volatile ( R"(
      csrrc x0, mcause, %0
      csrrc %0, mstatus, x0
  )"
      : "=r"(readback_val)
      : "r"(MCAUSE_MPIE_MASK)
      :
      );

  test_fail += (((readback_val & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET) != 0x0);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mstatus.mpie after clearing bits: %0lx\n", ((readback_val & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET));
  // Restore value and read back
  __asm__ volatile ( R"(
      csrrw x0, mcause, %0
      csrrw %0, mstatus, x0
  )"
      : "=r"(readback_val)
      : "r"(mcause_initial_val)
      :
      );

  test_fail += (  ((readback_val & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET)
               != ((mcause_initial_val & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET));
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
      csrrs %0, mstatus, x0
  )"
      : "=r"(mstatus_initial_val)
      :
      :
      );

  cvprintf(V_HIGH, "Initial value mstatus.mpie: %0lx\n", ((mstatus_initial_val & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET));

  // Bit set and read back
  __asm__ volatile ( R"(
      csrrs x0, mstatus, %0
      csrrs %0, mcause, x0
  )"
      : "=r"(readback_val)
      : "r"(MSTATUS_MPIE_MASK)
      :
      );

  test_fail += (((readback_val & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET) != 0x1);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mcause.mpie after setting bits: %0lx\n", ((readback_val & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET));

  // Bit clear and read back
  __asm__ volatile ( R"(
      csrrc x0, mstatus, %0
      csrrc %0, mcause, x0
  )"
      : "=r"(readback_val)
      : "r"(MSTATUS_MPIE_MASK)
      :
      );

  test_fail += (((readback_val & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET) != 0x0);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);
  cvprintf(V_HIGH, "Read back mcause.mpie after clearing bits: %0lx\n", ((readback_val & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET));

  // Restore value and read back
  __asm__ volatile ( R"(
      csrrw x0, mstatus, %0
      csrrw %1, mcause, x0
  )"
      : "=r"(readback_val)
      : "r"(mstatus_initial_val)
      :
      );

  test_fail += (  ((readback_val & MCAUSE_MPIE_MASK) >> MCAUSE_MPIE_OFFSET)
               != ((mstatus_initial_val & MSTATUS_MPIE_MASK) >> MSTATUS_MPIE_OFFSET));
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
  uint8_t test_fail = 0;
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
      csrrw %1, mie, x0
      csrrw %0, mepc, x0
  )"
      : "=r"(readback_val_mepc), "=r"(readback_val_mie)
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
  uint8_t test_fail = 0;
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
      csrrw %1, mip, x0
      csrrw %0, mepc, x0
  )"
      : "=r"(readback_val_mepc), "=r"(readback_val_mip)
      :
      : "t0"
      );

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
  uint8_t test_fail = 0;
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
      csrrw %0, 0x307, x0
      csrrw %1, 0x307, %1
  )"
      : "=r"(mtvt_initial_val), "=r"(readback_val_mtvt)
      : "r"(mtvt_initial_val)
      :
      );

  // All bits should be zeroed
  test_fail += readback_val_mtvt;
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  __asm__ volatile ( R"(
      addi t0, x0, -1
      csrrw %0, 0x307, t0
      csrrw %1, 0x307, %1
  )"
      : "=r"(mtvt_initial_val), "=r"(readback_val_mtvt)
      : "r"(mtvt_initial_val)
      :
      );

  // Check for correct alignment
  test_fail += ~(readback_val_mtvt >> max(SMCLIC_ID_WIDTH+2, 6));
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
  uint8_t test_fail = 0;
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
      csrrw %0, mtvec, x0
      csrrw %1, mtvec, %1
  )"
      : "=r"(mtvec_initial_val), "=r"(readback_val_mtvec)
      : "r"(mtvec_initial_val)
      :
      );

  // All bits above 2 should be zeroed
  test_fail += (readback_val_mtvec >> 2);
  if (ABORT_ON_ERROR_IMMEDIATE) assert(test_fail == 0);

  __asm__ volatile ( R"(
      addi t0, x0, -1
      csrrw %0, mtvec, t0
      csrrw %1, mtvec, %1
  )"
      : "=r"(mtvec_initial_val), "=r"(readback_val_mtvec)
      : "r"(mtvec_initial_val)
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


