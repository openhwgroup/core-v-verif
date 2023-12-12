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
// zcmt directed test
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
#define NUM_TESTS 13
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
#define MARCHID_CV32E40X 0x14
#define MARCHID_CV32E40S 0x15

#define OPCODE_SYSTEM  0x73

#define MSTATEEN0_ADDR 0x30c
#define MSECCFG_ADDR   0x747
#define PMPCFG0_ADDR   0x3a0
#define PMPADDR0_ADDR  0x3b0
#define PMPADDR1_ADDR  0x3b1
#define PMPADDR2_ADDR  0x3b2
#define JVT_ADDR       0x017


// ---------------------------------------------------------------
// Global variables
// ---------------------------------------------------------------
// Print verbosity, consider implementing this as a virtual
// peripheral setting to be controlled from UVM.
volatile verbosity_t global_verbosity = V_LOW;

volatile uint32_t * volatile g_expect_illegal;
volatile uint32_t * volatile g_expect_tablejmp;
volatile uint32_t * volatile g_csr_instr;
volatile uint32_t * volatile g_csr_instr_rd_val;
volatile uint32_t * volatile g_csr_instr_rs1_val;

volatile uint32_t * volatile g_recovery_cm_jt;

extern volatile uint32_t jvt_table;
extern volatile uint32_t recovery_cm_jt_m_0;
extern volatile uint32_t recovery_cm_jt_m_1;
extern volatile uint32_t recovery_cm_jt_m_31;
extern volatile uint32_t recovery_cm_jt_u_0;
extern volatile uint32_t recovery_cm_jt_u_1;
extern volatile uint32_t recovery_cm_jt_u_31;
// ---------------------------------------------------------------
// Test prototypes - should match
// uint32_t <name>(uint32_t index, uint8_t report_name)
//
// Use template below for implementation
// ---------------------------------------------------------------
uint32_t mstateen0_rw_m(uint32_t index, uint8_t report_name);
uint32_t mstateen0_rw_u_illegal(uint32_t index, uint8_t report_name);
uint32_t jvt_rw_m(uint32_t index, uint8_t report_name);
uint32_t jvt_rw_u_illegal(uint32_t index, uint8_t report_name);
uint32_t jvt_rw_u_legal(uint32_t index, uint8_t report_name);
uint32_t cm_jt_m(uint32_t index, uint8_t report_name);
uint32_t cm_jalt_m(uint32_t index, uint8_t report_name);
uint32_t cm_jt_u_illegal(uint32_t index, uint8_t report_name);
uint32_t cm_jalt_u_illegal(uint32_t index, uint8_t report_name);
uint32_t cm_jt_u_legal(uint32_t index, uint8_t report_name);
uint32_t cm_jalt_u_legal(uint32_t index, uint8_t report_name);
uint32_t cm_jt_m_trap(uint32_t index, uint8_t report_name);
uint32_t cm_jalt_m_trap(uint32_t index, uint8_t report_name);

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
void handle_insn_access_fault(void);
void handle_ecall(void);
void handle_ecall_u(void);

// ---------------------------------------------------------------
// Test entry point
// ---------------------------------------------------------------
int main(int argc, char **argv){

  volatile uint32_t (* volatile tests[NUM_TESTS])(volatile uint32_t, volatile uint8_t);

  volatile uint32_t test_res = 0x1;
  volatile int      retval   = 0;

  g_expect_illegal      = calloc(1, sizeof(uint32_t));
  g_expect_tablejmp     = calloc(1, sizeof(uint32_t));
  g_csr_instr           = calloc(1, sizeof(uint32_t));
  g_csr_instr_rd_val    = calloc(1, sizeof(uint32_t));
  g_csr_instr_rs1_val   = calloc(1, sizeof(uint32_t));
  g_recovery_cm_jt      = calloc(1, sizeof(uint32_t));

  // Add function pointers to new tests here
  tests[0]  = mstateen0_rw_m;
  tests[1]  = mstateen0_rw_u_illegal;
  tests[2]  = jvt_rw_m;
  tests[3]  = jvt_rw_u_illegal;
  tests[4]  = jvt_rw_u_legal;
  tests[5]  = cm_jt_m;
  tests[6]  = cm_jalt_m;
  tests[7]  = cm_jt_u_illegal;
  tests[8]  = cm_jalt_u_illegal;
  tests[9]  = cm_jt_u_legal;
  tests[10] = cm_jalt_u_legal;
  tests[11] = cm_jt_m_trap;
  tests[12] = cm_jalt_m_trap;

  // TODO silabs-hfegran: defering these tests to a later PR
  //tests[11] = cm_jt_m_trap_m;
  //tests[12] = cm_jt_u_trap_u;
  //tests[12] = cm_jalt_u_trap;

  // Run all tests in list above
  cvprintf(V_LOW, "\nZcmt Test start\n\n");
  for (volatile int i = START_TEST_IDX; i < NUM_TESTS; i++) {
    test_res = set_test_status(tests[i](i, (volatile uint32_t)(0)), test_res);
  }

  // Report failures
  retval = get_result(test_res, tests);

  free((void *)g_expect_illegal       );
  free((void *)g_csr_instr            );
  free((void *)g_csr_instr_rd_val     );
  free((void *)g_csr_instr_rs1_val    );
  free((void *)g_recovery_cm_jt       );
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
    # must ensure that a1 is not some garbage value
    add a1, zero, zero
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

    # Decrement *g_expect_illegal
    lw s0, g_expect_illegal
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

void set_pmpcfg(pmpsubcfg_t pmpsubcfg, uint32_t reg_no){
  volatile pmpcfg_t temp   = { 0 };
  volatile pmpcfg_t pmpcfg = { 0 };

  temp.reg_idx[reg_no % 4].cfg   = 0xff;
  pmpcfg.reg_idx[reg_no % 4].cfg = pmpsubcfg.raw;

  (void)csr_instr(CSRRC, PMPCFG0_ADDR + (reg_no / 4), temp.raw);
  (void)csr_instr(CSRRS, PMPCFG0_ADDR + (reg_no / 4), pmpcfg.raw);

  return;
}

// -----------------------------------------------------------------------------

__attribute__((naked)) void jvt_code(void) {
  __asm__ volatile ( R"(
    .option push
    .option norvc
    .global jvt_table
    .extern jvt_index_1
    .align 6
    jvt_table:
    index_0: .word(jvt_index_0)
    index_1: .word(jvt_index_1)
    index_2: .word(jvt_index_2)
    .space 112, 0x0
    index_31: .word(jvt_index_31)
    index_32: .word(jvt_index_32)
    .space 8
    index_35: .word(jvt_index_35)
    .space 172, 0x0
    index_79: .word(jvt_index_79)
    .space 172, 0x0
    index_123: nop
    .space 524, 0x0
    index_255: .word(jvt_index_255)
    .option pop
  )");
}

// -----------------------------------------------------------------------------


__attribute__((optimize("align-functions=4"), naked)) void jvt_index_0(void) {
  __asm__ volatile ( R"(
    lw a0, g_recovery_cm_jt
    lw a0, 0(a0)
    jalr zero, 0(a0)
  )");
}

// -----------------------------------------------------------------------------

__attribute__((optimize("align-functions=4"), naked)) void jvt_index_1(void) {
  __asm__ volatile ( R"(
    addi sp, sp, -8
    sw a0, 0(sp)
    sw a1, 4(sp)

    lw a0, g_expect_tablejmp
    lw a1, 0(a0)
    addi a1, a1, -1
    sw a1, 0(a0)

    lw a1, 4(sp)
    lw a0, 0(sp)
    addi sp, sp, 8

    lw a0, g_recovery_cm_jt
    lw a0, 0(a0)
    jalr zero, 0(a0)

  )");
}

// -----------------------------------------------------------------------------

__attribute__((optimize("align-functions=4"), naked)) void jvt_index_2(void) {
  __asm__ volatile ( R"(
    addi sp, sp, -8
    sw a0, 0(sp)
    sw a1, 4(sp)

    lw a0, g_expect_tablejmp
    lw a1, 0(a0)
    addi a1, a1, -2
    sw a1, 0(a0)

    lw a1, 4(sp)
    lw a0, 0(sp)
    addi sp, sp, 8
    lw a0, g_recovery_cm_jt
    lw a0, 0(a0)
    jalr zero, 0(a0)
  )");
}

// -----------------------------------------------------------------------------

__attribute__((optimize("align-functions=4"), naked)) void jvt_index_31(void) {
  __asm__ volatile ( R"(
    addi sp, sp, -8
    sw a0, 0(sp)
    sw a1, 4(sp)

    lw a0, g_expect_tablejmp
    lw a1, 0(a0)
    addi a1, a1, -31
    sw a1, 0(a0)

    lw a1, 4(sp)
    lw a0, 0(sp)
    addi sp, sp, 8

    lw a0, g_recovery_cm_jt
    lw a0, 0(a0)
    jalr zero, 0(a0)

  )");
}

// -----------------------------------------------------------------------------

__attribute__((optimize("align-functions=4"), naked)) void jvt_index_32(void) {
  __asm__ volatile ( R"(
    addi sp, sp, -8
    sw a0, 0(sp)
    sw a1, 4(sp)

    lw a0, g_expect_tablejmp
    lw a1, 0(a0)
    addi a1, a1, -32
    sw a1, 0(a0)

    lw a1, 4(sp)
    lw a0, 0(sp)
    addi sp, sp, 8
    ret

  )");
}

// -----------------------------------------------------------------------------

__attribute__((optimize("align-functions=4"), naked)) void jvt_index_35(void) {
  __asm__ volatile ( R"(
    addi sp, sp, -8
    sw a0, 0(sp)
    sw a1, 4(sp)

    lw a0, g_expect_tablejmp
    lw a1, 0(a0)
    addi a1, a1, -35
    sw a1, 0(a0)

    lw a1, 4(sp)
    lw a0, 0(sp)
    addi sp, sp, 8
    ret
  )");
}

// -----------------------------------------------------------------------------

__attribute__((optimize("align-functions=4"), naked)) void jvt_index_79(void) {
  __asm__ volatile ( R"(
    addi sp, sp, -8
    sw a0, 0(sp)
    sw a1, 4(sp)

    lw a0, g_expect_tablejmp
    lw a1, 0(a0)
    addi a1, a1, -79
    sw a1, 0(a0)

    lw a1, 4(sp)
    lw a0, 0(sp)
    addi sp, sp, 8
    ret

  )");
}

// -----------------------------------------------------------------------------

__attribute__((optimize("align-functions=4"), naked)) void jvt_index_255(void) {
  __asm__ volatile ( R"(
    addi sp, sp, -8
    sw a0, 0(sp)
    sw a1, 4(sp)

    lw a0, g_expect_tablejmp
    lw a1, 0(a0)
    addi a1, a1, -255
    sw a1, 0(a0)

    lw a1, 4(sp)
    lw a0, 0(sp)
    addi sp, sp, 8
    ret

  )");
}

// -----------------------------------------------------------------------------

uint32_t mstateen0_rw_m(uint32_t index, uint8_t report_name){
  volatile uint8_t     test_fail = 0;
  volatile mstateen0_t mstateen0 = { 0 };
  volatile mstateen0_t mstateen0_rval = { 0 };

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // CSRRW 0
  *g_expect_illegal = 0;
  mstateen0_rval.raw = csr_instr(CSRRW, MSTATEEN0_ADDR, mstateen0.raw);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRW 1 to bit 2 (jvt)
  *g_expect_illegal = 0;
  mstateen0.fields.jvt_access = 1;
  mstateen0_rval.raw = csr_instr(CSRRW, MSTATEEN0_ADDR, mstateen0.raw);
  // Read pre-value, should be zero
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRW 0 to bit 2 (jvt)
  *g_expect_illegal = 0;
  mstateen0.fields.jvt_access = 0;
  mstateen0_rval.raw = csr_instr(CSRRW, MSTATEEN0_ADDR, mstateen0.raw);
  // Read pre-value, jvt should be one
  test_fail += (mstateen0_rval.fields.jvt_access != 1) ? 1 : 0;
  mstateen0_rval.fields.jvt_access = 0;
  // Check that all others bits were zero (RO bits)
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRW all 1s
  *g_expect_illegal = 0;
  mstateen0.raw = 0xffffffffUL;
  mstateen0_rval.raw = csr_instr(CSRRW, MSTATEEN0_ADDR, mstateen0.raw);
  // Check pre-value, all bits should be zero
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRC clear all bits
  *g_expect_illegal = 0;
  mstateen0.raw = 0xffffffffUL;
  mstateen0_rval.raw = csr_instr(CSRRC, MSTATEEN0_ADDR, mstateen0.raw);
  // Check pre-value, only bit 2 should be 1
  test_fail += (mstateen0_rval.fields.jvt_access != 1) ? 1 : 0;
  mstateen0_rval.fields.jvt_access = 0;
  // Remaining bits should be zero
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRS set bit 2 (jvt)
  *g_expect_illegal = 0;
  mstateen0.raw = 0x0UL;
  mstateen0.fields.jvt_access = 1;
  mstateen0_rval.raw = csr_instr(CSRRS, MSTATEEN0_ADDR, mstateen0.raw);
  // Check pre-value, all bits should be zero
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRC bit 2 (jvt)
  *g_expect_illegal = 0;
  mstateen0.raw = 0x0UL;
  mstateen0.fields.jvt_access = 1;
  mstateen0_rval.raw = csr_instr(CSRRC, MSTATEEN0_ADDR, mstateen0.raw);
  // Read pre-value, jvt should be one
  test_fail += (mstateen0_rval.fields.jvt_access != 1) ? 1 : 0;
  mstateen0_rval.fields.jvt_access = 0;
  // Check that all others bits were zero (RO bits)
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRS set all bits
  *g_expect_illegal = 0;
  mstateen0.raw = 0xffffffffUL;
  mstateen0_rval.raw = csr_instr(CSRRS, MSTATEEN0_ADDR, mstateen0.raw);
  // Check pre-value, all bits should be zero
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI clear bit 2 (jvt)
  *g_expect_illegal = 0;
  mstateen0_rval.raw = csr_instr(CSRRWI, MSTATEEN0_ADDR, 0x0UL);
  // Read pre-value, jvt should be one
  test_fail += (mstateen0_rval.fields.jvt_access != 1) ? 1 : 0;
  mstateen0_rval.fields.jvt_access = 0;
  // Check that all others bits were zero (RO bits)
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI set bit 2 (jvt)
  *g_expect_illegal = 0;
  mstateen0_rval.raw = csr_instr(CSRRWI, MSTATEEN0_ADDR, 0x4UL);
  // Check pre-value, all bits should be zero
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRCI bit 2 (jvt)
  *g_expect_illegal = 0;
  mstateen0_rval.raw = csr_instr(CSRRCI, MSTATEEN0_ADDR, 0x4UL);
  // Read pre-value, jvt should be one
  test_fail += (mstateen0_rval.fields.jvt_access != 1) ? 1 : 0;
  mstateen0_rval.fields.jvt_access = 0;
  // Check that all others bits were zero (RO bits)
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI set all lower bits
  *g_expect_illegal = 0;
  mstateen0_rval.raw = csr_instr(CSRRWI, MSTATEEN0_ADDR, 0x1fUL);
  // Check pre-value, all bits should be zero
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI clear all lower bits
  *g_expect_illegal = 0;
  mstateen0_rval.raw = csr_instr(CSRRWI, MSTATEEN0_ADDR, 0x0UL);
  // Read pre-value, jvt should be one
  test_fail += (mstateen0_rval.fields.jvt_access != 1) ? 1 : 0;
  mstateen0_rval.fields.jvt_access = 0;
  // Check that all others bits were zero (RO bits)
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRSI set bit 2
  *g_expect_illegal = 0;
  mstateen0_rval.raw = csr_instr(CSRRSI, MSTATEEN0_ADDR, 0x4UL);
  // Check pre-value, all bits should be zero
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRCI all lower bits
  *g_expect_illegal = 0;
  mstateen0_rval.raw = csr_instr(CSRRCI, MSTATEEN0_ADDR, 0x1fUL);
  // Read pre-value, jvt should be one
  test_fail += (mstateen0_rval.fields.jvt_access != 1) ? 1 : 0;
  mstateen0_rval.fields.jvt_access = 0;
  // Check that all others bits were zero (RO bits)
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRSI set all lower bits
  *g_expect_illegal = 0;
  mstateen0_rval.raw = csr_instr(CSRRSI, MSTATEEN0_ADDR, 0x1fUL);
  // Check pre-value, all bits should be zero
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRCI bit 2 (jvt)
  *g_expect_illegal = 0;
  mstateen0_rval.raw = csr_instr(CSRRCI, MSTATEEN0_ADDR, 0x4UL);
  // Read pre-value, jvt should be one
  test_fail += (mstateen0_rval.fields.jvt_access != 1) ? 1 : 0;
  mstateen0_rval.fields.jvt_access = 0;
  // Check that all others bits were zero (RO bits)
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t mstateen0_rw_u_illegal(uint32_t index, uint8_t report_name){
  volatile uint8_t     test_fail      = 0;
  volatile mseccfg_t   mseccfg        = { 0 };
  volatile mstateen0_t mstateen0      = { 0 };
  volatile mstateen0_t mstateen0_rval = { 0 };
  volatile uint32_t    pmpaddr        = 0xffffffffUL;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Enable pmp-access for u-mode *full access for convenience*
  mseccfg.fields.rlb = 1;
  (void)csr_instr(CSRRW, MSECCFG_ADDR, mseccfg.raw);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 1,
      .fields.w = 1,
      .fields.x = 1,
      .fields.a = PMPMODE_TOR,
      .fields.l = 0
  }, 0);

  (void)csr_instr(CSRRW, PMPADDR0_ADDR, pmpaddr);

  // Switch to user mode
  __asm__ volatile ( R"( ecall )");

  // CSRRW 0
  *g_expect_illegal = 2;
  (void)csr_instr(CSRRW, MSTATEEN0_ADDR, mstateen0.raw);
  mstateen0_rval.raw = csr_instr(CSRRW, MSTATEEN0_ADDR, mstateen0.raw);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRW 1 to bit 2 (jvt)
  *g_expect_illegal = 2;
  mstateen0.fields.jvt_access = 1;
  (void)csr_instr(CSRRW, MSTATEEN0_ADDR, mstateen0.raw);
  mstateen0_rval.raw = csr_instr(CSRRW, MSTATEEN0_ADDR, mstateen0.raw);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRW 0 to bit 2 (jvt)
  *g_expect_illegal = 2;
  mstateen0.fields.jvt_access = 0;
  (void)csr_instr(CSRRW, MSTATEEN0_ADDR, mstateen0.raw);
  mstateen0_rval.raw = csr_instr(CSRRW, MSTATEEN0_ADDR, mstateen0.raw);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRW all 1s
  *g_expect_illegal = 2;
  mstateen0.raw = 0xffffffffUL;
  (void)csr_instr(CSRRW, MSTATEEN0_ADDR, mstateen0.raw);
  mstateen0_rval.raw = csr_instr(CSRRW, MSTATEEN0_ADDR, mstateen0.raw);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRC clear all bits
  *g_expect_illegal = 2;
  mstateen0.raw = 0xffffffffUL;
  (void)csr_instr(CSRRC, MSTATEEN0_ADDR, mstateen0.raw);
  mstateen0_rval.raw = csr_instr(CSRRC, MSTATEEN0_ADDR, mstateen0.raw);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRS set bit 2 (jvt)
  *g_expect_illegal = 2;
  mstateen0.raw = 0x0UL;
  mstateen0.fields.jvt_access = 1;
  (void)csr_instr(CSRRS, MSTATEEN0_ADDR, mstateen0.raw);
  mstateen0_rval.raw = csr_instr(CSRRS, MSTATEEN0_ADDR, mstateen0.raw);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRC bit 2 (jvt)
  *g_expect_illegal = 2;
  mstateen0.raw = 0x0UL;
  mstateen0.fields.jvt_access = 1;
  (void)csr_instr(CSRRC, MSTATEEN0_ADDR, mstateen0.raw);
  mstateen0_rval.raw = csr_instr(CSRRC, MSTATEEN0_ADDR, mstateen0.raw);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRS set all bits
  *g_expect_illegal = 2;
  mstateen0.raw = 0xffffffffUL;
  (void)csr_instr(CSRRS, MSTATEEN0_ADDR, mstateen0.raw);
  mstateen0_rval.raw = csr_instr(CSRRS, MSTATEEN0_ADDR, mstateen0.raw);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRWI clear bit 2 (jvt)
  *g_expect_illegal = 2;
  (void)csr_instr(CSRRWI, MSTATEEN0_ADDR, 0x0UL);
  mstateen0_rval.raw = csr_instr(CSRRWI, MSTATEEN0_ADDR, 0x0UL);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRWI set bit 2 (jvt)
  *g_expect_illegal = 2;
  (void)csr_instr(CSRRWI, MSTATEEN0_ADDR, 0x4UL);
  mstateen0_rval.raw = csr_instr(CSRRWI, MSTATEEN0_ADDR, 0x4UL);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRCI bit 2 (jvt)
  *g_expect_illegal = 2;
  (void)csr_instr(CSRRCI, MSTATEEN0_ADDR, 0x4UL);
  mstateen0_rval.raw = csr_instr(CSRRCI, MSTATEEN0_ADDR, 0x4UL);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRWI set all bits
  *g_expect_illegal = 2;
  (void)csr_instr(CSRRWI, MSTATEEN0_ADDR, 0xfffUL);
  mstateen0_rval.raw = csr_instr(CSRRWI, MSTATEEN0_ADDR, 0xfffUL);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRWI clear all bits
  *g_expect_illegal = 2;
  (void)csr_instr(CSRRWI, MSTATEEN0_ADDR, 0x0UL);
  mstateen0_rval.raw = csr_instr(CSRRWI, MSTATEEN0_ADDR, 0x0UL);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRSI set bit 2
  *g_expect_illegal = 2;
  (void)csr_instr(CSRRSI, MSTATEEN0_ADDR, 0x4UL);
  mstateen0_rval.raw = csr_instr(CSRRSI, MSTATEEN0_ADDR, 0x4UL);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRCI all lower bits
  *g_expect_illegal = 2;
  (void)csr_instr(CSRRCI, MSTATEEN0_ADDR, 0x1fUL);
  mstateen0_rval.raw = csr_instr(CSRRCI, MSTATEEN0_ADDR, 0x1fUL);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRSI set all lower bits
  *g_expect_illegal = 2;
  (void)csr_instr(CSRRSI, MSTATEEN0_ADDR, 0x1fUL);
  mstateen0_rval.raw = csr_instr(CSRRSI, MSTATEEN0_ADDR, 0x1fUL);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);

  // CSRRCI bit 2 (jvt)
  *g_expect_illegal = 2;
  (void)csr_instr(CSRRCI, MSTATEEN0_ADDR, 0x4UL);
  mstateen0_rval.raw = csr_instr(CSRRCI, MSTATEEN0_ADDR, 0x4UL);
  test_fail += (mstateen0_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;
  assert(!test_fail);


  // Switch back to machine mode
  __asm__ volatile ( R"( ecall )");

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t jvt_rw_m(uint32_t index, uint8_t report_name){
  volatile uint8_t test_fail = 0;
  volatile jvt_t   jvt       = { 0 };
  volatile jvt_t   jvt_rval  = { 0 };

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // CSRRW 0
  *g_expect_illegal = 0;
  jvt_rval.raw = csr_instr(CSRRW, JVT_ADDR, jvt.raw);
  // Check pre-value, all bits should be zero
  test_fail += (jvt_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRW all 1s
  *g_expect_illegal = 0;
  jvt.raw = 0xffffffffUL;
  jvt_rval.raw = csr_instr(CSRRW, JVT_ADDR, jvt.raw);
  // Check pre-value, all bits should be zero
  test_fail += (jvt_rval.fields.mode != 0) ? 1 : 0;
  test_fail += (jvt_rval.fields.base != 0x0UL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRC clear all bits
  *g_expect_illegal = 0;
  jvt.raw = 0xffffffffUL;
  jvt_rval.raw = csr_instr(CSRRC, JVT_ADDR, jvt.raw);
  // Check pre-value, should be all 1s
  test_fail += (jvt_rval.fields.mode != 0) ? 1 : 0;
  test_fail += (jvt_rval.fields.base != 0x3ffffffUL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRS set all bits
  *g_expect_illegal = 0;
  jvt.raw = 0xffffffffUL;
  jvt_rval.raw = csr_instr(CSRRS, JVT_ADDR, jvt.raw);
  // Check pre-value, all bits should be zero
  test_fail += (jvt_rval.fields.mode != 0) ? 1 : 0;
  test_fail += (jvt_rval.fields.base != 0x0UL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI clear all bits
  *g_expect_illegal = 0;
  jvt_rval.raw = csr_instr(CSRRWI, JVT_ADDR, 0x0UL);
  // Read pre-value, all bits should be 1
  test_fail += (jvt_rval.fields.mode != 0) ? 1 : 0;
  test_fail += (jvt_rval.fields.base != 0x3ffffffUL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI set all lower bits
  *g_expect_illegal = 0;
  jvt_rval.raw = csr_instr(CSRRWI, JVT_ADDR, 0x1fUL);
  // Check pre-value, all bits should be zero
  test_fail += (jvt_rval.fields.mode != 0) ? 1 : 0;
  test_fail += (jvt_rval.fields.base != 0x0UL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRCI clear all lower bits
  *g_expect_illegal = 0;
  jvt_rval.raw = csr_instr(CSRRCI, JVT_ADDR, 0x1fUL);
  // Read pre-value, all bits should be 1
  test_fail += (jvt_rval.fields.mode != 0) ? 1 : 0;
  test_fail += (jvt_rval.fields.base != 0x0UL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRSI set all lower bits
  *g_expect_illegal = 0;
  jvt_rval.raw = csr_instr(CSRRWI, JVT_ADDR, 0x1fUL);
  // Check pre-value, all bits should be zero
  test_fail += (jvt_rval.fields.mode != 0) ? 1 : 0;
  test_fail += (jvt_rval.fields.base != 0x0UL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI clear all
  *g_expect_illegal = 0;
  jvt_rval.raw = csr_instr(CSRRWI, JVT_ADDR, 0x0UL);
  // Read pre-value, all bits should be 1
  test_fail += (jvt_rval.fields.mode != 0) ? 1 : 0;
  test_fail += (jvt_rval.fields.base != 0x0UL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t jvt_rw_u_illegal(uint32_t index, uint8_t report_name){
  volatile uint8_t   test_fail = 0;
  volatile mseccfg_t mseccfg   = { 0 };
  volatile uint32_t  jvt_rval  = 0UL;
  volatile uint32_t  jvt       = 0UL;
  volatile uint32_t  pmpaddr   = 0xffffffffUL;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Enable pmp-access for u-mode *full access for convenience*
  mseccfg.fields.rlb = 1;
  (void)csr_instr(CSRRW, MSECCFG_ADDR, mseccfg.raw);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 1,
      .fields.w = 1,
      .fields.x = 1,
      .fields.a = PMPMODE_TOR,
      .fields.l = 0
  }, 0);

  (void)csr_instr(CSRRW, PMPADDR0_ADDR, pmpaddr);

  // Switch to user mode
  __asm__ volatile ( R"( ecall )");

  // CSRRW 0
  *g_expect_illegal = 2;
  jvt_rval = csr_instr(CSRRW, JVT_ADDR, jvt);
  (void)csr_instr(CSRRW, JVT_ADDR, jvt);
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRW all 1s
  *g_expect_illegal = 2;
  jvt = 0xffffffffUL;
  jvt_rval = csr_instr(CSRRW, JVT_ADDR, jvt);
  (void)csr_instr(CSRRW, JVT_ADDR, jvt);
  test_fail += (jvt_rval != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRC clear all bits
  *g_expect_illegal = 2;
  jvt = 0xffffffffUL;
  jvt_rval = csr_instr(CSRRC, JVT_ADDR, jvt);
  (void)csr_instr(CSRRC, JVT_ADDR, jvt);
  test_fail += (jvt_rval != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRS set all bits
  *g_expect_illegal = 2;
  jvt = 0xffffffffUL;
  jvt_rval = csr_instr(CSRRS, JVT_ADDR, jvt);
  (void)csr_instr(CSRRS, JVT_ADDR, jvt);
  test_fail += (jvt_rval != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI clear all bits
  *g_expect_illegal = 2;
  jvt_rval = csr_instr(CSRRWI, JVT_ADDR, 0x0UL);
  (void)csr_instr(CSRRWI, JVT_ADDR, 0x0UL);
  test_fail += (jvt_rval != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI set all lower bits
  *g_expect_illegal = 2;
  jvt_rval = csr_instr(CSRRWI, JVT_ADDR, 0xfffUL);
  (void)csr_instr(CSRRWI, JVT_ADDR, 0xfffUL);
  test_fail += (jvt_rval != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRCI clear all lower bits
  *g_expect_illegal = 2;
  jvt_rval = csr_instr(CSRRCI, JVT_ADDR, 0xfffUL);
  (void)csr_instr(CSRRCI, JVT_ADDR, 0xfffUL);
  test_fail += (jvt_rval != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRSI set all lower bits
  *g_expect_illegal = 2;
  jvt_rval = csr_instr(CSRRWI, JVT_ADDR, 0xfffUL);
  (void)csr_instr(CSRRWI, JVT_ADDR, 0xfffUL);
  test_fail += (jvt_rval != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI clear all
  *g_expect_illegal = 2;
  jvt_rval = csr_instr(CSRRWI, JVT_ADDR, 0x0UL);
  (void)csr_instr(CSRRWI, JVT_ADDR, 0x0UL);
  test_fail += (jvt_rval != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // Switch back to machine mode
  __asm__ volatile ( R"( ecall )");

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t jvt_rw_u_legal(uint32_t index, uint8_t report_name){
  volatile uint8_t     test_fail = 0;
  volatile mseccfg_t   mseccfg   = { 0 };
  volatile jvt_t       jvt_rval  = { 0 };
  volatile jvt_t       jvt       = { 0 };
  volatile mstateen0_t mstateen0 = { 0 };
  volatile uint32_t    pmpaddr   = 0xffffffffUL;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Enable pmp-access for u-mode *full access for convenience*
  mseccfg.fields.rlb = 1;
  (void)csr_instr(CSRRW, MSECCFG_ADDR, mseccfg.raw);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 1,
      .fields.w = 1,
      .fields.x = 1,
      .fields.a = PMPMODE_TOR,
      .fields.l = 0
  }, 0);

  (void)csr_instr(CSRRW, PMPADDR0_ADDR, pmpaddr);

  mstateen0.fields.jvt_access = 1;
  (void)csr_instr(CSRRS, MSTATEEN0_ADDR, mstateen0.raw);

  // Switch to user mode
  __asm__ volatile ( R"( ecall )");

  // CSRRW jvt_t
  *g_expect_illegal = 0;
  jvt_rval.raw = csr_instr(CSRRW, JVT_ADDR, jvt.raw);
  // Check pre-value, all bits should be zero
  test_fail += (jvt_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRW all 1s
  *g_expect_illegal = 0;
  jvt.raw = 0xffffffffUL;
  jvt_rval.raw = csr_instr(CSRRW, JVT_ADDR, jvt.raw);
  // Check pre-value, all bits should be zero
  test_fail += (jvt_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRC clear all bits
  *g_expect_illegal = 0;
  jvt.raw = 0xffffffffUL;
  jvt_rval.raw = csr_instr(CSRRC, JVT_ADDR, jvt.raw);
  // Check pre-value, should be all 1s
  test_fail += (jvt_rval.fields.mode != 0x0) ? 1 : 0;
  test_fail += (jvt_rval.fields.base != 0x3ffffffUL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRS set all bits
  *g_expect_illegal = 0;
  jvt.raw = 0xffffffffUL;
  jvt_rval.raw = csr_instr(CSRRS, JVT_ADDR, jvt.raw);
  // Check pre-value, all bits should be zero
  test_fail += (jvt_rval.raw != 0) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI clear all
  *g_expect_illegal = 0;
  jvt_rval.raw = csr_instr(CSRRWI, JVT_ADDR, 0x0UL);
  // Read pre-value, all bits should be 1
  test_fail += (jvt_rval.fields.mode != 0x0) ? 1 : 0;
  test_fail += (jvt_rval.fields.base != 0x3ffffffUL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI set all lower bits
  *g_expect_illegal = 0;
  jvt_rval.raw = csr_instr(CSRRWI, JVT_ADDR, 0x1fUL);
  // Check pre-value, all bits should be zero
  test_fail += (jvt_rval.raw != 0x0UL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRCI clear all lower bits
  *g_expect_illegal = 0;
  jvt_rval.raw = csr_instr(CSRRCI, JVT_ADDR, 0x1fUL);
  // Read pre-value, all bits should be 0 due to RO .mode
  test_fail += (jvt_rval.raw != 0x0UL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRSI set all bits
  *g_expect_illegal = 0;
  jvt_rval.raw = csr_instr(CSRRWI, JVT_ADDR, 0x1fUL);
  // Check pre-value, all bits should be zero
  test_fail += (jvt_rval.raw != 0x0UL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // CSRRWI clear all
  *g_expect_illegal = 0;
  jvt_rval.raw = csr_instr(CSRRWI, JVT_ADDR, 0x0UL);
  // Read pre-value, all bits should be 0 due to RO .mode
  test_fail += (jvt_rval.raw != 0x0UL) ? 1 : 0;
  test_fail += (*g_expect_illegal != 0) ? 1 : 0;

  // Switch back to machine mode
  __asm__ volatile ( R"( ecall )");

  mstateen0.fields.jvt_access = 1;
  (void)csr_instr(CSRRC, MSTATEEN0_ADDR, mstateen0.raw);

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t cm_jt_m(uint32_t index, uint8_t report_name){
  volatile uint8_t   test_fail = 0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  (void)csr_instr(CSRRW, JVT_ADDR, ((uint32_t)&jvt_table));

  *g_expect_tablejmp = 1 + 31;
  __asm__ volatile ( R"(
    .global recovery_cm_jt_m_0
    .global recovery_cm_jt_m_1
    .global recovery_cm_jt_m_31
    addi sp, sp, -12
    sw a0, 0(sp)
    sw a1, 4(sp)
    sw a2, 8(sp)

    lw a0, g_recovery_cm_jt
    la a1, recovery_cm_jt_m_0
    sw a1, 0(a0)

    cm.jt  0
    recovery_cm_jt_m_0:

    lw a0, g_recovery_cm_jt
    la a1, recovery_cm_jt_m_1
    sw a1, 0(a0)

    cm.jt  1
    recovery_cm_jt_m_1:

    lw a0, g_recovery_cm_jt
    la a1, recovery_cm_jt_m_31
    sw a1, 0(a0)

    cm.jt 31
    recovery_cm_jt_m_31:

    lw a2, 8(sp)
    lw a1, 4(sp)
    lw a0, 0(sp)
    addi sp, sp, 12
  )" ::: "ra", "memory");

  test_fail += (*g_expect_tablejmp != 0) ? 1 : 0;

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t cm_jalt_m(uint32_t index, uint8_t report_name){
  volatile uint8_t   test_fail = 0;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  (void)csr_instr(CSRRW, JVT_ADDR, ((uint32_t)&jvt_table));
  *g_expect_tablejmp = 32 + 79 + 255;

  __asm__ volatile ( R"(
    cm.jalt 32
    cm.jalt 79
    cm.jalt 255
  )" ::: "ra", "memory");

  test_fail += (*g_expect_tablejmp != 0) ? 1 : 0;

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t cm_jt_u_illegal(uint32_t index, uint8_t report_name){
  volatile uint8_t   test_fail = 0;
  volatile mseccfg_t mseccfg   = { 0 };
  volatile uint32_t  pmpaddr   = 0xffffffffUL;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Enable pmp-access for u-mode *full access for convenience*
  mseccfg.fields.rlb = 1;
  (void)csr_instr(CSRRW, MSECCFG_ADDR, mseccfg.raw);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 1,
      .fields.w = 1,
      .fields.x = 1,
      .fields.a = PMPMODE_TOR,
      .fields.l = 0
  }, 0);

  (void)csr_instr(CSRRW, PMPADDR0_ADDR, pmpaddr);

  (void)csr_instr(CSRRW, JVT_ADDR, ((uint32_t)&jvt_table));
  *g_expect_tablejmp = 0;

  __asm__ volatile ( R"(
    ecall
    cm.jt 0
    cm.jt 1
    cm.jt 15
    cm.jt 16
    cm.jt 30
    cm.jt 31
    ecall
  )" ::: "ra", "memory");

  test_fail += (*g_expect_tablejmp != 0) ? 1 : 0;

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------
uint32_t cm_jalt_u_illegal(uint32_t index, uint8_t report_name) {
  volatile uint8_t   test_fail = 0;
  volatile mseccfg_t mseccfg   = { 0 };
  volatile uint32_t  pmpaddr   = 0xffffffffUL;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Enable pmp-access for u-mode *full access for convenience*
  mseccfg.fields.rlb = 1;
  (void)csr_instr(CSRRW, MSECCFG_ADDR, mseccfg.raw);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 1,
      .fields.w = 1,
      .fields.x = 1,
      .fields.a = PMPMODE_TOR,
      .fields.l = 0
  }, 0);

  (void)csr_instr(CSRRW, PMPADDR0_ADDR, pmpaddr);

  (void)csr_instr(CSRRW, JVT_ADDR, ((uint32_t)&jvt_table));
  *g_expect_tablejmp = 0;

  __asm__ volatile ( R"(
    ecall
    cm.jalt 32
    cm.jalt 33
    cm.jalt 127
    cm.jalt 128
    cm.jalt 254
    cm.jalt 255
    ecall
  )" ::: "ra", "memory");

  test_fail += (*g_expect_tablejmp != 0) ? 1 : 0;

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t cm_jt_u_legal(uint32_t index, uint8_t report_name){
  volatile uint8_t   test_fail   = 0;
  volatile mseccfg_t mseccfg     = { 0 };
  volatile mstateen0_t mstateen0 = { 0 };
  volatile uint32_t  pmpaddr     = 0xffffffffUL;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }
  // Enable pmp-access for u-mode *full access for convenience*
  mseccfg.fields.rlb = 1;
  (void)csr_instr(CSRRW, MSECCFG_ADDR, mseccfg.raw);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 1,
      .fields.w = 1,
      .fields.x = 1,
      .fields.a = PMPMODE_TOR,
      .fields.l = 0
  }, 0);

  (void)csr_instr(CSRRW, PMPADDR0_ADDR, pmpaddr);

  mstateen0.fields.jvt_access = 1;
  (void)csr_instr(CSRRS, MSTATEEN0_ADDR, mstateen0.raw);

  (void)csr_instr(CSRRW, JVT_ADDR, ((uint32_t)&jvt_table));

  *g_expect_tablejmp = 0 + 1 + 31;

  __asm__ volatile ( R"(
    .global recovery_cm_jt_u_0
    .global recovery_cm_jt_u_1
    .global recovery_cm_jt_u_31
    ecall
    addi sp, sp, -12
    sw a0, 0(sp)
    sw a1, 4(sp)
    sw a2, 8(sp)

    lw a0, g_recovery_cm_jt
    la a1, recovery_cm_jt_u_0
    sw a1, 0(a0)

    cm.jt  0
    recovery_cm_jt_u_0:

    lw a0, g_recovery_cm_jt
    la a1, recovery_cm_jt_u_1
    sw a1, 0(a0)

    cm.jt  1
    recovery_cm_jt_u_1:

    lw a0, g_recovery_cm_jt
    la a1, recovery_cm_jt_u_31
    sw a1, 0(a0)

    cm.jt 31
    recovery_cm_jt_u_31:

    lw a2, 8(sp)
    lw a1, 4(sp)
    lw a0, 0(sp)
    addi sp, sp, 12
    ecall
  )" ::: "ra", "memory");

  mstateen0.fields.jvt_access = 1;
  (void)csr_instr(CSRRC, MSTATEEN0_ADDR, mstateen0.raw);

  test_fail += (*g_expect_tablejmp != 0) ? 1 : 0;

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t cm_jalt_u_legal(uint32_t index, uint8_t report_name){
  volatile uint8_t   test_fail   = 0;
  volatile mseccfg_t mseccfg     = { 0 };
  volatile mstateen0_t mstateen0 = { 0 };
  volatile uint32_t  pmpaddr     = 0xffffffffUL;

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  // Enable pmp-access for u-mode *full access for convenience*
  mseccfg.fields.rlb = 1;
  (void)csr_instr(CSRRW, MSECCFG_ADDR, mseccfg.raw);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 1,
      .fields.w = 1,
      .fields.x = 1,
      .fields.a = PMPMODE_TOR,
      .fields.l = 0
  }, 0);

  (void)csr_instr(CSRRW, PMPADDR0_ADDR, pmpaddr);

  mstateen0.fields.jvt_access = 1;
  (void)csr_instr(CSRRS, MSTATEEN0_ADDR, mstateen0.raw);

  (void)csr_instr(CSRRW, JVT_ADDR, ((uint32_t)&jvt_table));

  *g_expect_tablejmp = 32 + 79 + 255;

  __asm__ volatile ( R"(
    ecall
    cm.jalt 32
    cm.jalt 79
    cm.jalt 255
    ecall
  )" ::: "ra", "memory");

  mstateen0.fields.jvt_access = 1;
  (void)csr_instr(CSRRC, MSTATEEN0_ADDR, mstateen0.raw);

  test_fail += (*g_expect_tablejmp != 0) ? 1 : 0;

  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t cm_jt_m_trap(uint32_t index,  uint8_t report_name){
  volatile uint8_t test_fail = 0;
  volatile mseccfg_t mseccfg = { 0 };

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  (void)csr_instr(CSRRW, JVT_ADDR, ((uint32_t)&jvt_table));

  mseccfg.fields.rlb = 1;
  (void)csr_instr(CSRRW, MSECCFG_ADDR, mseccfg.raw);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 1,
      .fields.w = 1,
      .fields.x = 1,
      .fields.a = PMPMODE_TOR,
      .fields.l = 0
    }, 0);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 0,
      .fields.w = 0,
      .fields.x = 0,
      .fields.a = PMPMODE_TOR,
      .fields.l = 1
    }, 1);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 1,
      .fields.w = 1,
      .fields.x = 1,
      .fields.a = PMPMODE_TOR,
      .fields.l = 0
    }, 2);

  // Set PMP configuration (lock down index 2 in table)
  (void)csr_instr(CSRRW, PMPADDR0_ADDR, ((uint32_t)&jvt_table + 2*4) >> 2);
  (void)csr_instr(CSRRW, PMPADDR1_ADDR, ((uint32_t)&jvt_table + 3*4) >> 2);
  (void)csr_instr(CSRRW, PMPADDR2_ADDR, 0xffffffffUL >> 2);

  *g_expect_tablejmp = 2;
  __asm__ volatile ( R"(
    .global recovery_cm_jt_m_2
    addi sp, sp, -12
    sw a0, 0(sp)
    sw a1, 4(sp)
    sw a2, 8(sp)

    lw a0, g_recovery_cm_jt
    la a1, recovery_cm_jt_m_2
    sw a1, 0(a0)

    cm.jt 2
    recovery_cm_jt_m_2:
    lw a2, 8(sp)
    lw a1, 4(sp)
    lw a0, 0(sp)

    addi sp, sp, 12
  )");

  test_fail += (*g_expect_tablejmp != 0) ? 1 : 0;
  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

uint32_t cm_jalt_m_trap(uint32_t index,  uint8_t report_name){
  volatile uint8_t test_fail = 0;
  volatile mseccfg_t mseccfg = { 0 };

  SET_FUNC_INFO

  if (report_name) {
    cvprintf(V_LOW, "\"%s\"", name);
    return 0;
  }

  (void)csr_instr(CSRRW, JVT_ADDR, ((uint32_t)&jvt_table));

  mseccfg.fields.rlb = 1;
  (void)csr_instr(CSRRW, MSECCFG_ADDR, mseccfg.raw);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 1,
      .fields.w = 1,
      .fields.x = 1,
      .fields.a = PMPMODE_TOR,
      .fields.l = 0
    }, 0);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 0,
      .fields.w = 0,
      .fields.x = 0,
      .fields.a = PMPMODE_TOR,
      .fields.l = 1
    }, 1);

  set_pmpcfg((pmpsubcfg_t){
      .fields.r = 1,
      .fields.w = 1,
      .fields.x = 1,
      .fields.a = PMPMODE_TOR,
      .fields.l = 0
    }, 2);

  // Set PMP configuration (lock down index 2 in table)
  (void)csr_instr(CSRRW, PMPADDR0_ADDR, ((uint32_t)&jvt_table + 35*4) >> 2);
  (void)csr_instr(CSRRW, PMPADDR1_ADDR, ((uint32_t)&jvt_table + 36*4) >> 2);
  (void)csr_instr(CSRRW, PMPADDR2_ADDR, 0xffffffffUL >> 2);

  *g_expect_tablejmp = 35;
  __asm__ volatile ( R"(
    cm.jalt 35
  )");

  test_fail += (*g_expect_tablejmp != 0) ? 1 : 0;
  if (test_fail) {
    // Should never be here in this test case unless something goes really wrong
    cvprintf(V_LOW, "\nTest: \"%s\" FAIL!\n", name);
    return index + 1;
  }
  cvprintf(V_MEDIUM, "\nTest: \"%s\" No self checking in this test, OK!\n", name);
  return 0;
}

// -----------------------------------------------------------------------------

__attribute__((naked)) void handle_insn_access_fault(void) {
  __asm__ volatile ( R"(
    call handle_insn_access_fault_code
    j end_handler_ret
  )");
}

// -----------------------------------------------------------------------------

void handle_insn_access_fault_code(void) {
  volatile uint32_t mepc;
  volatile mcause_t mcause = { 0 };
  volatile jvt_t    jvt    = { 0 };

  // RWX !L & MODE OFF
  volatile const uint32_t pmp_enable_access_all = 0x07070707;

  __asm__ volatile ( R"(
     csrrs %[mc], mcause, x0
     csrrs %[mp], mepc, x0
     csrrs %[jvt], 0x017, x0
     )"
     : [mc] "=r"(mcause.raw),
       [mp] "=r"(mepc),
       [jvt] "=r"(jvt.raw)
     :
     :
     );

  cvprintf(V_DEBUG, "In handler, mepc: 0x%08lx, mcause: 0x%08lx\n", mepc, mcause.raw);

  switch (mcause.clic.interrupt) {
    case 0:
      switch (mcause.clic.exccode) {
        case 0x1: cvprintf(V_LOW, "Instruction access fault at 0x%08lx\n", mepc);
                  break;
        case 0x2: cvprintf(V_LOW, "Invalid instruction fault at 0x%08lx\n", mepc);
                  break;
      }
      break;
    case 1:
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
