// Copyright (c) 2026 Amit Matth
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


/**
 * mscratch CSR Essential Test Program
 * 
 * Verifies full 32-bit read/write access to mscratch register (CSR 0x340)
 * 
 * Essential Tests:
 *   1. Boundary patterns (all zeros/ones)
 *   2. Walking-1 (each bit independently settable)
 *   3. Walking-0 (each bit independently clearable)
 *   4. CSRRW atomic swap
 *   5. CSRRS/CSRRC atomic bit manipulation
 *   6. Immediate variants (CSRRWI/CSRRSI/CSRRCI)
 */

#include <stdio.h>
#include <stdint.h>

/* CSR Access Macros */
#define CSR_WRITE(csr, val)        asm volatile ("csrw " #csr ", %0" :: "r"(val))
#define CSR_READ(csr, dest)        asm volatile ("csrr %0, " #csr : "=r"(dest))
#define CSR_SWAP(csr, rd, rs)      asm volatile ("csrrw %0, " #csr ", %1" : "=r"(rd) : "r"(rs))
#define CSR_SET_BITS(csr, rd, rs)  asm volatile ("csrrs %0, " #csr ", %1" : "=r"(rd) : "r"(rs))
#define CSR_CLR_BITS(csr, rd, rs)  asm volatile ("csrrc %0, " #csr ", %1" : "=r"(rd) : "r"(rs))
#define CSR_SWAP_IMM(csr, rd, imm)     asm volatile ("csrrwi %0, " #csr ", " #imm : "=r"(rd))
#define CSR_SET_BITS_IMM(csr, rd, imm) asm volatile ("csrrsi %0, " #csr ", " #imm : "=r"(rd))
#define CSR_CLR_BITS_IMM(csr, rd, imm) asm volatile ("csrrci %0, " #csr ", " #imm : "=r"(rd))

static int tests_run = 0;
static int tests_passed = 0;

/* Test a write/read pattern */
static int test_pattern(uint32_t pattern)
{
    uint32_t readback;
    tests_run++;
    CSR_WRITE(mscratch, pattern);
    CSR_READ(mscratch, readback);
    if (readback == pattern) {
        tests_passed++;
        return 1;
    }
    printf("  [FAIL] Wrote 0x%08X, Read 0x%08X\n", pattern, readback);
    return 0;
}

int main(void)
{
    uint32_t old_val, readback;
    int errors;

    printf("\n=== mscratch CSR (0x340) Test Suite ===\n\n");

    /*---------------------------------------------------------------
     * Test 1: Boundary Patterns
     *---------------------------------------------------------------*/
    printf("Test 1: Boundary Patterns\n");
    test_pattern(0x00000000);
    test_pattern(0xFFFFFFFF);
    printf("  [DONE]\n\n");

    /*---------------------------------------------------------------
     * Test 2: Walking-1 (verify each bit can be set)
     *---------------------------------------------------------------*/
    printf("Test 2: Walking-1 (32 bits)\n");
    errors = 0;
    for (int i = 0; i < 32; i++) {
        if (!test_pattern(1U << i)) errors++;
    }
    printf("  [DONE] %d errors\n\n", errors);

    /*---------------------------------------------------------------
     * Test 3: Walking-0 (verify each bit can be cleared)
     *---------------------------------------------------------------*/
    printf("Test 3: Walking-0 (32 bits)\n");
    errors = 0;
    for (int i = 0; i < 32; i++) {
        if (!test_pattern(~(1U << i))) errors++;
    }
    printf("  [DONE] %d errors\n\n", errors);

    /*---------------------------------------------------------------
     * Test 4: CSRRW Atomic Swap
     *---------------------------------------------------------------*/
    printf("Test 4: CSRRW Atomic Swap\n");
    tests_run++;
    CSR_WRITE(mscratch, 0xDEADBEEF);
    CSR_SWAP(mscratch, old_val, 0x12345678);
    CSR_READ(mscratch, readback);

    if (old_val == 0xDEADBEEF && readback == 0x12345678) {
        tests_passed++;
        printf("  [PASS] old=0x%08X, new=0x%08X\n", old_val, readback);
    } else {
        printf("  [FAIL] old=0x%08X (exp 0xDEADBEEF), new=0x%08X (exp 0x12345678)\n",
               old_val, readback);
    }
    printf("\n");

    /*---------------------------------------------------------------
     * Test 5: CSRRS/CSRRC Atomic Bit Set/Clear
     *---------------------------------------------------------------*/
    printf("Test 5: CSRRS/CSRRC Atomic Bit Manipulation\n");
    tests_run++;
    errors = 0;

    CSR_WRITE(mscratch, 0x00000000);
    
    /* Set bits [3:0] */
    CSR_SET_BITS(mscratch, old_val, 0x0F);
    CSR_READ(mscratch, readback);
    if (old_val != 0x00000000 || readback != 0x0000000F) errors++;

    /* Clear bit 0 */
    CSR_CLR_BITS(mscratch, old_val, 0x01);
    CSR_READ(mscratch, readback);
    if (old_val != 0x0000000F || readback != 0x0000000E) errors++;

    if (errors == 0) {
        tests_passed++;
        printf("  [PASS] CSRRS/CSRRC verified\n");
    } else {
        printf("  [FAIL] %d errors in atomic bit operations\n", errors);
    }
    printf("\n");

    /*---------------------------------------------------------------
     * Test 6: Immediate Variants (5-bit immediate)
     *---------------------------------------------------------------*/
    printf("Test 6: Immediate Variants (CSRRWI/CSRRSI/CSRRCI)\n");
    tests_run++;
    errors = 0;

    /* CSRRWI: swap with immediate */
    CSR_WRITE(mscratch, 0xAAAAAAAA);
    CSR_SWAP_IMM(mscratch, old_val, 0x1F);
    CSR_READ(mscratch, readback);
    if (old_val != 0xAAAAAAAA || readback != 0x1F) errors++;

    /* CSRRSI: set bits with immediate */
    CSR_WRITE(mscratch, 0x00000000);
    CSR_SET_BITS_IMM(mscratch, old_val, 0x15);
    CSR_READ(mscratch, readback);
    if (readback != 0x15) errors++;

    /* CSRRCI: clear bits with immediate */
    CSR_WRITE(mscratch, 0xFFFFFFFF);
    CSR_CLR_BITS_IMM(mscratch, old_val, 0x1F);
    CSR_READ(mscratch, readback);
    if (readback != 0xFFFFFFE0) errors++;

    if (errors == 0) {
        tests_passed++;
        printf("  [PASS] All immediate variants verified\n");
    } else {
        printf("  [FAIL] %d errors in immediate operations\n", errors);
    }
    printf("\n");

    /*---------------------------------------------------------------
     * Test 7: Alternating Bit Patterns (crosstalk detection)
     *---------------------------------------------------------------*/
    printf("Test 7: Alternating Bit Patterns\n");
    errors = 0;
    
    if (!test_pattern(0xAAAAAAAA)) errors++;  /* 10101010... */
    if (!test_pattern(0x55555555)) errors++;  /* 01010101... */
    if (!test_pattern(0xF0F0F0F0)) errors++;  /* Nibble alternating */
    if (!test_pattern(0x0F0F0F0F)) errors++;
    if (!test_pattern(0xFF00FF00)) errors++;  /* Byte alternating */
    if (!test_pattern(0x00FF00FF)) errors++;
    
    if (errors == 0) {
        printf("  [PASS] No adjacent bit interference detected\n");
    } else {
        printf("  [FAIL] %d pattern errors (possible crosstalk)\n", errors);
    }
    printf("\n");

    /*---------------------------------------------------------------
     * Test 8: Back-to-back Atomic Operations
     *---------------------------------------------------------------*/
    printf("Test 8: Back-to-back Atomic Operations\n");
    tests_run++;
    errors = 0;
    
    uint32_t v1, v2, v3, v4;
    
    CSR_WRITE(mscratch, 0x00000000);
    CSR_SET_BITS(mscratch, v1, 0x000000FF);  /* Set byte 0 */
    CSR_SET_BITS(mscratch, v2, 0x0000FF00);  /* Set byte 1 */
    CSR_CLR_BITS(mscratch, v3, 0x0000000F);  /* Clear lower nibble */
    CSR_SWAP(mscratch, v4, 0xCAFEBABE);      /* Swap entire value */
    CSR_READ(mscratch, readback);
    
    /* Verify each intermediate value */
    if (v1 != 0x00000000) errors++;  /* Initial state */
    if (v2 != 0x000000FF) errors++;  /* After first set */
    if (v3 != 0x0000FFFF) errors++;  /* After second set */
    if (v4 != 0x0000FFF0) errors++;  /* After clear */
    if (readback != 0xCAFEBABE) errors++;  /* Final value */
    
    if (errors == 0) {
        tests_passed++;
        printf("  [PASS] Atomic operation chain verified\n");
    } else {
        printf("  [FAIL] %d errors in atomic chain\n", errors);
    }
    printf("\n");

    /*---------------------------------------------------------------
     * Summary
     *---------------------------------------------------------------*/
    CSR_WRITE(mscratch, 0);

    printf("=== SUMMARY ===\n");
    printf("Tests: %d/%d passed\n", tests_passed, tests_run);

    if (tests_passed == tests_run) {
        printf("SUCCESS: Full 32-bit CSR access verified!\n\n");
        return 0;
    } else {
        printf("FAILURE: %d tests failed!\n\n", tests_run - tests_passed);
        return 1;
    }
}