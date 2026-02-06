// Copyright (c) 2026 OpenHW Group
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Read/Write access test to all 32-bits of the mscratch CSR.
//

#include <stdio.h>
#include <stdlib.h>

#define CSR_MSCRATCH 0x340

/* Helper macros for CSR access */
#define CSR_READ(csr, var)  __asm__ volatile("csrr %0, " #csr : "=r"(var))
#define CSR_WRITE(csr, val) __asm__ volatile("csrw " #csr ", %0" :: "r"(val))

/* Test pattern structure */
typedef struct {
    unsigned int value;
    const char *name;
} test_pattern_t;

int main(int argc, char *argv[])
{
    unsigned int original_value;
    unsigned int readback;
    int test_passed = 1;
    int test_count = 0;
    int failure_count = 0;

    /* Save original mscratch value to restore later */
    CSR_READ(mscratch, original_value);
    printf("mscratch Bit-Level Access Test\n");
    printf("================================\n");
    printf("Original mscratch value: 0x%08x\n\n", original_value);

    /* Comprehensive test patterns */
    test_pattern_t patterns[] = {
        {0x00000000, "All zeros"},
        {0xFFFFFFFF, "All ones"},
        {0x55555555, "Alternating 01 (0x55555555)"},
        {0xAAAAAAAA, "Alternating 10 (0xAAAAAAAA)"},
        {0x0000FFFF, "Lower 16 bits set"},
        {0xFFFF0000, "Upper 16 bits set"},
        {0x00FF00FF, "Byte pattern 1"},
        {0xFF00FF00, "Byte pattern 2"},
        {0x0F0F0F0F, "Nibble pattern 1"},
        {0xF0F0F0F0, "Nibble pattern 2"},
        {0x33333333, "2-bit pattern 1"},
        {0xCCCCCCCC, "2-bit pattern 2"},
        {0x00000001, "Single bit 0"},
        {0x80000000, "Single bit 31"},
    };

    /* 1. Pattern-based tests */
    printf("Running pattern-based tests...\n");
    for (unsigned int i = 0; i < sizeof(patterns)/sizeof(patterns[0]); i++) {
        test_count++;
        CSR_WRITE(mscratch, patterns[i].value);
        CSR_READ(mscratch, readback);

        if (readback != patterns[i].value) {
            printf("FAIL: %s\n", patterns[i].name);
            printf("Wrote: 0x%08x  Read: 0x%08x\n", patterns[i].value, readback);
            test_passed = 0;
            failure_count++;
        } else {
            printf("PASS: %s\n", patterns[i].name);
        }
    }

    /* 2. Walking 1's test (detects stuck-at-0 bits) */
    printf("\nRunning walking 1's test (detect stuck-at-0 bits)...\n");
    for (unsigned int bit = 0; bit < 32; bit++) {
        unsigned int test_val = (1U << bit);
        test_count++;
        CSR_WRITE(mscratch, test_val);
        CSR_READ(mscratch, readback);

        if (readback != test_val) {
            printf("FAIL: Bit %2u stuck-at fault\n", bit);
            printf("Wrote: 0x%08x  Read: 0x%08x\n", test_val, readback);
            test_passed = 0;
            failure_count++;
        }
    }
    if (failure_count == 0) {
        printf("All 32 bits can be set to 1 independently\n");
    }

    /* 3. Walking 0's test (detects stuck-at-1 bits) */
    printf("\nRunning walking 0's test (detect stuck-at-1 bits)...\n");
    for (unsigned int bit = 0; bit < 32; bit++) {
        unsigned int test_val = ~(1U << bit);
        test_count++;
        CSR_WRITE(mscratch, test_val);
        CSR_READ(mscratch, readback);

        if (readback != test_val) {
            printf("FAIL: Bit %2u stuck-at fault\n", bit);
            printf("Wrote: 0x%08x  Read: 0x%08x\n", test_val, readback);
            test_passed = 0;
            failure_count++;
        }
    }
    if (failure_count == 0) {
        printf("All 32 bits can be set to 0 independently\n");
    }

    /* 4. Bit independence test (detects coupling/aliasing) */
    printf("\nRunning bit independence test (detect coupling)...\n");
    CSR_WRITE(mscratch, 0x00000000);
    CSR_READ(mscratch, readback);
    if (readback != 0x00000000) {
        printf("FAIL: Cannot clear all bits before independence test\n");
        test_passed = 0;
        failure_count++;
    } else {
        unsigned int cumulative = 0;
        int coupling_detected = 0;
        for (unsigned int bit = 0; bit < 32; bit++) {
            unsigned int expected = cumulative | (1U << bit);
            CSR_WRITE(mscratch, expected);
            CSR_READ(mscratch, readback);
            test_count++;

            if (readback != expected) {
                printf("FAIL: Bit coupling detected at bit %2u\n", bit);
                printf("Expected: 0x%08x  Read: 0x%08x\n", expected, readback);
                test_passed = 0;
                failure_count++;
                coupling_detected = 1;
                break;
            }
            cumulative = expected;
        }
        if (!coupling_detected) {
            printf("No bit coupling detected (all bits independent)\n");
        }
    }

    /* 5. Restoring original mscratch value test */
    CSR_WRITE(mscratch, original_value);
    CSR_READ(mscratch, readback);
    if (readback != original_value) {
        printf("\nFAIL: Could not fully restore original mscratch value!\n");
        printf("    Original: 0x%08x  Restored: 0x%08x\n", original_value, readback);
	test_passed = 0;
        failure_count++;
    }

    /* Final summary */
    printf("\n================================\n");
    printf("TEST SUMMARY\n");
    printf("================================\n");
    printf("Total tests executed: %d\n", test_count);
    printf("Failures detected:    %d\n", failure_count);

    if (test_passed && failure_count == 0) {
        printf("\nALL TESTS PASSED\n");
        printf("   Full 32-bit read/write access to mscratch verified!\n");
        return EXIT_SUCCESS;
    } else {
        printf("\nTEST FAILED\n");
        printf("   mscratch does NOT have full 32-bit access.\n");
        printf("   Check for hardware defects or CSR implementation issues.\n");
        return EXIT_FAILURE;
    }
}
