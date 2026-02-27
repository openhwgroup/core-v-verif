/*
** Copyright (c) 2026 Nikunj
** SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
*******************************************************************************
**
** mscratch CSR test for CV32E40P core.
**
** This test verifies that the mscratch CSR (Machine Scratch Register) has
** full 32-bit read/write access. The mscratch register is defined in the
** RISC-V Privileged Specification as a general-purpose scratch register
** available to machine-mode software.
**
** Test strategy:
** 1. Write various patterns to mscratch (all 0s, all 1s, alternating, walking)
** 2. Read back the value and verify it matches what was written
** 3. Test all 32 bits individually using walking bit patterns
** 4. Test common boundary values (0x00000000, 0xFFFFFFFF, 0x80000000, etc.)
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

#define MSCRATCH_CSR 0x340

// Helper function to write to mscratch CSR
static inline void write_mscratch(unsigned int val) {
    __asm__ volatile("csrw %0, %1" : : "i"(MSCRATCH_CSR), "r"(val));
}

// Helper function to read from mscratch CSR
static inline unsigned int read_mscratch(void) {
    unsigned int val;
    __asm__ volatile("csrr %0, %1" : "=r"(val) : "i"(MSCRATCH_CSR));
    return val;
}

// Test a specific pattern
int test_pattern(unsigned int pattern, const char* description) {
    unsigned int readback;
    
    write_mscratch(pattern);
    readback = read_mscratch();
    
    if (readback != pattern) {
        printf("\tERROR: %s failed!\n", description);
        printf("\t  Expected: 0x%08x\n", pattern);
        printf("\t  Got:      0x%08x\n", readback);
        return 1;
    }
    
    printf("\t✓ %s: 0x%08x\n", description, readback);
    return 0;
}

int main(int argc, char *argv[])
{
    int errors = 0;
    unsigned int i;
    
    printf("\n=== CV32E40P MSCRATCH CSR Test ===\n");
    printf("Testing Machine Scratch Register (CSR 0x%03x)\n\n", MSCRATCH_CSR);
    
    // Test 1: All zeros
    printf("Test 1: Basic patterns\n");
    errors += test_pattern(0x00000000, "All zeros");
    
    // Test 2: All ones
    errors += test_pattern(0xFFFFFFFF, "All ones");
    
    // Test 3: Alternating patterns
    errors += test_pattern(0xAAAAAAAA, "Alternating 1010");
    errors += test_pattern(0x55555555, "Alternating 0101");
    
    // Test 4: Byte boundaries
    errors += test_pattern(0xFF00FF00, "Byte pattern 1");
    errors += test_pattern(0x00FF00FF, "Byte pattern 2");
    
    printf("\nTest 2: Walking 1-bit (testing all 32 bits individually)\n");
    
    // Test 5: Walking 1-bit pattern (test each bit individually)
    for (i = 0; i < 32; i++) {
        unsigned int pattern = (1U << i);
        char desc[64];
        snprintf(desc, sizeof(desc), "Walking 1-bit [bit %2u]", i);
        errors += test_pattern(pattern, desc);
    }
    
    printf("\nTest 3: Walking 0-bit (inverse test)\n");
    
    // Test 6: Walking 0-bit pattern (all 1s except one bit)
    for (i = 0; i < 32; i++) {
        unsigned int pattern = ~(1U << i);
        char desc[64];
        snprintf(desc, sizeof(desc), "Walking 0-bit [bit %2u]", i);
        errors += test_pattern(pattern, desc);
    }
    
    printf("\nTest 4: Boundary values\n");
    
    // Test 7: Various boundary values
    errors += test_pattern(0x80000000, "MSB set");
    errors += test_pattern(0x00000001, "LSB set");
    errors += test_pattern(0x7FFFFFFF, "Max positive (signed)");
    errors += test_pattern(0x80000001, "Min negative + 1");
    errors += test_pattern(0x12345678, "Random pattern 1");
    errors += test_pattern(0xDEADBEEF, "Random pattern 2");
    errors += test_pattern(0xCAFEBABE, "Random pattern 3");
    
    // Test 8: Verify no side effects - write and read multiple times
    printf("\nTest 5: Persistence check (no side effects)\n");
    write_mscratch(0xA5A5A5A5);
    for (i = 0; i < 10; i++) {
        unsigned int readback = read_mscratch();
        if (readback != 0xA5A5A5A5) {
            printf("\tERROR: Persistence test failed on read %u!\n", i);
            printf("\t  Expected: 0xA5A5A5A5\n");
            printf("\t  Got:      0x%08x\n", readback);
            errors++;
        }
    }
    if (errors == 0) {
        printf("\t✓ Value persists across multiple reads\n");
    }
    
    // Test 9: Clear at end
    printf("\nTest 6: Final cleanup\n");
    errors += test_pattern(0x00000000, "Clear to zero");
    
    // Summary
    printf("\n=== Test Summary ===\n");
    if (errors == 0) {
        printf("ALL TESTS PASSED!\n");
        printf("The mscratch CSR has full 32-bit read/write access.\n");
        printf("Total patterns tested: %d\n", 32 + 32 + 14 + 10); // walking bits + walking zeros + boundaries + persistence
        return EXIT_SUCCESS;
    } else {
        printf("TEST FAILED with %d error(s)!\n", errors);
        return EXIT_FAILURE;
    }
}
