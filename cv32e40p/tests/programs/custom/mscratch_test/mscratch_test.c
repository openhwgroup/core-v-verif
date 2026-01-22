// Copyright (c) 2026 Amit Matth
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

#include <stdio.h>
#include <stdlib.h>

int main() {
    unsigned int read_val;
    unsigned int old_val;
    int fail_count = 0;

    printf("\n=== Starting Comprehensive mscratch CSR Test ===\n");

    // -------------------------------------------------------------------------
    // Test 1: Basic Patterns (Boundary values and alternating bits)
    // -------------------------------------------------------------------------
    printf("[1/4] Testing Basic Patterns...\n");
    unsigned int patterns[] = {
        0x00000000, // All Zeros
        0xFFFFFFFF, // All Ones
        0xAAAAAAAA, // Alternating 1010...
        0x55555555, // Alternating 0101...
        0xDEADBEEF, // Random pattern
        0xCAFEBABE  // Random pattern
    };

    for (int i = 0; i < 6; i++) {
        unsigned int pat = patterns[i];
        
        // Write pattern
        asm volatile ("csrw mscratch, %0" : : "r"(pat));
        
        // Read back
        asm volatile ("csrr %0, mscratch" : "=r"(read_val));

        if (read_val != pat) {
            printf("  [FAIL] Wrote 0x%08x, Read 0x%08x\n", pat, read_val);
            fail_count++;
        }
    }

    // -------------------------------------------------------------------------
    // Test 2: Walking "One" (Testing Stuck-at-0 faults)
    // -------------------------------------------------------------------------
    printf("[2/4] Testing Walking '1' (0 -> 31)...\n");
    for (int i = 0; i < 32; i++) {
        unsigned int pat = (1u << i);
        
        asm volatile ("csrw mscratch, %0" : : "r"(pat));
        asm volatile ("csrr %0, mscratch" : "=r"(read_val));

        if (read_val != pat) {
            printf("  [FAIL] Bit %d: Wrote 0x%08x, Read 0x%08x\n", i, pat, read_val);
            fail_count++;
        }
    }

    // -------------------------------------------------------------------------
    // Test 3: Walking "Zero" (Testing Stuck-at-1 faults)
    // -------------------------------------------------------------------------
    printf("[3/4] Testing Walking '0' (0 -> 31)...\n");
    for (int i = 0; i < 32; i++) {
        unsigned int pat = ~(1u << i);
        
        asm volatile ("csrw mscratch, %0" : : "r"(pat));
        asm volatile ("csrr %0, mscratch" : "=r"(read_val));

        if (read_val != pat) {
            printf("  [FAIL] Bit %d: Wrote 0x%08x, Read 0x%08x\n", i, pat, read_val);
            fail_count++;
        }
    }

    // -------------------------------------------------------------------------
    // Test 4: Atomic Read-Modify-Write Operations (CSRRS, CSRRC)
    // -------------------------------------------------------------------------
    printf("[4/4] Testing Atomic Operations (CSRRS/CSRRC)...\n");
    
    // Initial Setup: mscratch = 0x0000FFFF
    unsigned int init_val = 0x0000FFFF;
    asm volatile ("csrw mscratch, %0" : : "r"(init_val));

    // A. Test CSRRS (Read and Set Bits)
    // Set upper 16 bits (0xFFFF0000). Expected result: 0xFFFFFFFF.
    // CSRRS returns the OLD value.
    unsigned int set_mask = 0xFFFF0000;
    asm volatile ("csrrs %0, mscratch, %1" : "=r"(old_val) : "r"(set_mask));
    
    // Check returned old value
    if (old_val != 0x0000FFFF) {
        printf("  [FAIL] CSRRS Old Value: Expected 0x0000FFFF, Got 0x%08x\n", old_val);
        fail_count++;
    }
    
    // Check new value in register
    asm volatile ("csrr %0, mscratch" : "=r"(read_val));
    if (read_val != 0xFFFFFFFF) {
        printf("  [FAIL] CSRRS New Value: Expected 0xFFFFFFFF, Got 0x%08x\n", read_val);
        fail_count++;
    }

    // B. Test CSRRC (Read and Clear Bits)
    // Clear lower 8 bits (0x000000FF). Current is 0xFFFFFFFF.
    // Expected result: 0xFFFFFF00.
    unsigned int clr_mask = 0x000000FF;
    asm volatile ("csrrc %0, mscratch, %1" : "=r"(old_val) : "r"(clr_mask));

    if (old_val != 0xFFFFFFFF) {
         printf("  [FAIL] CSRRC Old Value: Expected 0xFFFFFFFF, Got 0x%08x\n", old_val);
         fail_count++;
    }

    asm volatile ("csrr %0, mscratch" : "=r"(read_val));
    if (read_val != 0xFFFFFF00) {
        printf("  [FAIL] CSRRC New Value: Expected 0xFFFFFF00, Got 0x%08x\n", read_val);
        fail_count++;
    }

    // -------------------------------------------------------------------------
    // Conclusion
    // -------------------------------------------------------------------------
    if (fail_count == 0) {
        printf("\n=== SUCCESS: All mscratch CSR tests passed! ===\n");
        return EXIT_SUCCESS;
    } else {
        printf("\n=== FAILURE: %d tests failed! ===\n", fail_count);
        return EXIT_FAILURE;
    }
}
