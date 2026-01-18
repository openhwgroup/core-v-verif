// Copyright (c) 2026 David Frisbee
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
/*
 * *****************************************************************************
 **
 ** Test the mscratch register for correct read, write, and atomic behavior.
 **
 ** 1. Stress Test: All zeros / all ones (power & fan-out check)
 ** 2. Precision Test: Walking ones (short/bridging check)
 ** 3. Precision Test: Walking zeros (stuck-at check)
 ** 4. Logic Test: Atomic read/write swap (csrrw verification)
 ** 5. Logic Test: Atomic bit manipulation (csrrs/csrrc verification)
 **
 *******************************************************************************
 */

#include <stdio.h>

/* CSR access macros */
#define WRITE_CSR(reg, val) asm volatile("csrw " #reg ", %0" ::"r"((unsigned int)(val)))
#define READ_CSR(reg, val) asm volatile("csrr %0, " #reg : "=r"(val))
#define SWAP_CSR(reg, out, in) asm volatile("csrrw %0, " #reg ", %1" : "=r"(out) : "r"((unsigned int)(in)))
#define SET_CSR_BITS(reg, out, mask) asm volatile("csrrs %0, " #reg ", %1" : "=r"(out) : "r"((unsigned int)(mask)))
#define CLEAR_CSR_BITS(reg, out, mask) asm volatile("csrrc %0, " #reg ", %1" : "=r"(out) : "r"((unsigned int)(mask)))


int main()
{
    unsigned int write_val, read_back, old_val;
    int error_count = 0;

    printf("\n---Beginning test of mscratch register---\n");

    /* Test all zeros */
    printf("Test 1: Stress checks (all zeros/ones)...\n");
    WRITE_CSR(mscratch, 0x00000000);
    READ_CSR(mscratch, read_back);
    if (read_back != 0x00000000) {
        error_count++;
        printf("\tError: Failed all-zeros test! Read %x\n", read_back);
    }

    /* Test all ones */
    WRITE_CSR(mscratch, 0xFFFFFFFF);
    READ_CSR(mscratch, read_back);
    if (read_back != 0xFFFFFFFF) {
        error_count++;
        printf("\tError: Failed all-ones test! Read %x\n", read_back);
    }

    /* Walking ones */
    printf("Test 2: Walking ones...\n");
    for (int i = 0; i < 32; i++) {
        write_val = (1U << i);
        WRITE_CSR(mscratch, write_val);
        READ_CSR(mscratch, read_back);

        if (read_back != write_val) {
            error_count++;
            printf("\tError: Bit %d stuck! Wrote %x, read %x\n", i, write_val, read_back);
        }
    }

    /* Walking zeros */
    printf("Test 3: Walking zeros...\n");
    for (int i = 0; i < 32; i++) {
        write_val = ~(1U << i);
        WRITE_CSR(mscratch, write_val);
        READ_CSR(mscratch, read_back);

        if (read_back != write_val) {
            error_count++;
            printf("\tError: Bit %d stuck! Wrote %x, read %x\n", i, write_val, read_back);
        }
    }

    /* Test atomic swap logic */
    printf("Test 4: Atomic swap logic (csrrw)...\n");

    unsigned int pattern_a = 0xAAAAAAAA;
    unsigned int pattern_b = 0x55555555;

    WRITE_CSR(mscratch, pattern_a);
    SWAP_CSR(mscratch, old_val, pattern_b);

    /* Verify we got the OLD value back correctly */
    if (old_val != pattern_a) {
        error_count++;
        printf("\tError: Swap read failed! Expected %x, got %x\n", pattern_a, old_val);
    }
    /* Verify the NEW value was written */
    READ_CSR(mscratch, read_back);
    if (read_back != pattern_b) {
        error_count++;
        printf("\tError: Swap write failed! Expected %x, got %x\n", pattern_b, read_back);
    }

    /* Atomic bit manipulation */
    printf("Test 5: Atomic bit manipulation (csrrs/csrrc)...\n");
    WRITE_CSR(mscratch, 0);

    /* Test atomic set (csrrs) */
    unsigned int set_mask = 0xF;
    SET_CSR_BITS(mscratch, old_val, set_mask);

    if (old_val != 0) {
        error_count++;
        printf("\tError: CSRRS read wrong old value! Expected 0, got %x\n", old_val);
    }
    READ_CSR(mscratch, read_back);
    if (read_back != 0xF) {
        error_count++;
        printf("\tError: CSRRS failed to set bits! Expected 0xF, got %x\n", read_back);
    }

    /* Test atomic clear (csrrc) */
    unsigned int clear_mask = 0x1;
    CLEAR_CSR_BITS(mscratch, old_val, clear_mask);

    if (old_val != 0xF) {
        error_count++;
        printf("\tError: CSRRC read wrong old value! Expected 0xF, got %x\n", old_val);
    }
    READ_CSR(mscratch, read_back);
    if (read_back != 0xE) {
        error_count++;
        printf("\tError: CSRRC failed to clear bit! Expected 0xE, got %x\n", read_back);
    }

    /* Cleanup and exit */
    WRITE_CSR(mscratch, 0);
    printf("Finished. Total errors: %d\n", error_count);
    return error_count;
}
