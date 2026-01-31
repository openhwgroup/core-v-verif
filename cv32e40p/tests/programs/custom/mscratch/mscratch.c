// Copyright (c) <year> <organization>
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

// CSR access functions
static inline void write_mscratch(uint32_t val) {
    __asm__ volatile ("csrw 0x340, %0" :: "r"(val));
}

static inline uint32_t read_mscratch(void) {
    uint32_t val;
    __asm__ volatile ("csrr %0, 0x340" : "=r"(val));
    return val;
}

static inline uint32_t swap_mscratch(uint32_t val) {
    uint32_t old;
    __asm__ volatile ("csrrw %0, 0x340, %1" : "=r"(old) : "r"(val));
    return old;
}

static inline uint32_t set_mscratch_bits(uint32_t mask) {
    uint32_t old;
    __asm__ volatile ("csrrs %0, 0x340, %1" : "=r"(old) : "r"(mask));
    return old;
}

static inline uint32_t clear_mscratch_bits(uint32_t mask) {
    uint32_t old;
    __asm__ volatile ("csrrc %0, 0x340, %1" : "=r"(old) : "r"(mask));
    return old;
}

int main(void) {
    uint32_t w, r, old;
    int test_count = 0;

    printf("=== mscratch CSR Comprehensive Test ===\n\n");

    /* Test 1: All zeros */
    printf("Test %d: All zeros\n", ++test_count);
    write_mscratch(0x00000000);
    if (read_mscratch() != 0x00000000) {
        printf("FAILED\n");
        return EXIT_FAILURE;
    }

    /* Test 2: All ones */
    printf("Test %d: All ones\n", ++test_count);
    write_mscratch(0xFFFFFFFF);
    if (read_mscratch() != 0xFFFFFFFF) {
        printf("FAILED\n");
        return EXIT_FAILURE;
    }

    /* Test 3: Walking-1s */
    printf("Test %d: Walking-1s (32 patterns)\n", ++test_count);
    for (int i = 0; i < 32; i++) {
        w = (1u << i);
        write_mscratch(w);
        r = read_mscratch();
        if (r != w) {
            printf("FAILED at bit %d\n", i);
            return EXIT_FAILURE;
        }
    }

    /* Test 4: Walking-0s */
    printf("Test %d: Walking-0s (32 patterns)\n", ++test_count);
    for (int i = 0; i < 32; i++) {
        w = ~(1u << i);
        write_mscratch(w);
        r = read_mscratch();
        if (r != w) {
            printf("FAILED at bit %d\n", i);
            return EXIT_FAILURE;
        }
    }

    /* Test 5: Atomic swap */
    printf("Test %d: Atomic swap (csrrw)\n", ++test_count);
    write_mscratch(0x12345678);
    old = swap_mscratch(0xA5A55A5A);
    if (old != 0x12345678 || read_mscratch() != 0xA5A55A5A) {
        printf("FAILED\n");
        return EXIT_FAILURE;
    }

    /* Test 6: Checkerboard patterns */
    printf("Test %d: Checkerboard patterns\n", ++test_count);
    uint32_t checkers[] = {0xAAAAAAAA, 0x55555555};
    for (int i = 0; i < 2; i++) {
        write_mscratch(checkers[i]);
        if (read_mscratch() != checkers[i]) {
            printf("FAILED\n");
            return EXIT_FAILURE;
        }
    }

    /* Test 7: Bit-set operations */
    printf("Test %d: Bit-set operations (csrrs)\n", ++test_count);
    write_mscratch(0x00000000);
    set_mscratch_bits(0x0000000F);
    if (read_mscratch() != 0x0000000F) {
        printf("FAILED\n");
        return EXIT_FAILURE;
    }
    set_mscratch_bits(0xF0000000);
    if (read_mscratch() != 0xF000000F) {
        printf("FAILED\n");
        return EXIT_FAILURE;
    }

    /* Test 8: Bit-clear operations */
    printf("Test %d: Bit-clear operations (csrrc)\n", ++test_count);
    clear_mscratch_bits(0x0000000F);
    if (read_mscratch() != 0xF0000000) {
        printf("FAILED\n");
        return EXIT_FAILURE;
    }
    clear_mscratch_bits(0xF0000000);
    if (read_mscratch() != 0x00000000) {
        printf("FAILED\n");
        return EXIT_FAILURE;
    }

    /* Test 9: State retention */
    printf("Test %d: State retention across reads\n", ++test_count);
    write_mscratch(0xDEADBEEF);
    for (int i = 0; i < 10; i++) {
        if (read_mscratch() != 0xDEADBEEF) {
            printf("FAILED at read %d\n", i);
            return EXIT_FAILURE;
        }
    }

    printf("\n=== ALL TESTS PASSED ===\n");
    printf("Total tests: %d\n", test_count);
    
    return EXIT_SUCCESS;
}
