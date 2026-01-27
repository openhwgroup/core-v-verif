// Copyright (c) 2026 Arijit Pal
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

/*
 * Test: mscratch_test
 * Description: Validates full 32-bit R/W access to the mscratch CSR (0x340).
 * Logic: Writes/Reads patterns (Zeros, Ones, Alternating) to detect stuck bits or crosstalk.
 * Returns: 0 on Success; Non-zero index on Failure.
 */
#include <stdint.h>

int main() {
    // Patterns: 0, All-1s, 0x55.., 0xAA.., Random, Sanity
    uint32_t p[] = {0, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA, 0x12345678, 0xDEADBEEF};
    uint32_t v;

    for (int i = 0; i < 6; i++) {
        __asm__ volatile ("csrw 0x340, %0" :: "r"(p[i]));
        __asm__ volatile ("csrr %0, 0x340" : "=r"(v));
        if (v != p[i]) return i + 1;
    }
    return 0;
}
