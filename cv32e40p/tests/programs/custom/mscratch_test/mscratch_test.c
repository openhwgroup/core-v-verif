// Copyright (c) 2026 Jagadeesh Mummana
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

#include <stdint.h>
#include <stdio.h>

// CSR numbers
#define CSR_MSCRATCH 0x340

static inline void write_csr(unsigned int csr, uint32_t value) {
    asm volatile ("csrw %0, %1" :: "i"(csr), "r"(value));
}

static inline uint32_t read_csr(unsigned int csr) {
    uint32_t value;
    asm volatile ("csrr %0, %1" : "=r"(value) : "i"(csr));
    return value;
}

int main(void) {
    uint32_t test_pattern = 0xA5A5F00D;
    uint32_t readback;

    write_csr(CSR_MSCRATCH, test_pattern);
    readback = read_csr(CSR_MSCRATCH);

    if (readback != test_pattern) {
        printf("MSCRATCH TEST FAILED\n");
        printf("Wrote: 0x%08x Read: 0x%08x\n", test_pattern, readback);
        return 1;
    }

    printf("MSCRATCH TEST PASSED\n");
    printf("Value: 0x%08x\n", readback);

    return 0;
}
