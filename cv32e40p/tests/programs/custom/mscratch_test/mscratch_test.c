// Copyright (c) 2026 Your Name
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#include <stdio.h>
#include <stdlib.h>

int main() {
    unsigned int write_val = 0xFFFFFFFF; //Testing all 32 bits
    unsigned int read_val = 0;

    // Writing to mscratch (0x340)
    asm volatile ("csrw mscratch, %0" : : "r"(write_val));

    // Reading from mscratch
    asm volatile ("csrr %0, mscratch" : "=r"(read_val));

    if (read_val == write_val) {
        printf("mscratch test PASSED: Read 0x%08x\n", read_val);
        return 0; 
    } else {
        printf("mscratch test FAILED: Wrote 0x%08x, Read 0x%08x\n", write_val, read_val);
        return 1;
    }
}
