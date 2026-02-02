// Copyright (c) 2026 Sanjay Chitroda
// SPDX-License-Identifier:Apache-2.0 WITH SHL-2.1

#include <stdint.h>

static inline void write_mscratch(uint32_t val)
{
    asm volatile ("csrw mscratch, %0" :: "r"(val));
}

static inline uint32_t read_mscratch(void)
{
    uint32_t val;
    asm volatile ("csrr %0, mscratch" : "=r"(val));
    return val;
}

int main(void)
{
    uint32_t test = 0xA5A5F00D;
    write_mscratch(test);

    uint32_t readback = read_mscratch();
    if (readback != test)
        return 1;

    return 0;
}

