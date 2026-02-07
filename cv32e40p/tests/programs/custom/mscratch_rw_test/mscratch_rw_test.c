// Copyright (c) 2026 danteantu5@gmail.com
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

#include <stdint.h>

int main(int argc, char *argv[])
{
    // Simplified test that reads the current value of mscratch, flips it
    // writes the new flipped value, and checks if the write operation was successful or not.
    unsigned int initial_value;
    asm volatile("csrr %0, 0x340" : "=r"(initial_value));
    unsigned int target = ~initial_value;
    asm volatile("csrw 0x340, %0" :: "r"(target));
    unsigned int current_value;
    asm volatile("csrr %0, 0x340" : "=r"(current_value));
    if(current_value == target) {
      printf("Successfuly read/written mscratch reg\n");
    }
    else {
      printf("Error trying to read/write mscratch reg\n");
    }
}
