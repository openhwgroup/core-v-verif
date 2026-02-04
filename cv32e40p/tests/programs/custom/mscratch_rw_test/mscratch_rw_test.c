// Copyright (c) 2026 Nai-Chen(Simone) Cheng
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
    int passed = 0;
    int total = 0;
    unsigned int all_zero_wval, all_zero_rval;
    unsigned int all_one_wval, all_one_rval;
    unsigned int even_bit_wval, even_bit_rval;
    unsigned int odd_bit_rval, odd_bit_wval;
    unsigned int random_wval, random_rval;

    printf("\nMSCRATCH CSR Read/Write test: Testing all 32 bits of MSCRATCH (CSR 0x340)\n");

    all_zero_wval = 0x00000000;
    __asm__ volatile("csrw 0x340, %0" : : "r"(all_zero_wval));
    __asm__ volatile("csrr %0, 0x340" : "=r"(all_zero_rval));
    if (all_zero_wval != all_zero_rval) {
        printf("FAIL: All zeros\n");
        printf("Expected: 0x%08x\n", all_zero_wval);
        printf("Got:      0x%08x\n", all_zero_rval);
        printf("Diff:     0x%08x\n\n", all_zero_wval ^ all_zero_rval);
    } else {
        printf("PASS: All zeros\n");
        passed++;
    }
    total++;

    all_one_wval = 0xFFFFFFFF;
    __asm__ volatile("csrw 0x340, %0" : : "r"(all_one_wval));
    __asm__ volatile("csrr %0, 0x340" : "=r"(all_one_rval));
    if (all_one_wval != all_one_rval) {
        printf("FAIL: All ones\n");
        printf("Expected: 0x%08x\n", all_one_wval);
        printf("Got:      0x%08x\n", all_one_rval);
        printf("Diff:     0x%08x\n\n", all_one_wval ^ all_one_rval);
    } else {
        printf("PASS: All ones\n");
        passed++;
    }
    total++;

    even_bit_wval = 0xAAAAAAAA;
    __asm__ volatile("csrw 0x340, %0" : : "r"(even_bit_wval));
    __asm__ volatile("csrr %0, 0x340" : "=r"(even_bit_rval));
    if (even_bit_wval != even_bit_rval) {
        printf("FAIL: Alternating bits (even)\n");
        printf("Expected: 0x%08x\n", even_bit_wval);
        printf("Got:      0x%08x\n", even_bit_rval);
        printf("Diff:     0x%08x\n\n", even_bit_wval ^ even_bit_rval);
    } else {
        printf("PASS: Alternating bits (even)\n");
        passed++;
    }
    total++;

    odd_bit_wval = 0x55555555;
    __asm__ volatile("csrw 0x340, %0" : : "r"(odd_bit_wval));
    __asm__ volatile("csrr %0, 0x340" : "=r"(odd_bit_rval));
    if (odd_bit_wval != odd_bit_rval) {
        printf("FAIL: Alternating bits (odd)\n");
        printf("Expected: 0x%08x\n", odd_bit_wval);
        printf("Got:      0x%08x\n", odd_bit_rval);
        printf("Diff:     0x%08x\n\n", odd_bit_wval ^ odd_bit_rval);
    } else {
        printf("PASS: Alternating bits (odd)\n");
        passed++;
    }
    total++;

    random_wval = 0x12345678;
    __asm__ volatile("csrw 0x340, %0" : : "r"(random_wval));
    __asm__ volatile("csrr %0, 0x340" : "=r"(random_rval));
    if (random_wval != random_rval) {
        printf("FAIL: Random bits\n");
        printf("Expected: 0x%08x\n", random_wval);
        printf("Got:      0x%08x\n", random_rval);
        printf("Diff:     0x%08x\n\n", random_wval ^ random_rval);
    } else {
        printf("PASS: Random bits\n");
        passed++;
    }
    total++;

    printf("Passed: %d/%d\n", passed, total);

    if (passed == total) {
        return EXIT_SUCCESS;
    } else {
        return EXIT_FAILURE;
    }
}
