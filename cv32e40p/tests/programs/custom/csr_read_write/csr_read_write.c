/*
**
** Copyright (c) 2026 FallenDeity
** 
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
** 
**     https://solderpad.org/licenses/
** 
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
** 
*******************************************************************************
**
** CSR read and write instruction test: Write a value to mscratch CSR 
**                       and read it back to verify correct operation.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

// Helper macro to read/write CSR, 0x340 is the mscratch CSR
#define test_csr_pattern(val) ({ \
    unsigned int read_back; \
    __asm__ volatile ("csrw mscratch, %0" : : "r"(val)); \
    __asm__ volatile ("csrr %0, mscratch" : "=r"(read_back)); \
    read_back; \
})

typedef struct {
    int passed;
    int total;
} TestResult;

int check_csr_value(unsigned int expected, unsigned int actual, const char *desc) {
    if (actual != expected) {
        printf("FAILED %s: Expected 0x%08X, Got 0x%08X\n", desc, expected, actual);
        return 0;
    }
    printf("PASSED %s: 0x%08X\n", desc, expected);
    return 1;
}

TestResult static_pattern_test(void) {
    TestResult result = {0, 0};
    unsigned int patterns[] = {
        0xDEADBEEF, // Common test pattern
        0xFFFFFFFF, // All bits high
        0x00000000, // All bits low
        0x55555555, // Alternating (0101...)
        0xAAAAAAAA, // Alternating (1010...)
        0x12345678  // Random distribution
    };
    int num_patterns = sizeof(patterns) / sizeof(patterns[0]);

    for (int i = 0; i < num_patterns; i++) {
        unsigned int read_val = test_csr_pattern(patterns[i]);
        result.total++;
        result.passed += check_csr_value(patterns[i], read_val, "pattern");
    }
    return result;
}

TestResult walking_bit_test(int is_walking_one) {
    TestResult result = {0, 0};
    char desc[32];
    
    for (int i = 0; i < 32; i++) {
        unsigned int write_val = is_walking_one ? (1U << i) : ~(1U << i);
        unsigned int read_val = test_csr_pattern(write_val);
        result.total++;
        
        snprintf(desc, sizeof(desc), "bit %d", i);
        result.passed += check_csr_value(write_val, read_val, desc);
    }
    return result;
}

int main(int argc, char *argv[]) {
    TestResult result;
    int pass_count = 0;
    int total_tests = 0;

    printf("\n=== Static Pattern Tests ===\n");
    result = static_pattern_test();
    pass_count += result.passed;
    total_tests += result.total;

    printf("\n=== Walking 1 Test (proves each bit can be set) ===\n");
    result = walking_bit_test(1);
    pass_count += result.passed;
    total_tests += result.total;
    
    printf("\n=== Walking 0 Test (proves each bit can be cleared) ===\n");
    result = walking_bit_test(0);
    pass_count += result.passed;
    total_tests += result.total;

    printf("\n=== Test Summary ===\n");
    if (pass_count == total_tests) {
        printf("All %d CSR Read/Write tests PASSED.\n", total_tests);
        return EXIT_SUCCESS;
    } else {
        printf("%d out of %d CSR Read/Write tests PASSED.\n", pass_count, total_tests);
        return EXIT_FAILURE;
    }
}