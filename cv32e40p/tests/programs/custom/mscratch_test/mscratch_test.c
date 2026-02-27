/*
**
** Copyright 2025 OpenHW Group
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
** Machine Scratch CSR Test: Verify read/write of all 32-bits of the mscratch CSR
**
** This test writes a 32-bit pattern to the mscratch (Machine Scratch) CSR,
** reads it back, and verifies that the value matches. The mscratch register
** is a machine-mode read/write register that can be used to hold temporary
** values. This test validates proper CSR access for all 32-bits.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
    unsigned int test_patterns[] = {
        0x00000000,  // All zeros
        0xFFFFFFFF,  // All ones
        0x55555555,  // Alternating pattern (0101...)
        0xAAAAAAAA,  // Alternating pattern (1010...)
        0x12345678,  // Random pattern 1
        0xDEADBEEF,  // Random pattern 2
        0xCAFEBABE,  // Random pattern 3
        0x80000000   // MSB only
    };
    
    unsigned int readback;
    int err_cnt = 0;
    int i;
    
    printf("\nMachine Scratch CSR (mscratch) Test\n");
    printf("====================================\n\n");
    
    /* Test each pattern */
    for (i = 0; i < 8; i++) {
        unsigned int pattern = test_patterns[i];
        
        printf("Test %d: Writing 0x%08x to mscratch\n", i, pattern);
        
        /* Write pattern to mscratch (CSR 0x340) */
        __asm__ volatile("csrw 0x340, %0" : : "r"(pattern));
        
        /* Read back the value */
        __asm__ volatile("csrr %0, 0x340" : "=r"(readback));
        
        /* Verify the value matches */
        if (readback == pattern) {
            printf("        Read back:  0x%08x [PASS]\n\n", readback);
        } else {
            printf("        Read back:  0x%08x [FAIL]\n", readback);
            printf("        Expected:   0x%08x\n\n", pattern);
            err_cnt++;
        }
    }
    
    /* Print summary */
    printf("====================================\n");
    if (err_cnt == 0) {
        printf("All tests PASSED!\n\n");
        return EXIT_SUCCESS;
    } else {
        printf("ERROR: %d test(s) FAILED!\n\n", err_cnt);
        return EXIT_FAILURE;
    }
}
