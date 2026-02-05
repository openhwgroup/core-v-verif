#include <stdio.h>
#include <stdint.h>

int main(void)
{
    // Test vectors
    static const uint32_t patterns[] = {
        0x00000000, 0xFFFFFFFF, // Stuck-at tests
        0xAAAAAAAA, 0x55555555, // Checkerboard 
        0x600D1DEA, 0x12345678, // Unique 
        0xA5A5A5A5, 0x5A5A5A5A  // toggling
    };

    uint32_t read_val;
    int i, errors = 0;
    int num_tests = (int)(sizeof(patterns) / sizeof(patterns[0]));

    printf("\n!! mscratch verification !!\n");

    for (i = 0; i < num_tests; i++) {
        uint32_t val = patterns[i];
        
        __asm__ __volatile__ ("csrw mscratch, %0" : : "r"(val));
        __asm__ __volatile__ ("csrr %0, mscratch" : "=r"(read_val));

        if (read_val == val) {
            printf("[PASS] Vector %d: Wrote 0x%08x | Read 0x%08x\n", i, val, read_val);
        } else {
            printf("[FAIL] Vector %d: Wrote 0x%08x | Read 0x%08x (MISMATCH)\n", i, val, read_val);
            errors++;
        }
    }

    // Error reporting
    if (errors == 0) {
        printf("\nSUCCESS: All %d test vectors verified with 100%% integrity.\n", num_tests);
        return 0;
    } else {
        printf("\nFAILURE: %d out of %d patterns failed verification.\n", errors, num_tests);
        return 1;
    }
}
