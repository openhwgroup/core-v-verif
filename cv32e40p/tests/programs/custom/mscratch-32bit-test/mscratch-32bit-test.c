#include <stdio.h>
#include <stdint.h>

int main(void)
{
    static const uint32_t patterns[] = {
        0x00000000, 0xFFFFFFFF,
        0xAAAAAAAA, 0x55555555,
        0xDEADBEEF, 0xCAFEBABE,
        0x12345678, 0x87654321
    };

    uint32_t read_val;
    int i, errors = 0;

    printf("\n=== Full 32-bit mscratch CSR (0x340) write/read test ===\n");

    for (i = 0; i < (int)(sizeof(patterns)/sizeof(patterns[0])); i++) {
        uint32_t val = patterns[i];
        asm volatile ("csrw mscratch, %0" : : "r"(val));
        asm volatile ("csrr %0, mscratch" : "=r"(read_val));
        if (read_val == val) {
            printf("PASS 0x%08x -> 0x%08x\n", val, read_val);
        } else {
            printf("FAIL 0x%08x -> 0x%08x\n", val, read_val);
            errors++;
        }
    }

    if (errors == 0) {
        printf("\nSUCCESS: All 32-bit patterns verified!\n");
        return 0;
    } else {
        printf("\nFAILED: %d errors\n", errors);
        return 1;
    }
}
