#include <stdint.h>
#include <stdio.h>

static inline void write_mscratch(uint32_t v) {
    asm volatile ("csrw mscratch, %0" : : "r"(v));
}

static inline uint32_t read_mscratch(void) {
    uint32_t v;
    asm volatile ("csrr %0, mscratch" : "=r"(v));
    return v;
}

int main(void) {

    uint32_t patterns[] = {
        0x00000000,
        0xFFFFFFFF,
        0xAAAAAAAA,
        0x55555555,
        0x12345678,
        0x87654321
    };

    for (int i = 0; i < 6; i++) {
        write_mscratch(patterns[i]);
        uint32_t r = read_mscratch();

        if (r != patterns[i]) {
            printf("FAIL: mscratch mismatch: wrote 0x%08x, read 0x%08x\n",
                    patterns[i], r);
            return 1;   // FAIL
        }
    }

    printf("MSCRATCH TEST IS SUCCESSFUL\n");
    return 0;  // SUCCESS
}
