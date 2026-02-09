#include <stdint.h>
#include <stdio.h>

static inline void write_csr(uint32_t val) {
    asm volatile ("csrw mscratch, %0" :: "r"(val));
}

static inline uint32_t read_csr(void) {
    uint32_t val;
    asm volatile ("csrr %0, mscratch" : "=r"(val));
    return val;
}

int main() {
    uint32_t patterns[] = {
        0x00000000,
        0xFFFFFFFF,
        0xA5A5A5A5,
        0x5A5A5A5A
    };

    printf("Starting mscratch test...\n");

    for (int i = 0; i < 4; i++) {
        write_csr(patterns[i]);
        uint32_t r = read_csr();

        printf("Write: 0x%08X Read: 0x%08X\n",
               patterns[i], r);

        if (r != patterns[i]) {
            printf("FAIL at index %d\n", i);
            while (1);   // stop here
        }
    }

    printf("MSCRATCH TEST PASSED\n");

    return 0;
}

