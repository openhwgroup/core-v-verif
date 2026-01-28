#include <stdint.h>

static inline void write_mscratch(uint32_t value) {
    asm volatile ("csrw mscratch, %0" :: "r"(value));
}

static inline uint32_t read_mscratch(void) {
    uint32_t value;
    asm volatile ("csrr %0, mscratch" : "=r"(value));
    return value;
}

int main(void) {
    volatile uint32_t patterns[] = {
        0x00000000,
        0xFFFFFFFF,
        0xAAAAAAAA,
        0x55555555,
        0x80000000,
        0x7FFFFFFF,
        0x12345678,
        0xDEADBEEF
    };

    for (int i = 0; i < (int)(sizeof(patterns) / sizeof(patterns[0])); i++) {
        write_mscratch(patterns[i]);
        uint32_t readback = read_mscratch();

        if (readback != patterns[i]) {
            // Non-zero exit value → test failure
            return 1;
        }
    }

    // Zero exit value → EXIT SUCCESS
    return 0;
}
