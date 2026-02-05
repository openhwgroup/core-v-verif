#include <stdint.h>
#include <stdlib.h>

#define MSCRATCH_CSR 0x340

static inline void write_mscratch(uint32_t value)
{
    asm volatile ("csrw %0, %1" :: "i"(MSCRATCH_CSR), "r"(value));
}

static inline uint32_t read_mscratch(void)
{
    uint32_t value;
    asm volatile ("csrr %0, %1" : "=r"(value) : "i"(MSCRATCH_CSR));
    return value;
}

static inline int check(uint32_t value)
{
    write_mscratch(value);
    return (read_mscratch() == value);
}

int main(void)
{
    if (!check(0x00000000)) return EXIT_FAILURE;
    if (!check(0xFFFFFFFF)) return EXIT_FAILURE;
    if (!check(0xAAAAAAAA)) return EXIT_FAILURE;
    if (!check(0x55555555)) return EXIT_FAILURE;
    if (!check(0x80000000)) return EXIT_FAILURE;
    if (!check(0x00000001)) return EXIT_FAILURE;

    return EXIT_SUCCESS;
}

