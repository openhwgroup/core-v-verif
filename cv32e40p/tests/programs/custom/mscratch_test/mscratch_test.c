#include <stdint.h>
#include <stdio.h>
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

static int run_test(const char *name, uint32_t value)
{
    printf("[ RUN  ] %s\n", name);
    write_mscratch(value);
    uint32_t rb = read_mscratch();

    if (rb != value) {
        printf("[ FAIL ] %s (wrote 0x%08X, read 0x%08X)\n", name, value, rb);
        return -1;
    }

    printf("[ PASS ] %s\n", name);
    return 0;
}

int main(void)
{
    int failures = 0;

    printf("\n");
    printf("mscratch Bit-Level Access Test\n");
    printf("==============================\n\n");

    failures += run_test("TEST1: all zeros",        0x00000000);
    failures += run_test("TEST2: all ones",         0xFFFFFFFF);
    failures += run_test("TEST3: alternating 1010",0xAAAAAAAA);
    failures += run_test("TEST4: alternating 0101",0x55555555);
    failures += run_test("TEST5: MSB only",         0x80000000);
    failures += run_test("TEST6: LSB only",         0x00000001);

    printf("\n--- Test Results ---\n");

    if (failures == 0) {
        printf("All tests: PASS\n");
        printf("\n[ RESULT ] PASS\n");
        return EXIT_SUCCESS;
    } else {
        printf("Failures detected: %d\n", failures);
        printf("\n[ RESULT ] FAIL\n");
        return EXIT_FAILURE;
    }
}

