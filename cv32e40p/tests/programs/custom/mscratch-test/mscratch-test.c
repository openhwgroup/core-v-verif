#include <stdio.h>
#include <stdint.h>

static inline void write_csr(unsigned int csr, uint32_t value) {
    asm volatile ("csrw %0, %1" :: "i"(csr), "r"(value));
}

static inline uint32_t read_csr(unsigned int csr) {
    uint32_t value;
    asm volatile ("csrr %0, %1" : "=r"(value) : "i"(csr));
    return value;
}

#define MSCRATCH 0x340

int main() {
    uint32_t val;

    printf("=== MSCRATCH CSR TEST ===\n");

    write_csr(MSCRATCH, 0x00000000);
    val = read_csr(MSCRATCH);
    printf("Test 1 (all zeros): %s\n", val == 0x00000000 ? "PASS" : "FAIL");

    write_csr(MSCRATCH, 0xFFFFFFFF);
    val = read_csr(MSCRATCH);
    printf("Test 2 (all ones): %s\n", val == 0xFFFFFFFF ? "PASS" : "FAIL");

    write_csr(MSCRATCH, 0xAAAAAAAA);
    val = read_csr(MSCRATCH);
    printf("Test 3 (pattern A): %s\n", val == 0xAAAAAAAA ? "PASS" : "FAIL");

    write_csr(MSCRATCH, 0x55555555);
    val = read_csr(MSCRATCH);
    printf("Test 4 (pattern B): %s\n", val == 0x55555555 ? "PASS" : "FAIL");

    write_csr(MSCRATCH, 0x12345678);
    val = read_csr(MSCRATCH);
    printf("Test 5 (random): %s\n", val == 0x12345678 ? "PASS" : "FAIL");

    write_csr(MSCRATCH, 0x00000001);
    val = read_csr(MSCRATCH);
    printf("Test 6 (LSB): %s\n", val == 0x00000001 ? "PASS" : "FAIL");

    write_csr(MSCRATCH, 0x80000000);
    val = read_csr(MSCRATCH);
    printf("Test 7 (MSB): %s\n", val == 0x80000000 ? "PASS" : "FAIL");

    write_csr(MSCRATCH, 0x0F0F0F0F);
    val = read_csr(MSCRATCH);
    printf("Test 8 (nibble): %s\n", val == 0x0F0F0F0F ? "PASS" : "FAIL");

    write_csr(MSCRATCH, 0xDEADBEEF);
    val = read_csr(MSCRATCH);
    printf("Test 9 (retention): %s\n", val == 0xDEADBEEF ? "PASS" : "FAIL");

    printf("=== ALL 9 TESTS COMPLETED ===\n");

    return 0;
}


