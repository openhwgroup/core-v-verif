#include <stdint.h>
#include <stdio.h>


// This is the virtual printer peripheral address
#define VIRTUAL_PRINTER_ADDR 0x10000000


// Macros for CSR access using inline assembly
#define write_csr(reg, val) \
    asm volatile ("csrw " #reg ", %0" :: "r"(val))

#define read_csr(reg) ({ \
    uint32_t __v; \
    asm volatile ("csrr %0, " #reg : "=r"(__v)); \
    __v; \
})

int main() {
    uint32_t test_patterns[] = {0xAAAAAAAA, 0x55555555};
    int success = 1;

    for (int i = 0; i < 2; i++) {
        uint32_t write_val = test_patterns[i];
        
        // Write to mscratch (address 0x340)
        write_csr(mscratch, write_val);
        
        // Read back from mscratch
        uint32_t read_val = read_csr(mscratch);

        if (read_val == write_val) {
            printf("Pattern 0x%08X: PASS\n", write_val);
        } 
	else {
		printf("Pattern 0x%08X: FAIL (Read: 0x%08X)\n", write_val, read_val);
		success = 0;
        }
    }

    return success ? 0 : 1;
}

