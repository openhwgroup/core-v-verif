#include <stdio.h>

int main() {
    //Write out all 32 bits to leave no bits behind
    unsigned int write_val = 0xACE12345;
    unsigned int read_val = 0;

    printf("Executing mscratch CSR test...\n");

    // Write to mscratch (CSR 0x340)
    asm volatile ("csrw mscratch, %0" : : "r" (write_val));

    // Read back from mscratch
    asm volatile ("csrr %0, mscratch" : "=r" (read_val));

    if (read_val == write_val) {
        printf("SUCCESS: Written 0x%08x, Read 0x%08x\n", write_val, read_val);
        return 0; 
    } else {
        printf("FAILURE: Written 0x%08x, Read 0x%08x\n", write_val, read_val);
        return 1;
    }
}
