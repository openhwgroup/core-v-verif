/* mscratch.c
 *
 * Test program for the mscratch CSR (Machine Scratch Register)
 * Verifies read/write access to all 32 bits using various test patterns
 */

#include <stdint.h>
#include <stdio.h>

#define WRITE_CSR(csr, val) asm volatile ("csrw " #csr ", %0" :: "r"(val))
#define READ_CSR(csr) __extension__ ({ uint32_t __tmp; asm volatile ("csrr %0, " #csr : "=r"(__tmp)); __tmp; })

static const uint32_t test_patterns[] = {
    // Boundary cases
    0x00000000,
    0xFFFFFFFF,
    
    // Single bit set
    0x00000001,  // LSB
    0x00010000,  // bit 16
    0x80000000,  // MSB
    
    // Single bit clear
    0xFFFFFFFE,  // all except LSB
    0xFFFEFFFF,  // all except bit 16
    0x7FFFFFFF,  // all except MSB
    
    // 2-bit repeating
    0x55555555,  // 01
    0xAAAAAAAA,  // 10
    
    // 3-bit repeating (with inverses)
    0x49249249,  // 010
    0xB6DB6DB6,  // 101 (inverse)
    0x92492492,  // 100
    0x6DB6DB6D,  // 011 (inverse)
    
    // 4-bit repeating
    0x33333333,  // 0011
    0xCCCCCCCC,  // 1100 (inverse)
    
    // Nibble patterns
    0x0F0F0F0F,
    0xF0F0F0F0,
    
    // Byte patterns
    0x00FF00FF,
    0xFF00FF00,
    
    // Half-word patterns
    0x0000FFFF,
    0xFFFF0000,
    
    // Random patterns
    0x12345678,
    0xDEADBEEF
};

#define NUM_PATTERNS (sizeof(test_patterns) / sizeof(test_patterns[0]))

int main() {
    printf("Starting mscratch CSR test with %d patterns...\n\n", NUM_PATTERNS);
    
    // Check initial state
    uint32_t initial = READ_CSR(mscratch);
    if (initial != 0) {
        printf("Warning: mscratch not zero at start (0x%08x)\n", (unsigned int)initial);
    }
    
    int passed = 0;
    int failed = 0;
    
    // Test each pattern
    for (int i = 0; i < NUM_PATTERNS; i++) {
        uint32_t write_val = test_patterns[i];
        
        // Write to mscratch and read it back
        WRITE_CSR(mscratch, write_val);
        uint32_t read_val = READ_CSR(mscratch);
        
        // Check if we got back what we wrote
        if (read_val != write_val) {
            printf("mscratch FAIL: wrote 0x%08x, read 0x%08x\n", 
                   (unsigned int)write_val, (unsigned int)read_val);
            failed++;
        } else {
            printf("mscratch PASS: 0x%08x\n", (unsigned int)write_val);
            passed++;
        }
    }
    
    // Set mscratch back to zero
    WRITE_CSR(mscratch, 0);
    
    // Show results
    printf("\n=== Test Summary ===\n");
    printf("Passed: %d/%d\n", passed, NUM_PATTERNS);
    printf("Failed: %d/%d\n", failed, NUM_PATTERNS);
    
    if (failed == 0) {
        printf("mscratch test PASSED\n");
        return 0;
    } else {
        printf("mscratch test FAILED\n");
        return 1;
    }
}
