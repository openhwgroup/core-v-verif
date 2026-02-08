/*
*******************************************************************************
**
** Test to verify full 32-bit write/read access to the mscratch CSR (0x340)
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

#define MSCRATCH_CSR 0x340

static inline void write_mscratch(unsigned int value)
{
    __asm__ volatile("csrw %0, %1" :: "i"(MSCRATCH_CSR), "r"(value));
}

static inline unsigned int read_mscratch(void)
{
    unsigned int value;
    __asm__ volatile("csrr %0, %1" : "=r"(value) : "i"(MSCRATCH_CSR));
    return value;
}

int main(int argc, char *argv[])
{
    unsigned int patterns[] = {
        0x00000000,
        0xFFFFFFFF,
        0xAAAAAAAA,
        0x55555555,
        0xDEADBEEF
    };

    unsigned int readback;
    int i;

    printf("\nMSCRATCH CSR Test\n");
    printf("------------------\n");

    for (i = 0; i < sizeof(patterns)/sizeof(patterns[0]); i++) {

        printf("Writing  0x%08X to mscratch...\n", patterns[i]);

        write_mscratch(patterns[i]);
        readback = read_mscratch();

        printf("Readback 0x%08X\n", readback);

        if (readback != patterns[i]) {
            printf("ERROR: Mismatch detected!\n");
            return EXIT_FAILURE;
        }
    }

    printf("\nAll patterns verified successfully.\n\n");
    return EXIT_SUCCESS;
}
