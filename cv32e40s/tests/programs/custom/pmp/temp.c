#include "pmp.h"

// void temp()
// {

//   PMPXCFG pmpxcfg = {.write = 1, .mode = 3};
//   asm volatile("csrrw x0, 0x3a0, %0" ::"r"(pmpxcfg));
//   printf("\n\tpmpcfg = 0x%x\n\n", pmpxcfg);
//   // printf("\n\tsize of pmpcfg = 0x%x\n\n", sizeof(pmpxcfg));
//   asm volatile("csrrs %0, 0x3a0, x0" :"=r"(pmpxcfg));

//   printf("\n\tpmpbits = %d\n\n", pmpxcfg);

// }