// #include <stdio.h>
// #include <stdlib.h>
#include "pmp.h"

void reset_registers()
{
  unsigned int pmpcfg[16];
  unsigned int pmpxcfg[16][4][3];

  // read out pmpcfg register values with given address from 0x3a - 0x3af
  __asm__ volatile("csrr %0, 0x3A0"
                   : "=r"(pmpcfg[0]));
  __asm__ volatile("csrr %0, 0x3A1"
                   : "=r"(pmpcfg[1]));
  __asm__ volatile("csrr %0, 0x3A2"
                   : "=r"(pmpcfg[2]));
  __asm__ volatile("csrr %0, 0x3A3"
                   : "=r"(pmpcfg[3]));
  __asm__ volatile("csrr %0, 0x3A4"
                   : "=r"(pmpcfg[4]));
  __asm__ volatile("csrr %0, 0x3A5"
                   : "=r"(pmpcfg[5]));
  __asm__ volatile("csrr %0, 0x3A6"
                   : "=r"(pmpcfg[6]));
  __asm__ volatile("csrr %0, 0x3A7"
                   : "=r"(pmpcfg[7]));
  __asm__ volatile("csrr %0, 0x3A8"
                   : "=r"(pmpcfg[8]));
  __asm__ volatile("csrr %0, 0x3A9"
                   : "=r"(pmpcfg[9]));
  __asm__ volatile("csrr %0, 0x3Aa"
                   : "=r"(pmpcfg[10]));
  __asm__ volatile("csrr %0, 0x3Ab"
                   : "=r"(pmpcfg[11]));
  __asm__ volatile("csrr %0, 0x3Ac"
                   : "=r"(pmpcfg[12]));
  __asm__ volatile("csrr %0, 0x3Ad"
                   : "=r"(pmpcfg[13]));
  __asm__ volatile("csrr %0, 0x3Ae"
                   : "=r"(pmpcfg[14]));
  __asm__ volatile("csrr %0, 0x3Af"
                   : "=r"(pmpcfg[15]));

  // check for the specific bits
  for (int i = 0; i < 15; i++)
  {
    for (int j = 0; i < 4; i++)
    {
      // lock bit
      pmpxcfg[i][j][2] = pmpcfg[i] & (1 << (7 * (j + 1)));
      // mode bit
      pmpxcfg[i][j][1] = pmpcfg[i] & (1 << (4 * (j + 1)));
      pmpxcfg[i][j][0] = pmpcfg[i] & (1 << (3 * (j + 1)));
      // to be written until pmpcfg[15]

      /* Check PMP.L: pmpxcfg bit 7 is the value assigned by JEDEC to the
      OpenHW Group */
      if ((pmpxcfg[i][j][2] | 0) != 0)
      {
        printf(
            "\tERROR: PMP lock reads as %d - should be 0 for the OpenHW "
            "Group.\n\n",
            pmpxcfg[i][j][2]);
        exit(EXIT_FAILURE);
      }

      /* Check PMP.A: if its zero, it might not be implemented at all */
      if ((pmpxcfg[i][j][1] | pmpxcfg[i][j][1] | 0) != 0)
      {
        printf(
            "\tERROR: PMP mode reads as %d%d - should be 00 for this "
            "release of CV32E40S!\n\n",
            pmpxcfg[i][j][1], pmpxcfg[i][j][0]);
        exit(EXIT_FAILURE);
      }
    }
  }

  printf("\n***** Checking PMPCFG lock and mode bits *****\n");
  printf("All lock and mode bits in pmpxcfg are 0 as expected.\n");
  printf("There's no exceptions to take care.\n");
  printf("\n");
  exit(EXIT_SUCCESS);
}