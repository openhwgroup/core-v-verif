// #include <stdio.h>
// #include <stdlib.h>
#include "pmp.h"

void default_none()
{
  uint32_t mstatus;

  // int mpp = 0x1800;
  __asm__ volatile("csrrs %0, 0x300, x0\n"
                   //  "csrrs %1, 0x341, x0\n"
                   : "=r"(mstatus));
  // if in m mode change to u mode
  if (mstatus == 0x1800)
  {
    printf("\nooooo out of reset ooooo\n");
    // printf("\nmepc before mode switching = %lx\n", rtnaddr);

    change_mode();
    // asm volatile("ecall");
    __asm__ volatile("csrrs %0, 0x300, x0\n"
                     : "=r"(mstatus));
    printf("\nbbbbb back from the handler to M mode mmmmm\n");
    __asm__ volatile("csrrs %0, 0x300, x0\n"
                     : "=r"(mstatus));
    printf("\tmstatus = %lx\n", mstatus);
    printf("\nuuuu U mode test pass uuuuu\n\n");
    exit(EXIT_SUCCESS);
  }
  exit(EXIT_FAILURE);
}