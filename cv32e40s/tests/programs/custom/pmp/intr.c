// #include <stdio.h>
// #include <stdlib.h>

#include "pmp.h"

__attribute__((interrupt("machine"))) void u_sw_irq_handler(void)
{
  uint32_t mcause;
  uint32_t mepc;
  uint32_t mstatus;

  printf("\nxxxxx User permission denied xxxxx\n");
  printf("\tu_sw_irq_handler\n");

  __asm__ volatile("csrrw %0, mcause, x0"
                   : "=r"(mcause));
  printf("\tmcause = %lx\n\n", mcause);

  // Increment "mepc"
  __asm__ volatile("csrrw %0, mepc, x0"
                   : "=r"(mepc));
  mepc += 4;
  __asm__ volatile("csrrw x0, mepc, %0"
                   :
                   : "r"(mepc));

  // Set mmode again
  __asm__ volatile("csrrw %0, mstatus, x0"
                   : "=r"(mstatus));
  mstatus |= (3 << 11);
  __asm__ volatile("csrrw x0, mstatus, %0"
                   :
                   : "r"(mstatus));
  printf("\tmstatus = x%x before exiting handler\n", mstatus);
  return;

  exit(EXIT_FAILURE);
}