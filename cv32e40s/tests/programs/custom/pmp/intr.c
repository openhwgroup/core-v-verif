// #include <stdio.h>
// #include <stdlib.h>

#include "pmp.h"

__attribute__((interrupt("machine"))) void u_sw_irq_handler(void)
{
  printf("\nxxxxx User permission denied xxxxx\n");
  printf("\tu_sw_irq_handler\n");

  __asm__ volatile("csrrw %0, mcause, x0"
                   : "=r"(glb_csrs.mcause));
  printf("\tmcause = 0x%lx\n", glb_csrs.mcause);

  // Increment "mepc"
  __asm__ volatile("csrrw %0, mepc, x0"
                   : "=r"(glb_csrs.mepc));
  glb_csrs.mepc += 4;
  __asm__ volatile("csrrw x0, mepc, %0"
                   :
                   : "r"(glb_csrs.mepc));

  // Set mmode again
  __asm__ volatile("csrrw %0, mstatus, x0"
                   : "=r"(glb_csrs.mstatus));
  // mstatus |= (3 << 11);
  glb_csrs.mstatus = 0x1800;
  __asm__ volatile("csrrw x0, mstatus, %0"
                   :
                   : "r"(glb_csrs.mstatus));
  // printf("\tmstatus = 0x%lx before exiting handler\n", glb_csrs.mstatus);
  // __asm__ volatile("csrrw x0, mstatus, %0"
  //                  :
  //                  : "r"(mstatus));
  // printf("\tmstatus = x%x before exiting handler\n", mstatus);
  return;

  exit(EXIT_FAILURE);
}