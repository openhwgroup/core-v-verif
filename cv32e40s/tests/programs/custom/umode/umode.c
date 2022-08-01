// TODO:ropeders license header


#include <stdio.h>
#include <stdlib.h>


extern volatile int  myfunc(void);
//extern volatile void run_in_umode(int (*funptr)(void));
extern volatile int  run_in_umode(int (*funptr)(void));
extern volatile void setup_pmp(void);
extern volatile void set_mmode(void);

extern volatile uint32_t gbl_request_mmode = 0;


__attribute__ ((interrupt ("machine")))
void u_sw_irq_handler(void) {
  uint32_t mcause;
  uint32_t mepc;
  uint32_t mstatus;

  printf("u_sw_irq_handler\n");

  __asm__ volatile("csrrw %0, mcause, x0" : "=r"(mcause));
  printf("mcause = %d\n", mcause);

  if (gbl_request_mmode) {
    gbl_request_mmode = 0;

    // Increment "mepc"
    __asm__ volatile("csrrw %0, mepc, x0" : "=r"(mepc));
    mepc += 4;
    __asm__ volatile("csrrw x0, mepc, %0" : : "r"(mepc));

    // Set mmode again
    __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus));
    mstatus |= (3 << 11);
    __asm__ volatile("csrrw x0, mstatus, %0" : : "r"(mstatus));

    return;
  }

  exit(EXIT_FAILURE);
}


int main(void) {
  int x;

  // Easily visible header
  __asm__ volatile("nop");
  __asm__ volatile("nop");
  __asm__ volatile("nop");

  x = 0;
  printf("x = %d\n", x);
  x = myfunc();
  printf("x = %d\n", x);

  setup_pmp();

  x = 0;
  printf("x = %d\n", x);
  x = run_in_umode(myfunc);
  printf("x = %d\n", x);

  // Easily visible footer
  __asm__ volatile("nop");
  __asm__ volatile("nop");
  __asm__ volatile("nop");
  return EXIT_SUCCESS;
}