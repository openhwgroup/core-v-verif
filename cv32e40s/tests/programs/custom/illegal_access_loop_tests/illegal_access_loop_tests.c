#include <stdio.h>
#include <stdlib.h>
#include "corev_uvmt.h"
#include <stdint.h>

// extern and global variable declaration
extern volatile void  setup_pmp(), set_u_mode(), illegal_custom();

// Declaration of assert 
static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}

//control variables for the status handler
volatile int excc;

__attribute__ ((interrupt ("machine")))
void u_sw_irq_handler(void) {
  unsigned int mepc;

    excc += 1;
    //printf("The excc is now: %d\n", excc);
    __asm__ volatile("csrrw %0, mepc, x0" : "=r"(mepc)); // read the mepc

    mepc += 4;

    __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc 

}


void illegal_custom_loop(void){
/* 
Execute custom SYSTEM "Unprivileged or User-Level" instructions, ensure they are illegal instructions.
*/

  // Ref. illegal_custom_op_gen.py file to see how the instructions were generated.
  excc = 0; // set interrupt counter to 0
  setup_pmp(); // define a generous pmp region for u-mode
  illegal_custom(); // run the generated instructions in assembly
  assert_or_die(excc, 131072, "Some illegal U-mode custom intructions did not trap!\n");
}

void csr_privilege_loop(void){
/* 
Try all kinds of accesses (R, W, RW, S, C, …) to all M-level CSRs while in U-level;
ensure illegal instruction exception happens.
*/

  // see the gen_loop.py file for which registers are included in the test
  excc = 0; // set interrupt counter to 0
  setup_pmp();
  set_csr_loop();
  assert_or_die(excc, 12288, "Some illegal csr access attempts seem to not have triggered the exception handler!\n");
}



int main(void){

    illegal_custom_loop(); // long test + 60 minutes 
    //csr_privilege_loop();

}