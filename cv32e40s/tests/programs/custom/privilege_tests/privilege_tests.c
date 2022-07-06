// TODO:ropeders license header


#include <stdio.h>
#include <stdlib.h>

extern volatile int  setup_pmp(), change_exec_mode();
int t;
unsigned int mstatus;

__attribute__ ((interrupt ("machine")))
void u_sw_irq_handler(void) { // remove this trap handler and insert an 'ecall handler' instead. 
  unsigned int mepc, tmstatus;

  printf("--- entered trap handler --- \n");

  __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus)); // read the mstatus register
  __asm__ volatile("csrrw %0, mepc, x0" : "=r"(mepc)); // read the mepc

  
  mepc += 4;
  __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc 

  tmstatus = 0x1800;
  __asm__ volatile("csrrs x0, mstatus, %0" :: "r"(tmstatus)); // set machine mode 
}


int privilege_test(void){
  change_exec_mode();
  printf("now outside assembly and the handler\n");
  printf("this is the mstatus register\n");
  printf("%X\n", mstatus);

  return 0;
}




int main(void){
  //setup_pmp();
  t = privilege_test();


  return 0;
}