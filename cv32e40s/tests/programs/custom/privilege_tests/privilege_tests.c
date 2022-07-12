// TODO:ropeders license header


#include <stdio.h>
#include <stdlib.h>
#include "corev_uvmt.h"


// Declaration of assert 
static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}

// extern and global variable declaration
extern volatile void  setup_pmp(), change_exec_mode(int), set_u_mode();//, loop_reg(int);
unsigned int mstatus;


//control variables for the status handler
int thand, excc;



// Rewritten interrupt handler
__attribute__ ((interrupt ("machine")))
void u_sw_irq_handler(void) {
  unsigned int mepc, tmstatus;



  if (thand == 0) { // This is the privilege_test behavior
    __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus)); // read the mstatus register
    // printf("handler mstatus: %X\n", mstatus);
    __asm__ volatile("csrrw %0, mepc, x0" : "=r"(mepc)); // read the mepc

    
    mepc += 4;
    __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc 

    tmstatus = 0x1800;
    __asm__ volatile("csrrs x0, mstatus, %0" :: "r"(tmstatus)); // set machine mode 
  };

  if (thand == 1) {// This is csr_privilege behaviour
    //printf("entered trap handler!\n");
    __asm__ volatile("csrrw %0, mepc, x0" : "=r"(mepc)); // read the mepc
    mepc += 4;
    __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc 
    excc++;
  }


}


//First priviledge test
void privilege_test(void){
  int input_mode = 0;
  unsigned int mmask;
  // Todo:
  /* 
    - make the change_exec_mode function take arguments.
    - create to for loop to check all the different supported modes.
   */

  for (int i = 0; i <= 3; i++){
    input_mode = i << 11;
    // printf("input to the test is: %x\n", input_mode);
    change_exec_mode(input_mode);
    mmask = (mstatus & 3 << 11); // mask to get just the MPP field.
    if (i == 3) {
        assert_or_die(mmask, 0x1800, "error: core did not enter privilege mode as expected\n");
        }else {
        assert_or_die(mmask, 0x0, "error: core did not enter privilege mode as expected\n");
      };
  };

}

void reset_mode(void){
/* 
To satisfy the testing criteria this test must run first
this is to ensure 'Ensure that M-mode is the first mode entered after reset.
*/
__asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus)); // read the mstatus register
assert_or_die(mstatus, 0x1800, "error: core did not enter M-mode after reset\n");
printf("reset_mode test checked succesfully\n");
}


void csr_privilege(void){
/* 
Try all kinds of accesses (R, W, RW, S, C, …) to all M-level CSRs while in U-level;
ensure illegal instruction exception happens.
*/

/* 
// From 0x100 to 0xFFF
for(int i = 256; i <= 4095; i++){ // this runs through all the different CSR-registers
  for ()
}
*/

  thand = 1; // set u_sw_irq_handler to correct behaviour
  excc = 0; // set interrupt counter to 0
  setup_pmp();
  set_u_mode();
  assert_or_die(excc, 12288, "Some tests seem to not have triggered the exception handler!\n");
}


int main(void){
  //setup_pmp();
  //TODO:
  /* 

  
   */
  csr_privilege();
  // reset_mode(); // Done
  //privilege_test(); // this test is disable until github cv32e40s issue 243 is solved.
  //csr_privilege(); // CSR privilege tests






  return EXIT_SUCCESS;
}