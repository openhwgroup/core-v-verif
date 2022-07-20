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

unsigned int return_field(unsigned int x, int start, int stop){
/* 
Takes a register and the desired bit-field LSB start, MSB stop. Returns the bifield.
Ex. return_field(mstatus, 11, 12) --> mstatus[12:11] --> MPP field.
*/
  //printf("entered return_field\n");
  //printf("return input value is: %08X\n", x);
   if (stop == start){
   
   x = (x & 1 << start) >> start ;
   }else{
   x = (x & 3 << start) >> start; 
  //printf("return output value is: %08X\n", x);    
   }
  return x;
}



// extern and global variable declaration
extern volatile void  setup_pmp(), change_exec_mode(int), set_csr_loop(), set_u_mode(), illegal_custom();
volatile unsigned int mstatus, mscratchg, mie, mip, mcause;


//control variables for the status handler
volatile int thand, excc;


// Rewritten interrupt handler
__attribute__ ((interrupt ("machine")))
void u_sw_irq_handler(void) {
  unsigned int mepc, tmstatus;
  //printf("entered trap handler\n");


  if (thand == 6) {// read mip, mie, and move on. 
    __asm__ volatile("csrrw %0, mip, x0" : "=r"(mip)); // read the mepc
    __asm__ volatile("csrrw %0, mie, x0" : "=r"(mie)); // read the mepc
    __asm__ volatile("csrrw %0, mepc, x0" : "=r"(mepc)); // read the mepc

    mepc += 4;

    __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc 
  }

  if (thand == 5) {// In this case trap is expected behaviour, increment mepc and move on.
    __asm__ volatile("csrrw %0, mepc, x0" : "=r"(mepc)); // read the mepc

    mepc += 4;

    __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc 
  }


  if (thand == 4) { // dummy mode to set the core into macine mode. 
  tmstatus = 0x1800;

  __asm__ volatile("csrrs x0, mstatus, %0" :: "r"(tmstatus)); // set machine mode 

  __asm__ volatile("csrrw %0, mepc, x0" : "=r"(mepc)); // read the mepc
  mepc += 4;

  __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc 
  }

  if (thand == 2) {// mscratch_reliable_check()
  __asm__ volatile("csrrw %0, mscratch, x0" : "=r"(mscratchg));

  __asm__ volatile("csrrw %0, mepc, x0" : "=r"(mepc)); // read the mepc
  mepc += 4;

  __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc 

  tmstatus = 0x1800;

  __asm__ volatile("csrrs x0, mstatus, %0" :: "r"(tmstatus)); // set machine mode 
  }


  if (thand == 0) { // This is the privilege_test behavior
    __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus)); // read the mstatus register
 
    __asm__ volatile("csrrw %0, mepc, x0" : "=r"(mepc)); // read the mepc

    
    mepc += 4;

    __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc 

    tmstatus = 0x1800;

    __asm__ volatile("csrrs x0, mstatus, %0" :: "r"(tmstatus)); // set machine mode 
  }


  if (thand == 1) {// This is csr_privilege_loop behaviour
    excc += 1;
    //printf("The excc is now: %d\n", excc);
    __asm__ volatile("csrrw %0, mepc, x0" : "=r"(mepc)); // read the mepc

    mepc += 4;

    __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc 


  }


}


void set_m_mode(void) {
// Changes the handler functionality, and then calls an exception.
thand = 4;
__asm__ volatile("ecall");
}



//First priviledge test
void privilege_test(void){
  int input_mode = 0;
  unsigned int mmask;
  thand = 0;

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

}

void csr_cross_privilege(void) {
/* 
Try all kinds of access to all implemented U- and M-mode CSR registers while in U- and M-mode (cross), ensure appropriate access grant/deny. (Caveat) There is only one register, JVT.
 */

  excc = 0;
  thand = 1; 
  setup_pmp();
  set_u_mode();
  unsigned int utest;
  __asm__ volatile("csrrs %0, 0x017, x0" : "=r"(utest)); // read
  __asm__ volatile("csrrw x0, 0x017, %0" :: "r"(utest)); // write
  __asm__ volatile("csrrs x0, 0x017, %0" :: "r"(utest)); // set
  __asm__ volatile("csrrc x0, 0x017, %0" :: "r"(utest)); // clear
  __asm__ volatile("csrrw x0, 0x017, %0" :: "r"(utest)); // write again to 'reset' the initial value of the register before moving to another test
  assert_or_die(excc, 0, "Some tests seem to have triggered the exception handler, user should have access to this register\n"); 



/* csrrs  t0, 0xff5, x0 
csrrw  x0, 0xff5, t0 
csrrs  x0, 0xff5, t0 
csrrc  x0, 0xff5, t0  */
}

void misa_check(void) {
 /* 
  Read misa and see that "U" is always on
  Read misa and see that "N" is always off.
  */
  set_m_mode();
  unsigned int misa, user, reserved;
  __asm__ volatile("csrrw %0, misa, x0" : "=r"(misa));
  user = (misa & 1 << 20) >> 20;
  reserved = (misa & 1 << 13) >> 13;
  assert_or_die(user, 1, "error: User-mode not set in the misa register\n");
  assert_or_die(reserved, 0, "error: N-bit set in the misa register\n");

}

void mstatus_implement_check(void){
  /* 
  F-extension, S-mode are not supported on the platform, FS and XS should therefore be 0, and if both of those are 0 then the SD field should also be 0.
  */
  unsigned int mstatus, XS, FS, SD;
  __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus));
  XS = (mstatus & 3 << 15);// >> 15;
  FS = (mstatus & 3 << 13);// >> 13;
  SD = (mstatus & 1 << 31);// >> 31;
  //printf("%08X\n", mstatus);
  assert_or_die(XS, 0x0, "error: XS set in the mstatus register\n");
  assert_or_die(FS, 0x0, "error: FS set in the mstatus register\n");
  assert_or_die(SD, 0, "error: SD set in the mstatus register\n");



}

void mscratch_reliable_check(void){
  /* 
  Check that mscratch never changes in U-mode.
  change to u-mode, attempt to write to mscratch, trap and assert that mscratch is the same.
  */
  thand = 2; // set the exception handler behavior.
  unsigned int mscratch, uwrite;
  uwrite = 0x1800;


  __asm__ volatile("csrrw %0, mscratch, x0" : "=r"(mscratch));
  setup_pmp();
  set_u_mode();
  __asm__ volatile("csrrw x0, mscratch, %0" :: "r"(uwrite)); // write to the mscratch (in user mode)
  assert_or_die(mscratch, mscratchg, "error: mscratch register changed after attempted user mode read\n");

}

void should_not_exist_check(void) {
/* 
Catch all funciton for registers which should not exist according to the intern v-plan (Summer 2022) for the cv32e40s core.
*/
unsigned int csr_acc, user, misa;
csr_acc = 0x1800; // some std value
set_m_mode();
thand = 5; // sets the behavior of the exception handler.
// SPP should be 0 as S-mode is not implemented.
__asm__ volatile("csrrw %0, misa, x0" : "=r"(misa));
user = (misa & 1 << 18) >> 18;
assert_or_die(user, 0, "error: Supervisor-mode set in the misa register\n");


thand = 1; // setting the trap handler behaviour
excc = 0; // resetting the trap handler count

// mcounteren should exist
__asm__ volatile("csrrw %0, mcounteren, x0" : "=r"(csr_acc));
assert_or_die(excc, 0, "error: reading the mcounteren register should not trap in M-mode\n");


// mideleg and medeleg register should not be implemented
__asm__ volatile("csrrw %0, mideleg, x0" : "=r"(csr_acc));
__asm__ volatile("csrrw %0, medeleg, x0" : "=r"(csr_acc));

//various N-mode register should not exist anymore.
__asm__ volatile("csrrw %0, ustatus, x0"  : "=r"(csr_acc));
__asm__ volatile("csrrw %0, uie, x0"      : "=r"(csr_acc));
__asm__ volatile("csrrw %0, utvec, x0"    : "=r"(csr_acc));
__asm__ volatile("csrrw %0, uscratch, x0" : "=r"(csr_acc));
__asm__ volatile("csrrw %0, uepc, x0"     : "=r"(csr_acc));
__asm__ volatile("csrrw %0, ucause, x0"   : "=r"(csr_acc));
__asm__ volatile("csrrw %0, utval, x0"    : "=r"(csr_acc));
__asm__ volatile("csrrw %0, uip, x0"      : "=r"(csr_acc));

assert_or_die(excc, 10, "error: some of the unimplemented registers did not trap on instrs attempt\n");
}

void no_u_traps(void) {
  /* 
  U-mode interrupts are not supported. The 'zero-bits' in the 'mip' and 'mie' should remain zero.
  */
  unsigned int mask, garb, mipr, mier;
  mask = 0xF777; // zero bits mask
  mipr = mier = mask;
  thand = 6; // set trap handler behaviour
  setup_pmp();
  set_u_mode();
  __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(garb)); // illegal read 
  mipr = mip & mask;
  mier = mie & mask;
  assert_or_die(mier, 0x0, "error: zero-fields in the mier changed after interrrupts\n");
  assert_or_die(mipr, 0x0, "error: zero-fields in the mipr changed after interrupts\n");

}

void proper_xpp_val(void) {
/* 
When a trap is taken from privilege mode y into x, xPP is set to y. Assert this is true for M- and U-mode.
*/
  thand = 0;
  int input_mode = 0;
  unsigned int mmask;
  __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus));
  setup_pmp();
  set_u_mode();
  for (int i = 0; i <= 3; i = i + 3){
    input_mode = i << 11;
    change_exec_mode(input_mode);
    mmask = (mstatus & 3 << 11); // mask to get just the MPP field.
    if (i == 0) {
        assert_or_die(mmask, 0x0, "error: MPP does not display previous mode U-mode as expected\n");
        }
    if (i == 3) {
      assert_or_die(mmask, 0x1800, "error: MPP does not display previous mode M-mode as expected\n");
      }     
  };
}

void proper_ret_priv(void) {
/* 
Assert that U-mode is set in the MPP after returning from a M-mode.
*/
unsigned int mmask;
thand = 0;
setup_pmp();
set_u_mode();
__asm__ volatile("mret");
__asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus));
mmask = (mstatus & (3 << 11)); // mask to get the MPP field.
assert_or_die(mmask, 0x0, "error: MPP is not set to least privileged mode after executing mret\n");
mmask = (mstatus & (1 << 17)); // mask to get the MPRV field.
assert_or_die(mmask, 0x0, "error: MPRV is not set to 0 after executing mret\n");
}

// Illegal instruction fault is mcause[10:0] == 2
void check_wfi_trap(void) {
  /* 
  When in U-mode and TW=1 in mstatus, executing a WFI should trap to an illegal exception.
  */
  thand = 0;
  unsigned int set_tw, pmstatus, rmcause;
  set_tw = 0x200000; // mask for TW in mstatus
  setup_pmp();
  set_m_mode();
  __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus));
  pmstatus = mstatus | set_tw;
  __asm__ volatile("csrrw x0, mstatus, %0" :: "r"(pmstatus));
  set_u_mode();
  __asm__ volatile("wfi");
  __asm__ volatile("csrrw %0, mcause, x0" : "=r"(rmcause));
  printf("mcause is: %08X\n", rmcause);  pmstatus = rmcause & 0x2;
  assert_or_die(pmstatus, 0x2, "error: mcause not showing illegal insn exception after TW WFI trap.\n");
}

void correct_ecall(void) {
  /* 
  Be in U-mode, execute ecall, ensure that an exception is taken and mcause is set correctly.
  */
  unsigned int rmcause, pmstatus;
  setup_pmp();
  set_u_mode();
  __asm__ volatile("ecall");
  __asm__ volatile("csrrw %0, mcause, x0" : "=r"(rmcause));   
  pmstatus = rmcause & 0x8;
  assert_or_die(rmcause, 0x08, "error: mcause not showing ecall code after U-mode ecall.\n");

}

void correct_xret(void) {
  /* 
  Be in U-mode, execute MRET, ensure that it does not execute like it does in M-mode: Raise illegal exception, priv mode goes to M and not MPP, MPP becomes U, MPRV is unchanged.
  */
 volatile int MPRVs, mcode, MPP, MPRVt;

  __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus));
  // printf("this is the mstatus: %08X\n", mstatus);
  MPRVs = return_field(mstatus, 17, 17);
  setup_pmp();
  set_u_mode();
  __asm__ volatile("mret");
  __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus));
  // printf("this is the mstatus: %08X\n", mstatus);
  MPP = return_field(mstatus, 11, 12);
  MPRVt = return_field(mstatus, 17, 17);
  __asm__ volatile("csrrw %0, mcause, x0" : "=r"(mcause));
  // printf("this is the mcause: %08X\n", mcause);
  mcode = return_field(mcause, 1, 1);
  // printf("this is the mcode: %08X\n", mcode);
  assert_or_die(MPRVt, MPRVs, "error: MPRV changed state after illegal mret\n");
  assert_or_die(mcode, 1, "error: mcause did not report illegall exception\n");
  assert_or_die(MPP, 0x0, "error: MPP not set to U-mode after illegal insn.\n");

}

void check_uret(){
/* Executing uret should give an illegal instruction exception. */

  int mcode;
  __asm__ volatile("uret");
  __asm__ volatile("csrrw %0, mcause, x0" : "=r"(mcause));
  mcode = return_field(mcause, 1, 1);
  assert_or_die(mcode, 1, "error: mcause did not report illegal exception on 'uret' call\n");
}

int main(void){
/* 
  reset_mode();
  privilege_test();
  // sr_cross_privilege(); // TODO: This test will fail until the JVT-register is implemented.
  misa_check();
  mstatus_implement_check();
  mscratch_reliable_check();
  should_not_exist_check();
  no_u_traps();
  proper_xpp_val();
  proper_ret_priv();
  check_wfi_trap();
  correct_ecall();
  correct_xret();
  check_uret();
*/


  return EXIT_SUCCESS;
}