#ifndef __XSECURE_TEST_H__
#define __XSECURE_TEST_H__

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

//TODO: functions are fetched from the privilege test code. If these functions end up in a common function file, we should adopt this file to use the common functions.

#define CPUADDR_CPUCTRL     0xBF0
#define CPUADDR_SECURESEED0 0xBF9
#define CPUADDR_SECURESEED1 0xBFA
#define CPUADDR_SECURESEED2 0xBFC

// macros for using defines in inline asm
#define S(x) #x
#define STR(s) S(s)

// global values to hold registers for tests
volatile uint32_t cpuctrl, secureseed0, secureseed1, secureseed2;

int read_ctrlcpu_and_secureseeds_in_user_mode(void);
int read_ctrlcpu_and_secureseeds_in_machine_mode(void);


// assembly function to setup a generous PMP-region for user mode.
extern volatile void  setup_pmp();
// assembly function to set privilege-mode to user-mode
extern volatile void set_u_mode();

// standard value for the mstatus register
#define MSTATUS_STD_VAL 0x1800

typedef enum {
  M_MODE_BEH,
  TRAP_INCR_BEH
} trap_behavior_t;

// trap handler behavior definitions
volatile trap_behavior_t trap_handler_beh;

volatile uint32_t NUM_TRAP_EXECUTIONS;


/* Declaration of assert */
static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}

/* Retuns specific bit-field from [bit_indx_low : bit_indx_high] in register x */
unsigned int get_field(unsigned int x, int bit_indx_low, int bit_indx_high){
    int field = ( 1 << ( (bit_indx_high - bit_indx_low) + 1) )  - 1;
    x = (x & (field << bit_indx_low) ) >> bit_indx_low;
    return x;
}


/* Changes the handler functionality, and then calls an exception to change into m-mode. */
void set_m_mode(void) {
  trap_handler_beh = M_MODE_BEH;
  __asm__ volatile("ecall");
}


/* Checks the mepc for compressed instructions and increments appropriately */
void increment_mepc(void){
  volatile unsigned int insn, mepc;

    // read the mepc
    __asm__ volatile("csrrs %0, mepc, x0" : "=r"(mepc));

    // read the contents of the mepc pc.
    __asm__ volatile("lw %0, 0(%1)" : "=r"(insn) : "r"(mepc));

    // check for compressed instruction before increment.
    if ((insn & 0x3) == 0x3) {
      mepc += 4;
    } else {
      mepc += 2;
    }

    // write to the mepc
    __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc));
}

/* Rewritten interrupt handler */
__attribute__ ((interrupt ("machine")))
void u_sw_irq_handler(void) {

  switch(trap_handler_beh) {

    // set Machine mode in the trap handler
    case M_MODE_BEH :
      __asm__ volatile("csrrs x0, mstatus, %0" :: "r"(MSTATUS_STD_VAL));
      increment_mepc();
      break;

    // csr_privilege_loop behavior
    case TRAP_INCR_BEH :
      NUM_TRAP_EXECUTIONS += 1;
      increment_mepc();
      break;
  }

}


/////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////


void test_read_ctrlcpu_and_secureseeds_in_machine_mode(void){
  uint32_t csr_read;

  // setting the trap handler behaviour
  trap_handler_beh = TRAP_INCR_BEH;

  // resetting the trap handler count
  NUM_TRAP_EXECUTIONS = 0;

  // enter machine mode:
  set_m_mode();

  // read secureseed:
  __asm__ volatile("csrrw %0, " STR(CPUADDR_SECURESEED0) ", x0" : "=r"(csr_read));
  assert_or_die(csr_read, 0, "error: secureseed0 is not read as zero\n");
  __asm__ volatile("csrrw %0, " STR(CPUADDR_SECURESEED1) ", x0" : "=r"(csr_read));
  assert_or_die(csr_read, 0, "error: secureseed1 is not read as zero\n");
  __asm__ volatile("csrrw %0, " STR(CPUADDR_SECURESEED2) ", x0" : "=r"(csr_read));
  assert_or_die(csr_read, 0, "error: secureseed2 is not read as zero\n");

}


void test_read_ctrlcpu_and_secureseeds_in_user_mode(void){
  uint32_t csr_read;

  // setting the trap handler behaviour
  trap_handler_beh = TRAP_INCR_BEH;

  // resetting the trap handler count
  NUM_TRAP_EXECUTIONS = 0;

  // enter usermode:
  set_u_mode();

  // try to read ctrlcpu and secureseed:
  __asm__ volatile("csrrw %0, " STR(CPUADDR_CPUCTRL) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrs %0, " STR(CPUADDR_CPUCTRL) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrc %0, " STR(CPUADDR_CPUCTRL) ", x0" : "=r"(csr_read));

  __asm__ volatile("csrrw %0, " STR(CPUADDR_SECURESEED0) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrs %0, " STR(CPUADDR_SECURESEED0) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrc %0, " STR(CPUADDR_SECURESEED0) ", x0" : "=r"(csr_read));

  __asm__ volatile("csrrw %0, " STR(CPUADDR_SECURESEED1) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrs %0, " STR(CPUADDR_SECURESEED1) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrc %0, " STR(CPUADDR_SECURESEED1) ", x0" : "=r"(csr_read));

  __asm__ volatile("csrrw %0, " STR(CPUADDR_SECURESEED2) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrs %0, " STR(CPUADDR_SECURESEED2) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrc %0, " STR(CPUADDR_SECURESEED2) ", x0" : "=r"(csr_read));

  // number of exceptions should equal number of acesses
  assert_or_die(NUM_TRAP_EXECUTIONS, 4*3, "error: accessing cpuctrl or secureseed_ in usermode does not cause a trap\n");

}


int main(void){

  setup_pmp();

  test_read_ctrlcpu_and_secureseeds_in_machine_mode();
  test_read_ctrlcpu_and_secureseeds_in_user_mode();

  return EXIT_SUCCESS;
}

#endif