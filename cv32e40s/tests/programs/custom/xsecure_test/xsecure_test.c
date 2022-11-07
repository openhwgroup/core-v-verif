#ifndef __XSECURE_TEST_H__
#define __XSECURE_TEST_H__

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

//TODO: functions are fetched from the privilege test code. If these functions end up in a common function file, we should adopt this file to use the common functions.

#define CSRADDR_CPUCTRL     0xBF0
#define CSRADDR_SECURESEED0 0xBF9
#define CSRADDR_SECURESEED1 0xBFA
#define CSRADDR_SECURESEED2 0xBFC

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
  TRAP_INCR_BEH,
  UNEXPECTED_ERROR_BEH
} trap_behavior_t;

// trap handler behavior definitions
volatile trap_behavior_t trap_handler_beh = UNEXPECTED_ERROR_BEH;

volatile uint32_t num_trao_executions;
volatile uint32_t unexpected_irq_beh = 0;


/* Declaration of assert */
static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
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
      num_trao_executions += 1;
      increment_mepc();
      break;

    // unexpected handler irq (UNEXPECTED_ERROR_BEH and more)
    default:
      unexpected_irq_beh = 1;
  }

}


/////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////


void test_read_ctrlcpu_and_secureseeds_in_machine_mode(void){
  uint32_t csr_read;

  // setting the trap handler behaviour
  trap_handler_beh = M_MODE_BEH;

  // enter machine mode:
  set_m_mode();

  // read secureseed:
  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED0) ", x0" : "=r"(csr_read));
  assert_or_die(csr_read, 0, "error: secureseed0 is not read as zero\n");
  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED1) ", x0" : "=r"(csr_read));
  assert_or_die(csr_read, 0, "error: secureseed1 is not read as zero\n");
  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED2) ", x0" : "=r"(csr_read));
  assert_or_die(csr_read, 0, "error: secureseed2 is not read as zero\n");

  // set the trap handler to go into default mode
  trap_handler_beh = UNEXPECTED_ERROR_BEH;

}


void test_read_ctrlcpu_and_secureseeds_in_user_mode(void){
  uint32_t csr_read;

  // setting the trap handler behaviour
  trap_handler_beh = TRAP_INCR_BEH;

  // resetting the trap handler count
  num_trao_executions = 0;

  // enter usermode:
  set_u_mode();

  // try to read ctrlcpu and secureseed:
  __asm__ volatile("csrrw %0, " STR(CSRADDR_CPUCTRL) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrs %0, " STR(CSRADDR_CPUCTRL) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrc %0, " STR(CSRADDR_CPUCTRL) ", x0" : "=r"(csr_read));

  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED0) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrs %0, " STR(CSRADDR_SECURESEED0) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrc %0, " STR(CSRADDR_SECURESEED0) ", x0" : "=r"(csr_read));

  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED1) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrs %0, " STR(CSRADDR_SECURESEED1) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrc %0, " STR(CSRADDR_SECURESEED1) ", x0" : "=r"(csr_read));

  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED2) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrs %0, " STR(CSRADDR_SECURESEED2) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrc %0, " STR(CSRADDR_SECURESEED2) ", x0" : "=r"(csr_read));

  // number of exceptions should equal number of acesses
  assert_or_die(num_trao_executions, 4*3, "error: accessing cpuctrl or secureseed_ in usermode does not cause a trap\n");

  // set the trap handler to go into default mode
  trap_handler_beh = UNEXPECTED_ERROR_BEH;

}


int main(void){

  unexpected_error_beh = 0

  setup_pmp();

  test_read_ctrlcpu_and_secureseeds_in_machine_mode();
  test_read_ctrlcpu_and_secureseeds_in_user_mode();

  // check if there was an unexpected irq handler req
  assert_or_die(num_trao_executions, 4*3, "error: accessing cpuctrl or secureseed_ in usermode does not cause a trap\n");

  return EXIT_SUCCESS;
}

#endif