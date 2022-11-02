#ifndef __XSECURE_TEST_H__
#define __XSECURE_TEST_H__

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
//#include "xsecure_test.h"

#define CPUADDR_CPUCTRL     0xBF0
#define CPUADDR_SECURESEED0 0xBF9
#define CPUADDR_SECURESEED1 0xBFA
#define CPUADDR_SECURESEED2 0xBFC

// Macros for using defines in inline asm
#define S(x) #x
#define STR(s) S(s)

//global values to hold registers for tests
volatile uint32_t cpuctrl, secureseed0, secureseed1, secureseed2;

int read_ctrlcpu_and_secureseeds_in_user_mode(void);
int read_ctrlcpu_and_secureseeds_in_machine_mode(void);

/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////// TODO: lånt kode fra priviliged tests: /////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////

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


/* Assembly function to set privilege-mode to user-mode */
void set_u_mode() {
  uint32_t u_mode_setting = 0x1800;
  printf("KD: 2.1.1\n");
  __asm__ volatile( "csrrc  x0, mstatus,  %0;" : : "r"(u_mode_setting));
  printf("KD: 2.1.2\n");
  __asm__ volatile( "csrrw  x0, mepc,     ra;");
  printf("KD: 2.1.3\n");

  __asm__ volatile( "csrrc  x0, mstatus,  %0;"
                    "csrrw  x0, mepc,     ra;" //denne er litt feil kanskje TODO
                    "mret;"
                    : : "r"(u_mode_setting));
}


/* Changes the handler functionality, and then calls an exception to change into m-mode. */
void set_m_mode(void) {
  trap_handler_beh = M_MODE_BEH;
  __asm__ volatile("ecall");
}


/* Checks the mepc for compressed instructions and increments appropriately */
void increment_mepc(void){
  volatile unsigned int insn, mepc;

    __asm__ volatile("csrrs %0, mepc, x0" : "=r"(mepc)); // read the mepc
    __asm__ volatile("lw %0, 0(%1)" : "=r"(insn) : "r"(mepc)); // read the contents of the mepc pc.
    if ((insn & 0x3) == 0x3) { // check for compressed instruction before increment.
      mepc += 4;
    } else {
      mepc += 2;
    }
    __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc
}

/* Rewritten interrupt handler */
__attribute__ ((interrupt ("machine")))
void u_sw_irq_handler(void) {

  switch(trap_handler_beh) {

    case M_MODE_BEH : // set Machine mode in the trap handler (4)
      __asm__ volatile("csrrs x0, mstatus, %0" :: "r"(MSTATUS_STD_VAL));
      increment_mepc();
      break;


    case TRAP_INCR_BEH : // csr_privilege_loop behavior (1)
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
  trap_handler_beh = TRAP_INCR_BEH; // setting the trap handler behaviour
  NUM_TRAP_EXECUTIONS = 0; // resetting the trap handler count
  printf("KD: 1.1\n");
  //Enter machine mode:
  set_m_mode();
  printf("KD: 1.2\n");
  //Read secureseed:
  __asm__ volatile("csrrw %0, " STR(CPUADDR_SECURESEED0) ", x0" : "=r"(csr_read));
  assert_or_die(csr_read, 0, "error: secureseed0 is not read as zero\n");
  printf("KD: 1.3\n");
  __asm__ volatile("csrrw %0, " STR(CPUADDR_SECURESEED1) ", x0" : "=r"(csr_read));
  assert_or_die(csr_read, 0, "error: secureseed1 is not read as zero\n");
  printf("KD: 1.4\n");
  __asm__ volatile("csrrw %0, " STR(CPUADDR_SECURESEED2) ", x0" : "=r"(csr_read));
  assert_or_die(csr_read, 0, "error: secureseed2 is not read as zero\n");
  printf("KD: 1.5\n");
}


void test_read_ctrlcpu_and_secureseeds_in_user_mode(void){
  uint32_t csr_read;
  trap_handler_beh = TRAP_INCR_BEH; // setting the trap handler behaviour
  NUM_TRAP_EXECUTIONS = 0; // resetting the trap handler count
  printf("KD: 2.1\n");
  //Enter usermode:
  set_u_mode();
  printf("KD: 2.2\n");
  //Try to read ctrlcpu and secureseed:
  __asm__ volatile("csrrw %0, " STR(CPUADDR_CPUCTRL) ", x0" : "=r"(csr_read));
  printf("KD: 2.3\n");
  __asm__ volatile("csrrs %0, " STR(CPUADDR_CPUCTRL) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrc %0, " STR(CPUADDR_CPUCTRL) ", x0" : "=r"(csr_read));
  printf("KD: 2.4\n");
  __asm__ volatile("csrrw %0, " STR(CPUADDR_SECURESEED0) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrs %0, " STR(CPUADDR_SECURESEED0) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrc %0, " STR(CPUADDR_SECURESEED0) ", x0" : "=r"(csr_read));
  printf("KD: 2.5\n");
  __asm__ volatile("csrrw %0, " STR(CPUADDR_SECURESEED1) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrs %0, " STR(CPUADDR_SECURESEED1) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrc %0, " STR(CPUADDR_SECURESEED1) ", x0" : "=r"(csr_read));
  printf("KD: 2.6\n");
  __asm__ volatile("csrrw %0, " STR(CPUADDR_SECURESEED2) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrs %0, " STR(CPUADDR_SECURESEED2) ", x0" : "=r"(csr_read));
  __asm__ volatile("csrrc %0, " STR(CPUADDR_SECURESEED2) ", x0" : "=r"(csr_read));
  printf("KD: 2.7\n");
  //Number of exceptions should equal number of acesses
  assert_or_die(NUM_TRAP_EXECUTIONS, 4*3, "error: accessing cpuctrl or secureseed_ in usermode does not cause a trap\n");
  printf("KD: 2.8\n");
}


int main(void){
  printf("KD: Read secure seeds in machine mode.\n");;
  printf("KD: 1\n");
  test_read_ctrlcpu_and_secureseeds_in_machine_mode();
  printf("KD: 2\n");
  printf("KD: Go in traps when reading secure seeds in user mode.\n");;
  test_read_ctrlcpu_and_secureseeds_in_user_mode();
  printf("KD: 3\n");

  return EXIT_SUCCESS;
}

#endif