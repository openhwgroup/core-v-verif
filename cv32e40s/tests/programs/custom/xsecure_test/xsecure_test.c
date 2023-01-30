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
#define CSRADDR_CPUCTRL     0xBF0
#define CSRADDR_SECURESEED0 0xBF9
#define CSRADDR_SECURESEED1 0xBFA
#define CSRADDR_SECURESEED2 0xBFC



#define CSRADDR_HPMCOUNTER \
X("0xC03") \
X("0xC04") \
X("0xC05") \
X("0xC06") \
X("0xC07") \
X("0xC08") \
X("0xC09") \
X("0xC0A") \
X("0xC0B") \
X("0xC0C") \
X("0xC0D") \
X("0xC0E") \
X("0xC0F") \
X("0xC10") \
X("0xC11") \
X("0xC12") \
X("0xC13") \
X("0xC14") \
X("0xC15") \
X("0xC16") \
X("0xC17") \
X("0xC18") \
X("0xC19") \
X("0xC1A") \
X("0xC1B") \
X("0xC1C") \
X("0xC1D") \
X("0xC1E") \
X("0xC1F")

#define CSRADDR_HPMCOUNTERH \
X("0xC83") \
X("0xC84") \
X("0xC85") \
X("0xC86") \
X("0xC87") \
X("0xC88") \
X("0xC89") \
X("0xC8A") \
X("0xC8B") \
X("0xC8C") \
X("0xC8D") \
X("0xC8E") \
X("0xC8F") \
X("0xC90") \
X("0xC91") \
X("0xC92") \
X("0xC93") \
X("0xC94") \
X("0xC95") \
X("0xC96") \
X("0xC97") \
X("0xC98") \
X("0xC99") \
X("0xC9A") \
X("0xC9B") \
X("0xC9C") \
X("0xC9D") \
X("0xC9E") \
X("0xC9F")

// macros for using defines in inline asm
#define S(x) #x
#define STR(s) S(s)

// global values to hold registers for tests
volatile uint32_t cpuctrl, secureseed0, secureseed1, secureseed2;

int read_ctrlcpu_and_secureseeds_in_user_mode(void);
int read_ctrlcpu_and_secureseeds_in_machine_mode(void);
void csr_should_be_present(void);
void csr_should_not_be_present(void);

// assembly function to setup a generous PMP-region for user mode.
extern volatile void  setup_pmp();
// assembly function to set privilege-mode to user-mode
extern volatile void set_u_mode();

// standard value for the mstatus register
#define MSTATUS_STD_VAL 0x1800

typedef enum {
  M_MODE_BEH,
  TRAP_INCR_BEH,
  UNEXPECTED_IRQ_BEH
} trap_behavior_t;

// trap handler behavior definitions
volatile trap_behavior_t trap_handler_beh = UNEXPECTED_IRQ_BEH;

volatile uint32_t num_trap_executions;
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
      num_trap_executions += 1;
      increment_mepc();
      break;

    // unexpected handler irq (UNEXPECTED_IRQ_BEH and more)
    default:
      unexpected_irq_beh = 1;
  }

}


/////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////


void csr_should_be_present(void){

  uint32_t csr_acc;
  csr_acc = MSTATUS_STD_VAL; // some std value

  trap_handler_beh = TRAP_INCR_BEH; // setting the trap handler behaviour
  num_trap_executions = 0; // resetting the trap handler count

  __asm__ volatile("csrrs %0, mcounteren, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, mcounteren, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, mcounteren, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, mcounteren, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, mcounteren, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, mcycle, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, mcycle, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, mcycle, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, mcycle, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, mcycle, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, mcycleh, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, mcycleh, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, mcycleh, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, mcycleh, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, mcycleh, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, minstret, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, minstret, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, minstret, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, minstret, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, minstret, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, minstreth, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, minstreth, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, minstreth, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, minstreth, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, minstreth, %0" : "=r"(csr_acc));

  assert_or_die(num_trap_executions, 0, "error: reading the mcounteren, mcycle, mcycleh, minstret or minstreth register\n");

  // set the trap handler to go into default mode
  trap_handler_beh = UNEXPECTED_IRQ_BEH;

}
void csr_should_not_be_present(void) {
//
  uint32_t csr_acc;
  csr_acc = MSTATUS_STD_VAL; // some std value

  trap_handler_beh = TRAP_INCR_BEH; // setting the trap handler behaviour
  num_trap_executions = 0; // resetting the trap handler count


  #define X(addr) __asm__ volatile("csrrs %0, " addr ", x0" : "=r"(csr_acc)); \
      __asm__ volatile("csrrw x0, " addr ", %0" : "=r"(csr_acc)); \
      __asm__ volatile("csrrs x0, " addr ", %0" : "=r"(csr_acc)); \
      __asm__ volatile("csrrc x0, " addr ", %0" : "=r"(csr_acc));
  CSRADDR_HPMCOUNTER
  CSRADDR_HPMCOUNTERH
  #undef X

  // test that unimplemented registers results in illegal instructions
  __asm__ volatile("csrrs %0, cycle, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, cycle, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, cycle, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, cycle, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, cycleh, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, cycleh, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, cycleh, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, cycleh, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, instret, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, instret, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, instret, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, instret, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, instreth, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, instreth, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, instreth, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, instreth, %0" : "=r"(csr_acc));

  assert_or_die(num_trap_executions, 16 + 4*2*(32-3), "error: some of the unimplemented registers did not trap on instrs attempt\n");

  // set the trap handler to go into default mode
  trap_handler_beh = UNEXPECTED_IRQ_BEH;
}


void test_secureseeds_shows_zero_at_reads(void){
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
  trap_handler_beh = UNEXPECTED_IRQ_BEH;

}


void test_ctrlcpu_and_secureseeds_accessable_in_machine_mode_only(void){
  uint32_t csr_read;

  // setting the trap handler behaviour
  trap_handler_beh = TRAP_INCR_BEH;

  // resetting the trap handler count
  num_trap_executions = 0;

  // enter user mode:
  set_u_mode();

  // read ctrlcpu and secureseed in machine mode (which should not be successful):
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
  assert_or_die(num_trap_executions, 4*3, "error: accessing cpuctrl or secureseed_ in usermode does not cause a trap\n");

  // resetting the trap handler count
  num_trap_executions = 0;

  // enter machine mode:
  set_m_mode();

  // read ctrlcpu and secureseed in machine mode (which should be successful):

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
  assert_or_die(num_trap_executions, 0, "error: accessing cpuctrl or secureseed_ in machine mode cause a trap\n");

  // set the trap handler to go into default mode
  trap_handler_beh = UNEXPECTED_IRQ_BEH;

}


int main(void){

  unexpected_irq_beh = 0;

  csr_should_be_present();
  csr_should_not_be_present();

  setup_pmp();

  test_secureseeds_shows_zero_at_reads();
  test_ctrlcpu_and_secureseeds_accessable_in_machine_mode_only();

  // check if there was an unexpected irq handler req
  assert_or_die(num_trap_executions, 0, "ASSERT ERROR: unexpected irq handler\n");

  return EXIT_SUCCESS;
}

#endif