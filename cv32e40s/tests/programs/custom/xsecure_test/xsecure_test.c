// Copyright 2023 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

#ifndef __XSECURE_TEST_H__
#define __XSECURE_TEST_H__

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "corev_uvmt.h"

//TODO: functions are copied or based the privilege test code.
//If these functions end up in a common function file, we should adopt this file to use the common functions.


#define CSRADDR_CPUCTRL     0xBF0
#define CSRADDR_SECURESEED0 0xBF9
#define CSRADDR_SECURESEED1 0xBFA
#define CSRADDR_SECURESEED2 0xBFC
#define CSRADDR_CPUCTRL     0xBF0
#define CSRADDR_SECURESEED0 0xBF9
#define CSRADDR_SECURESEED1 0xBFA
#define CSRADDR_SECURESEED2 0xBFC
#define PMPCFG0             0x3A0
#define PMPADDR0            0x3B0


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

void test_ctrlcpu_and_secureseeds_accessable_in_machine_mode_only(void);
void test_secureseeds_show_zero_at_reads(void);
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

// Utility functions:


uint32_t random_num32() {
    volatile uint32_t num = *((volatile int *) CV_VP_RANDOM_NUM_BASE);
    return num;
}

// Declaration of assert
static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}


// Changes the handler functionality, and then calls an exception to change into m-mode.
void set_m_mode(void) {
  trap_handler_beh = M_MODE_BEH;
  __asm__ volatile("ecall");
}


// Checks the mepc for compressed instructions and increments appropriately
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

// Rewritten interrupt handler
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
      unexpected_irq_beh += 1;
  }

}

// Test functions:

void csr_should_be_present(void){

  uint32_t rd;

  trap_handler_beh = TRAP_INCR_BEH; // setting the trap handler behaviour
  num_trap_executions = 0; // resetting the trap handler count

  __asm__ volatile("csrr %0, mcounteren" : "=r"(rd)); //Read to csr_acc
  __asm__ volatile("csrw mcounteren, %0" :: "r"(random_num32())); //Write csr_acc
  __asm__ volatile("csrwi mcounteren, 0xF"); //Write immediate value

  __asm__ volatile("csrr %0, mcycle" : "=r"(rd));
  __asm__ volatile("csrw mcycle, %0" :: "r"(random_num32()));
  __asm__ volatile("csrwi mcycle, 0xF");

  __asm__ volatile("csrr %0, mcycleh" : "=r"(rd));
  __asm__ volatile("csrw mcycleh, %0" :: "r"(random_num32()));
  __asm__ volatile("csrwi mcycleh, 0xF");

  __asm__ volatile("csrr %0, minstret" : "=r"(rd));
  __asm__ volatile("csrw minstret, %0" :: "r"(random_num32()));
  __asm__ volatile("csrwi minstret, 0xF");

  __asm__ volatile("csrr %0, minstreth" : "=r"(rd));
  __asm__ volatile("csrw minstreth, %0" :: "r"(random_num32()));
  __asm__ volatile("csrwi minstreth, 0xF");


  assert_or_die(num_trap_executions, 0, "error: reading the mcounteren, mcycle, mcycleh, minstret or minstreth register\n");

  // set the trap handler to go into default mode
  trap_handler_beh = UNEXPECTED_IRQ_BEH;

}


void csr_should_not_be_present(void) {

  uint32_t rd;

  trap_handler_beh = TRAP_INCR_BEH; // setting the trap handler behaviour
  num_trap_executions = 0; // resetting the trap handler count


  #define X(addr) __asm__ volatile("csrr %0, " addr : "=r"(rd)); \
    __asm__ volatile("csrw " addr ", %0" :: "r"(random_num32())); \
    __asm__ volatile("csrwi " addr ", 0xF");
  CSRADDR_HPMCOUNTER
  CSRADDR_HPMCOUNTERH
  #undef X

  // test that unimplemented registers results in illegal instructions
  __asm__ volatile("csrr %0, cycle" : "=r"(rd));
  __asm__ volatile("csrw cycle, %0" :: "r"(random_num32()));
  __asm__ volatile("csrwi cycle, 0xF");

  __asm__ volatile("csrr %0, cycleh" : "=r"(rd));
  __asm__ volatile("csrw cycleh, %0" :: "r"(random_num32()));
  __asm__ volatile("csrwi cycleh, 0xF");

  __asm__ volatile("csrr %0, instret" : "=r"(rd));
  __asm__ volatile("csrw instret, %0" :: "r"(random_num32()));
  __asm__ volatile("csrwi instret, 0xF");

  __asm__ volatile("csrr %0, instreth" : "=r"(rd));
  __asm__ volatile("csrw instreth, %0" :: "r"(random_num32()));
  __asm__ volatile("csrwi instreth, 0xF");

  assert_or_die(num_trap_executions, 3*4 + 3*2*(32-3), "error: some of the unimplemented registers did not trap on instrs attempt\n");

  // set the trap handler to go into default mode
  trap_handler_beh = UNEXPECTED_IRQ_BEH;
}


void test_secureseeds_show_zero_at_reads(void){
  uint32_t rd;

  // setting the trap handler behaviour
  trap_handler_beh = M_MODE_BEH;

  // resetting the trap handler count
  num_trap_executions = 0;

  // enter machine mode:
  set_m_mode();


  // read secureseed:
  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED0) ", %1" : "=r"(rd) : "r"(random_num32()));
  assert_or_die(rd, 0, "error: secureseed0 is not read as zero\n");

  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED1) ", %1" : "=r"(rd) : "r"(random_num32()));
  assert_or_die(rd, 0, "error: secureseed1 is not read as zero\n");

  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED2) ", %1" : "=r"(rd) : "r"(random_num32()));
  assert_or_die(rd, 0, "error: secureseed2 is not read as zero\n");

  // set the trap handler to go into default mode
  trap_handler_beh = UNEXPECTED_IRQ_BEH;

}


void test_ctrlcpu_and_secureseeds_accessable_in_machine_mode_only(void){
  uint32_t rd;

  // setting the trap handler behaviour
  trap_handler_beh = TRAP_INCR_BEH;

  // resetting the trap handler count
  num_trap_executions = 0;

  // enter user mode:
  set_u_mode();

  // read ctrlcpu and secureseed in user mode (which should not be successful):
  __asm__ volatile("csrrw %0, " STR(CSRADDR_CPUCTRL) ", x0" : "=r"(rd));
  __asm__ volatile("csrrs %0, " STR(CSRADDR_CPUCTRL) ", x0" : "=r"(rd));
  __asm__ volatile("csrrc %0, " STR(CSRADDR_CPUCTRL) ", x0" : "=r"(rd));

  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED0) ", %1" : "=r"(rd) : "r"(random_num32()));
  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED0) ", %1" : "=r"(rd) : "r"(random_num32()));
  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED0) ", %1" : "=r"(rd) : "r"(random_num32()));

  // number of exceptions should equal number of acesses
  assert_or_die(num_trap_executions, 3+3, "error: accessing cpuctrl or secureseed_ in usermode does not cause a trap\n");

  // resetting the trap handler count
  num_trap_executions = 0;

  // enter machine mode:
  set_m_mode();

  // read ctrlcpu and secureseed in machine mode (which should be successful):

  __asm__ volatile("csrrw %0, " STR(CSRADDR_CPUCTRL) ", x0" : "=r"(rd));
  __asm__ volatile("csrrs %0, " STR(CSRADDR_CPUCTRL) ", x0" : "=r"(rd));
  __asm__ volatile("csrrc %0, " STR(CSRADDR_CPUCTRL) ", x0" : "=r"(rd));

  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED0) ", %1" : "=r"(rd) : "r"(random_num32()));

  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED0) ", %1" : "=r"(rd) : "r"(random_num32()));

  __asm__ volatile("csrrw %0, " STR(CSRADDR_SECURESEED0) ", %1" : "=r"(rd) : "r"(random_num32()));

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

  test_secureseeds_show_zero_at_reads();
  test_ctrlcpu_and_secureseeds_accessable_in_machine_mode_only();

  // check if there was an unexpected irq handler req
  assert_or_die(unexpected_irq_beh, 0, "ASSERT ERROR: unexpected irq handler\n");

  return EXIT_SUCCESS;
}

#endif
