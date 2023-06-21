/*
** Copyright 2022 OpenHW Group
**
** SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
** Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
** with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
**                                        https://solderpad.org/licenses/SHL-2.1/
** Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
** an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
** specific language governing permissions and limitations under the License.
*******************************************************************************
**
** Small interrupt test to check that interrupt exceptions are always taken in machine mode.
**
*******************************************************************************
*/


#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include "corev_uvmt.h"


#define TIMER_REG_ADDR       ((volatile uint32_t *) (CV_VP_INTR_TIMER_BASE))
#define TIMER_VAL_ADDR       ((volatile uint32_t *) (CV_VP_INTR_TIMER_BASE + 4))
#define M_ext_intr_bit  11
#define MSTATUS_MIE_BIT 3
#define external_machine_interrupt  0x800
// standard value for the mstatus register
#define MSTATUS_STD_VAL 0x1800

volatile uint32_t mmcause = 0;
volatile uint32_t mmstatus = 0;
volatile uint32_t mmie    = 0;
volatile uint32_t num_taken_interrupts = 0;
// MPP bit-field
volatile int MPP_FIELD [2] = {11, 12};

// Assembly function to setup a generous PMP-region for user mode.
extern volatile void  setup_pmp();
// Assembly function to set privilege-mode to user-mode
extern volatile void set_u_mode();

// Declaration of assert
static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}

/*
Returns specific bit-field from [bit_indx_low : bit_indx_high] in register x
*/
unsigned int get_field(unsigned int x, int bit_indx_low, int bit_indx_high){
    int field = ( 1 << ( (bit_indx_high - bit_indx_low) + 1) )  - 1;
    x = (x & (field << bit_indx_low) ) >> bit_indx_low;
    return x;
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

// example use:  "mm_ram_assert_irq(0x1 << i, 1);"
void mm_ram_assert_irq(uint32_t mask, uint32_t cycle_delay) {
    *TIMER_REG_ADDR = mask;
    *TIMER_VAL_ADDR = 1 + cycle_delay;
}

void mstatus_mie_enable() {
    int mie_bit = 0x1 << MSTATUS_MIE_BIT;
    asm volatile("csrrs x0, mstatus, %0" : : "r" (mie_bit));
}

void mie_enable(uint32_t irq) {
    // Enable the interrupt irq in MIE
    uint32_t mie_bit = 0x1 << irq;
    asm volatile("csrrs x0, mie, %0" : : "r" (mie_bit));
}

typedef enum {
  GET_MSTATUS,
  EXCEPTION_MODE,
} trap_behavior_t;

// trap handler behavior definitions
volatile trap_behavior_t trap_handler_beh;


/*
There is (currently) no way for the hart to know which privilege mode it is executing in, but its possible to use the mstatus to figure out the previous privilege mode.
Therefore the interrupt tests will have the m_external_irq_handler trap into u_sw_irq_handler, in order to see the interrupt handlers privilege.
For the trap tests the trap handler will trap again into itself to see which mode its operating in, a sort of self-policing action.
*/
__attribute__ ((interrupt ("machine")))
void u_sw_irq_handler(void) {
  volatile uint32_t mepc = 0;
    switch(trap_handler_beh) {

      case GET_MSTATUS :
        asm volatile("csrrs %0, mstatus, x0": "=r" (mmstatus));
        // set the mode going forward to machine mode.
        asm volatile("csrrs x0, mstatus, %0" :: "r"(MSTATUS_STD_VAL));
        increment_mepc();
        break;

      case EXCEPTION_MODE :
        __asm__ volatile("csrrs %0, mepc, x0" : "=r"(mepc)); // read the mepc
        trap_handler_beh = GET_MSTATUS;
        asm volatile("ecall");
        __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc
        increment_mepc();
        break;
    }
}

// specific interrupt handler
__attribute__((interrupt ("machine")))
void m_external_irq_handler(void) {
  volatile uint32_t mepc = 0;
  __asm__ volatile("csrrs %0, mepc, x0" : "=r"(mepc)); // read the mepc
  asm volatile("csrrs %0, mcause, x0": "=r" (mmcause));
  // Increment if interrupt
  if (mmcause >> 31) {
    num_taken_interrupts++;
  }

  // ecall to trap handler in order to see previous privilege mode.
  asm volatile("ecall");
  asm volatile("csrrs x0, mstatus, %0" :: "r"(MSTATUS_STD_VAL));
  __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc
  increment_mepc();

}

int main(void) {
    setup_pmp();


    // Test start:
    /*
    Observe traps (interrupts and exceptions) getting triggered while in M-mode and U-mode, ensure the handler always starts in M-mode.
    */
    mstatus_mie_enable();
    mie_enable(M_ext_intr_bit);
    num_taken_interrupts = 0;

    // case 1 user mode interrupt
    trap_handler_beh = GET_MSTATUS;
    set_u_mode();
    mm_ram_assert_irq(external_machine_interrupt, 1);
    while (!mmcause); // wait for interrupt to finish
    assert_or_die(num_taken_interrupts, 1, "Error: No interrupts registered!\n");
    volatile int get_mpp = get_field(mmstatus, 11, 12);
    assert_or_die(get_mpp, 0x3, "Error: Interrupt handler did not execute in machine mode!\n");

    // case 2 user mode exception
    trap_handler_beh = EXCEPTION_MODE;
    set_u_mode();
    asm volatile("ecall");
    get_mpp = get_field(mmstatus, MPP_FIELD[0], MPP_FIELD[1]);
    assert_or_die(get_mpp, 0x3, "Error: Interrupt handler did not execute in machine mode!\n");


    // case 3 machine mode interrupt
    mmcause = 0;
     trap_handler_beh = GET_MSTATUS;
    mm_ram_assert_irq(external_machine_interrupt, 1);
    while (!mmcause); // wait for interrupt to finish
    assert_or_die(num_taken_interrupts, 2, "Error: No interrupts registered!\n");
    get_mpp = get_field(mmstatus,  MPP_FIELD[0], MPP_FIELD[1]);
    assert_or_die(get_mpp, 0x3, "Error: Interrupt handler did not execute in machine mode!\n");


    // case 4 machine mode exception
    trap_handler_beh = EXCEPTION_MODE;
    asm volatile("ecall");
    get_mpp = get_field(mmstatus,  MPP_FIELD[0], MPP_FIELD[1]);
    assert_or_die(get_mpp, 0x3, "Error: Interrupt handler did not execute in machine mode!\n");


    exit(EXIT_SUCCESS);
}
