/*
**
** Copyright 2020 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*******************************************************************************
**
** Directed test for Zc extension   exersizes instructions and scenarios
**                                  not likely to becovered by randomly
**                                  generated tests.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

#include "zc_test.h"

#define DEBUG_PRINT false

//       Program Functions                //

//trigger interrupt
void vp_assert_irq(uint32_t mask, uint32_t cycle_delay) {
    *TIMER_REG_ADDR = mask;
    *TIMER_VAL_ADDR = 1 + cycle_delay;
}

uint32_t vp_random_num(uint32_t upper_bound, uint32_t lower_bound) {

    if ((upper_bound == 0xFFFFFFFF) && (lower_bound == 0)) {
      printf("ERROR: Illegal input value for function vp_random_num\n");
      printf("upper_bound = 0xFFFFFFFF and lower_bound = 0x0 causes overflow\n");
      exit(EXIT_FAILURE);
    }

    uint32_t random_num = *((volatile uint32_t *) CV_VP_RANDOM_NUM_BASE);
    uint32_t num = (random_num  % (upper_bound - lower_bound + 1)) + lower_bound;
    return num;
}


//       Interrupt Handler              //

// external interrupt handler
__attribute__((interrupt ("machine")))
void m_external_irq_handler(void) {
  volatile uint32_t mepc = 0;
  uint32_t ref = 0;
  //fetching reference
  switch (test_active)
  {
  case pushpop:
    ref = pushpop_instr_list[test_instr_num];
    break;

  case popret:
    ref = popret_instr_list[test_instr_num];
    break;

  case popretz:
    ref = popretz_instr_list[test_instr_num];
    break;

  case mvsa:
    ref = mvsa_instr_list[test_instr_num];
    break;

  case mvas:
    ref = mvas_instr_list[test_instr_num];
    break;

  default:
    printf("\tERROR: unrecognised test_active");
    failureCount += 1;
    break;
  }
  test_instr_num += 1;

  if(DEBUG_PRINT){
    printf("external interrupt encountered\n");
  }
  ex_traps_entered += 1;

  __asm__ volatile("csrrs %0, mepc, x0" : "=r"(mepc));
  if(DEBUG_PRINT){
    printf("returning to mepc: 0x%x \n", (unsigned int)mepc);
    printf("comparing to: 0x%x \n", (unsigned int)ref);
  }

  if(mepc == ref){
    printf("ERROR: illegal interrupt detected on mepc: 0x%x\n", (unsigned int)mepc);
    failureCount += 1;
  } else if(mepc != ref+2){
    printf("ERROR: testbench error detected on mepc: 0x%x\n", (unsigned int)mepc);
    failureCount += 1;
  }

}


static void
test_mva01s_same_register(void)
{
  printf("test_mva01s_same_register: start\n");
  __asm__ volatile(
    "cm.mva01s s2, s2"
    : : : "s2"
  );
  printf("test_mva01s_same_register: done\n");
}


int main(int argc, char *argv[])
{
  exp_irq = 0;
  failureCount = 0;
  ex_traps_entered = 0;
  test_instr_num = 0;


  // Setup

  printf("Enabling irq. \n");

  enable_all_irq();


  // Test: PushPop

  printf("\n\nTesting push/pop instructions. \n");
  test_active = pushpop;

  for (int i = PUSH_RLIST_MIN; i <= PUSH_RLIST_MAX; i++)
  {
    glb_irq_line = 0x1 << EX_IRQ_LINE;
    glb_irq_delay = vp_random_num(i-1, 2);
    if(DEBUG_PRINT){
      printf("\n\ntesting rlist %d, with a delay of %u cycles \n", i, (unsigned int)glb_irq_delay);
    }
    exp_irq += 2;
    interrupt_push_pop(i);
  }


  // Test: Popret

  printf("\n\nTesting popret instructions. \n");
  test_active = popret;
  test_instr_num = 0;

  for (int i = PUSH_RLIST_MIN; i <= PUSH_RLIST_MAX; i++)
  {
    glb_irq_line = 0x1 << EX_IRQ_LINE;
    glb_irq_delay = vp_random_num(i-1, 2);
    if(DEBUG_PRINT){
      printf("\n\ntesting rlist %d, with a delay of %u cycles \n", i, (unsigned int)glb_irq_delay);
    }
    exp_irq += 1;
    interrupt_popret(i);
  }


  // Test: Popretz

  printf("\n\nTesting popretz instructions. \n");
  test_active = popretz;
  test_instr_num = 0;

  for (int i = PUSH_RLIST_MIN; i <= PUSH_RLIST_MAX; i++)
  {
    glb_irq_line = 0x1 << EX_IRQ_LINE;
    glb_irq_delay = vp_random_num(i-1, 2);
    if(DEBUG_PRINT){
      printf("\n\ntesting rlist %d, with a delay of %u cycles \n", i, (unsigned int)glb_irq_delay);
    }
    exp_irq += 1;
    interrupt_popretz(i);
  }


  // Test: Mvsa01

  printf("\n\nTesting mvsa01 instructions. \n");
  test_active = mvsa;
  test_instr_num = 0;
  //creating random values for the target registers
  rnd0 = vp_random_num(0xFFFFFFFE, 0x0);
  rnd1 = vp_random_num(0xFFFFFFFE, 0x0);
  for (int i = 0; i < MVSA_INSTR_SIZE; i++)
  {
    glb_irq_line = 0x1 << EX_IRQ_LINE;
    glb_irq_delay = 3;
    if(DEBUG_PRINT){
      printf("\n\ntesting mvsa case %d, with a delay of %u cycles \n", i, (unsigned int)glb_irq_delay);
    }

    exp_irq += 1;
    iteratorVault = i;
    interrupt_mvsa(i, rnd0, rnd1);
    i = iteratorVault;
  }


  // Test: Mva01s

  printf("\n\nTesting mva01s instructions. \n");

  test_active = mvas;
  test_instr_num = 0;

  //creating random values for the target registers
  rnd0 = vp_random_num(0xFFFFFFFE, 0x0);
  rnd1 = vp_random_num(0xFFFFFFFE, 0x0);

  for (int i = 0; i < MVAS_INSTR_SIZE; i++)
  {
    glb_irq_line = 0x1 << EX_IRQ_LINE;
    glb_irq_delay = 3;
    if(DEBUG_PRINT){
      printf("\n\ntesting mvsa case %d, with a delay of %u cycles \n", i, (unsigned int)glb_irq_delay);
    }

    exp_irq += 1;
    iteratorVault = i;
    interrupt_mvas(i, rnd0, rnd1);
    i = iteratorVault;
  }


  // Test: Mva01s - Same Register (Sanity check of RTL bugfix.)

  test_mva01s_same_register();


  // ErrorCheck & Exit

  if(exp_irq != ex_traps_entered) {
    printf("\tERROR: %u interrupts taken, expected %u", (unsigned int)ex_traps_entered, (unsigned int)exp_irq);
    failureCount += 1;
  }
  else {
    printf("%0u interrupts taken \n", (unsigned int)ex_traps_entered);
  }

  if (failureCount) {
    printf("\tERROR: %0u failures detected!\n\n", (unsigned int)failureCount);
    return EXIT_FAILURE;
  }
  else {
    printf("\n");
    return EXIT_SUCCESS;
  }
}
