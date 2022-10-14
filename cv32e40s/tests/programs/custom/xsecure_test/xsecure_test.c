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
** Directed test for Xsecure        exersizes scenarios
**                                  not likely to becovered by randomly
**                                  generated tests.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

#include "xsecure_test.h"


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

  printf("external interrupt encountered\n");

}



int main(int argc, char *argv[])
{
  failureCount = 0;


  printf("Hello 40s Security. \n");


  if (failureCount) {
    printf("\tERROR: %0u failures detected!\n\n", (uint)failureCount);
    return EXIT_FAILURE;
  }
  else {
    printf("\n");
    return EXIT_SUCCESS;
  }
}