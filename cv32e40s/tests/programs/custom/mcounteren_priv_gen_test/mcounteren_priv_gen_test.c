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
** Contains generated tests on U-mode access and privilege instructions.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>
#include "corev_uvmt.h"
#include <stdint.h>
#include "mcounteren_priv_gen_test.h"
// extern and global variable declaration
extern volatile void  setup_pmp();
// assembly function which runs and counts all the illegal instructions and exceptions (respectively)
extern volatile uint32_t mco_loop();
// reads and return the mcounteren register
extern volatile uint32_t Check_mcounteren();
//extern volatile uint8_t gbl_mysignaltothehandler = 0;
volatile uint32_t exception_trap_increment_counter;


// Assert function 
static __inline__ void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}



int main(void){

    setup_pmp(); // set the pmp regions for U-mode.

    volatile unsigned int mcounteren_assert_val;
    mcounteren_assert_val = Check_mcounteren(); // load mcounteren into 'mcounteren_assert_val'
    assert_or_die(mcounteren_assert_val, MCOUNTEREN_DEFAULT_VAL, "error: mcounteren illegitimate value\n"); // assert register is zeroed 
    exception_trap_increment_counter = mco_loop();
    
    // Looks for 0 return value, which means no trapped executions or number of traps exceeded number of illegal excecutions
    if (exception_trap_increment_counter == 0){
      printf("trap count exceeded number of generated instructions or instructions were not generated!\n");
      exit(EXIT_FAILURE);
    }
    // The assert number stems from the 'illegal_mcounteren_loop_gen.py' script. The number is printed in the terminal once writing is complete.
    assert_or_die(exception_trap_increment_counter, ILLEGALLY_GENERATED_INSN, "error: executions based on zeroed mcounteren did not all trap correctly\n");      

}