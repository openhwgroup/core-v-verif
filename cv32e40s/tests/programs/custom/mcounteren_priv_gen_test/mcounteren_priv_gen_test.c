/*
**
** Copyright 2022 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
** https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*******************************************************************************
**
** Contains generated tests on U-mode access and privilege instructions.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>
#include "corev_uvmt.h"
#include <stdint.h>|

// extern and global variable declaration
extern volatile void  setup_pmp();
extern volatile unsigned int mco_loop(), Check_mcounteren();
extern volatile uint8_t gbl_mysignaltothehandler = 0;
volatile uint32_t exception_trap_increment_counter;
const int ZERO = 0x0;

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

    volatile unsigned int mcounter_a_val;
    mcounter_a_val = Check_mcounteren(); // load mcounteren into 'mcounter_a_val'
    assert_or_die(mcounter_a_val, ZERO, "error: mcounteren illegitimate value\n"); // assert register is zeroed 
    exception_trap_increment_counter = mco_loop();
    // The assert number stems from the 'illegal_mcounteren_loop_gen.py' script. The number is printed in the terminal once writing is complete.
    assert_or_die(exception_trap_increment_counter, 32, "error: executions based on zeroed mcounteren did not all trap correctly\n");
}