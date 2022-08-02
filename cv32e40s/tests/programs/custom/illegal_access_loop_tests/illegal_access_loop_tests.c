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
#include <stdint.h>

// extern and global variable declaration
extern volatile void  setup_pmp();
extern volatile unsigned int illegal_full(), csr_loop(), mco_loop(), Check_mcounteren();
extern volatile int gbl_mysignaltothehandler = 0;

// Declaration of assert 
static __inline__ void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}

void change_m_mode(void) {
  gbl_mysignaltothehandler = 1; // Set trap handler behavior
  __asm__ volatile("ecall");
  gbl_mysignaltothehandler = 0; // reset to avoid looping. 
}

void illegal_custom_loop(void) {
    /* 
    Tests U-mode access to various custom functions which are not yet implemented. Should all trap.
    */
    change_m_mode();
    volatile unsigned int epp = 0;
    epp = illegal_full();
    // The assert number stems from the 'illegal_custom_loop.py' script. The number is printed in the terminal once writing is complete.
    assert_or_die(epp, 131072, "error: not all illegal custom instructions triggered the trap handler\n");
}

void csr_privilege_loop(void) {
    /*  
    Checks Read, Write, Set and Clear privielege on all implemented CSR-registers according to the list in 'csr_privilege_gen.py'
    */
    change_m_mode();
    volatile unsigned int ecc = 0;
    ecc = csr_loop();
    // The assert number stems from the 'csr_privilege_gen.py' script. The number is printed in the terminal once writing is complete.
    assert_or_die(ecc, 12288, "error: not all illegal csr instructions triggered the trap handler\n");
}

void mcounteren_privilege_loop(void) {
    change_m_mode();
    volatile unsigned int emm = 0;
    volatile unsigned int mcounter_a_val;
    mcounter_a_val = Check_mcounteren(); // load mcounteren into 'mcounter_a_val'
    assert_or_die(mcounter_a_val, 0x0, "error: mcounteren illegitimate value\n"); // assert register is zeroed 
    emm = mco_loop();
    // The assert number stems from the 'illegal_mcounteren_loop_gen.py' script. The number is printed in the terminal once writing is complete.
    assert_or_die(emm, 32, "error: executions based on zeroed mcounteren did not all trap correctly\n");
}

int main(void){

    setup_pmp(); // set the pmp regions for U-mode.
    illegal_custom_loop(); // long test, 22 minutes 
    csr_privilege_loop();
    mcounteren_privilege_loop();
}