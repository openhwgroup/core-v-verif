#include <stdio.h>
#include <stdlib.h>
#include "corev_uvmt.h"
#include <stdint.h>

// extern and global variable declaration
extern volatile void  setup_pmp();
extern volatile unsigned int illegal_full(), csr_loop(), mco_loop();

// Declaration of assert 
static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}

void illegal_custom_loop(void) {
    unsigned int epp;
    setup_pmp();
    epp = illegal_full();
    assert_or_die(epp, 131072, "error: not all illegal custom instructions triggered the trap handler\n");
}

void csr_privilege_loop(void) {
    unsigned int epp;
    setup_pmp();
    epp = csr_loop();
    assert_or_die(epp, 12288, "error: not all illegal csr instructions triggered the trap handler\n");
}

void mcounteren_privilege_loop(void) {
    int epp;
    unsigned int mcounterval;
    __asm__ volatile("csrrw %0, mcounteren, x0" : "=r"(mcounterval)); // zero out the register
    assert_or_die(mcounterval, 0x0, "error: mcounteren illegitimate value\n"); // assert register iss zeroed 
    setup_pmp();
    epp = mco_loop();
    assert_or_die(epp, 32, "error: executions based on zeroed mcounteren did not all trap correctly\n");
}

int main(void){

    //illegal_custom_loop(); // long test, 22 minutes 
    //csr_privilege_loop();
    mcounteren_privilege_loop();
}