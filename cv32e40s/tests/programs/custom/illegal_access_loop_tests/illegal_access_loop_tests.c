#include <stdio.h>
#include <stdlib.h>
#include "corev_uvmt.h"
#include <stdint.h>

// extern and global variable declaration
extern volatile void  setup_pmp(), set_u_mode(), illegal_custom();
extern volatile unsigned int illegal_full();

// Declaration of assert 
static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}


int main(void){

    //illegal_custom_loop(); // long test + 60 minutes 
    //csr_privilege_loop();
    unsigned int epp;
    setup_pmp();
    epp = illegal_full();
    printf("This is the epp val: %08X\n", epp);
    exit(EXIT_SUCCESS);
}