#include "csr.h"

void return_to_machine() {
  char *argv[] = {"return_to_machine"};
  execve("return_to_machine", argv, NULL);
}

inline void set_status_pp(priv_e new_mode) {

  csr_set_mask(mstatus, CSR_MSTATUS_MPP, new_mode);
  asm volatile("la t0, 1f;"
               "csrrw t0, mepc, t0;"
               "mret;"
               "1:");
}

void test_fail() { exit(1); }

void test_pass() { exit(0); }
