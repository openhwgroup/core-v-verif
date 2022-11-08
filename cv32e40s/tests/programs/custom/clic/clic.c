#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

// MUST be 31 or less
#define NUM_TESTS 6

// Test prototypes - should match uint32_t <name>(uint32_t index)
uint32_t w_mcause_mpp_r_mstatus_mpp(uint32_t index);
uint32_t w_mstatus_mpp_r_mcause_mpp(uint32_t index);
uint32_t w_mcause_mpie_r_mstatus_mpie(uint32_t index);
uint32_t w_mstatus_mpie_r_mcause_mpie(uint32_t index);
uint32_t w_mie_notrap_r_zero(uint32_t index);
uint32_t w_mip_notrap_r_zero(uint32_t index);

uint32_t set_test_status(uint32_t test_no, uint32_t val_prev);
uint32_t run_test(uint32_t (*ptr)(), uint32_t index);
void get_result(uint32_t res);

int main(int argc, char **argv){

  uint32_t (*tests[NUM_TESTS])();
  uint32_t test_res = 0;

  // Add function pointers to new tests here
  tests[0] = w_mcause_mpp_r_mstatus_mpp;
  tests[1] = w_mstatus_mpp_r_mcause_mpp;
  tests[2] = w_mcause_mpie_r_mstatus_mpie;
  tests[3] = w_mstatus_mpie_r_mcause_mpie;
  tests[4] = w_mie_notrap_r_zero;
  tests[5] = w_mip_notrap_r_zero;

  // Run all tests in list above
  printf("\nCLIC Test start\n\n");
  for (int i = 0; i < NUM_TESTS; i++) {
    test_res = set_test_status( run_test( (uint32_t (*)())(*tests[i]), i) , test_res);
  }

  // Report failures
  get_result(test_res);
  return 0;
}

uint32_t set_test_status(uint32_t test_no, uint32_t val_prev){
  uint32_t res;
  res = val_prev | (1 << test_no);
  return res;
}

uint32_t run_test(uint32_t (*ptr)(), uint32_t index) {
  return (*ptr)(index);
}

uint32_t w_mcause_mpp_r_mstatus_mpp(uint32_t index){
  uint8_t test_fail = 0;
  printf("\nTesting write to mcause.mpp, read from mstatus.mpp\n");

  if (test_fail) {
    return index + 1;
  }
  return 0;
}

uint32_t w_mstatus_mpp_r_mcause_mpp(uint32_t index){
  uint8_t test_fail = 0;
  printf("\nTesting write to mstatus.mpp, read from mcause.mpp\n");
  if (test_fail) {
    return index + 1;
  }
  return 0;
}

uint32_t w_mcause_mpie_r_mstatus_mpie(uint32_t index){
  uint8_t test_fail = 0;
  printf("\nTesting write to mcause.mpie, read from mstatus.mpie\n");
  if (test_fail) {
    return index + 1;
  }
  return 0;
}

uint32_t w_mstatus_mpie_r_mcause_mpie(uint32_t index){
  uint8_t test_fail = 0;
  printf("\nTesting write to mstatus.mpie, read from mcause.mpie\n");
  if (test_fail) {
    return index + 1;
  }
  return 0;
}

uint32_t w_mie_notrap_r_zero(uint32_t index){
  uint8_t test_fail = 0;
  printf("\nTesting write to mie, should not trap and readback 0\n");
  if (test_fail) {
    return index + 1;
  }
  return 0;
}

uint32_t w_mip_notrap_r_zero(uint32_t index){
  uint8_t test_fail = 0;
  printf("\nTesting write to mip, should not trap and readback 0\n");
  if (test_fail) {
    return index + 1;
  }
  return 0;
}

void get_result(uint32_t res){
  if (res == 1) {
    printf("ALL PASS\n\n");
    return;
  }
  printf("\nResult: 0x%0lx\n", res);
  for (int i = 1; i <= NUM_TESTS; i++){
    if ((res >> i) & 0x1) {
      printf ("Test %0d failed\n", i-1);
    }
  }
}
