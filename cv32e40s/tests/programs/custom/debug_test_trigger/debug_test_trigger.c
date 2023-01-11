/*
**
** Copyright 2022 OpenHW Group
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
** Debug trigger test
*******************************************************************************
*/

#include <stdio.h>
#include <stdint.h>
#include "corev_uvmt.h"

// MUST be 31 or less (bit position-1 in result array determines test pass/fail
// status, thus we are limited to 31 tests with this construct.
#define NUM_TESTS 10
#define FAIL    1
#define SUCCESS 0

#define DEBUG_REQ_CONTROL_REG *(volatile int *) CV_VP_DEBUG_CONTROL_BASE
#define DEBUG_SEL_IDLE 0
#define DEBUG_SEL_DISABLE_TRIGGER 1
#define DEBUG_SEL_SETUP_TRIGGER 2

void _debugger_start(void)       __attribute__((section(".debugger")));
void _debugger(void)             __attribute__((section(".debugger")));
volatile void trigger_code(void) __attribute__((optimize("O0"))); // Ensure function call is executed
int  test_instruction_address_trigger(void);

volatile uint32_t mcontrol;

volatile int debug_sel;
volatile int debug_entry_status;


void __attribute__((naked)) _debugger_start(void) {
  __asm__ volatile (R"(cm.push {ra, s0-s11}, -64

                      call ra, _debugger

                      cm.pop {ra, s0-s11}, 64
                      dret)");
}

void _debugger (void) {
  printf("Entered debug\n");


  debug_entry_status = 1;
  switch (debug_sel) {
    case DEBUG_SEL_DISABLE_TRIGGER:
      printf("Disabling trigger\n");
      __asm__ volatile ("csrwi tdata1, 0");
    break;

    case DEBUG_SEL_SETUP_TRIGGER: // Set up trigger
      // Load tdata config csrs
      printf("Setting up triggers csr_write: tdata1 = 0x%08lx csr_write: tdata2 = 0x%08x\n", mcontrol,
                                                                                           (unsigned int) &trigger_code);
      __asm__ volatile (R"(lw   s1,     mcontrol
                           csrw tdata1, s1
                           la   s1,     trigger_code
                           csrw tdata2, s1)");

    break;
  }


}

volatile void trigger_code() {
  __asm__ volatile ("nop");
}

int trigger_test (int expect_trigger_match) {
  // Call trigger_code function, in the case of a trigger match the function is not executed
  debug_entry_status = 0;
  trigger_code();
  printf ("Trigger_test() - Instruction address match debug entry: %d (expected: %d)\n",
          debug_entry_status,   expect_trigger_match);
  return (debug_entry_status == expect_trigger_match) ? SUCCESS : FAIL;
}

int test_instruction_address_trigger () {
  int retval = 0;

  debug_sel = DEBUG_SEL_IDLE;
  retval += trigger_test(0); // Check that we don't have a trigger match before setup

  // Set up trigger
  mcontrol = (6 << 28 | // TYPE = 6
              1 << 27 | // DMODE = 1
              1 << 12 | // ACTION = Enter debug mode
              1 << 6  | // M = Match in machine mode
              1 << 2 ); // EXECUTE = Match on instruction address
  debug_sel = DEBUG_SEL_SETUP_TRIGGER;
  debug_entry_status = 0;
  // Assert debug req
  DEBUG_REQ_CONTROL_REG = (CV_VP_DEBUG_CONTROL_DBG_REQ(0x1)        |
                           CV_VP_DEBUG_CONTROL_REQ_MODE(0x1)       |
                           CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x8) |
                           CV_VP_DEBUG_CONTROL_START_DELAY(0xc8));
  // Wait for debug entry
  while (debug_entry_status == 0);

  debug_sel = DEBUG_SEL_DISABLE_TRIGGER; // Avoid infinite loop

  retval += trigger_test(1);


  return retval;
}


int main(int argc, char *argv[])
{
  int status = 0;

  // Test 0:
  // Expect trigger and return to the same instruction
  // Debugger will clear tdata[2] to avoid re-triggering upon return
  status = test_instruction_address_trigger();

  if (status != 0) {
    printf("Test 0 failed with status: %d\n", status);
    return status;
  }

  // Test 1:
  // Expect trigger with dpc changed in debugger handler to avoid

  printf("Finished \n");

}
