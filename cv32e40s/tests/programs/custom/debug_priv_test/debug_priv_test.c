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
** Several smaller directed test-cases asserting proper execution between debug and user mode.
**
*******************************************************************************
*/


#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "corev_uvmt.h"


// Global values to set test_cases for the assembly debug code, or write to global values which the .c code can read and assert

// Written by assembly debug code to signal .c code that debug is exiting.
volatile uint8_t glb_debug_status               = 0;
// Written by main code to set test case in assembly debug code
volatile uint8_t glb_expect_ebreaku_exc         = 0;
// Written by main code to set test case in assembly debug code
volatile uint8_t glb_setmprv_test               = 0;
// Written by main code to set test case in assembly debug code
volatile uint8_t glb_check_prv_test             = 0;
// Written by main code to set test case in assembly debug code
volatile uint8_t glb_check_prv_test_2           = 0;
// Written by main code to set test case in assembly debug code
volatile uint8_t glb_unsupported_mode_test      = 0;
// Written by main code to set test case in assembly debug code
volatile uint8_t glb_ebreaku_one_test           = 0;
// Written by main code to set test case in assembly debug code
volatile uint8_t glb_check_previous_prv_test    = 0;
// Written by assembly debug code. Asserts test case failure
volatile uint8_t glb_unsupported_check_failed   = 0;
// Written by assembly debug code. Asserts test case failure
volatile uint8_t glb_ebreaku_one_check          = 0;
// Written by assembly debug code. Contains dcsr register value
volatile uint32_t glb_check_prv_test_val        = 0;
// Written by assembly debug code. Contains dcsr register value
volatile uint32_t glb_dcsr_register             = 0;

// global variable written while in trap handler. Used to check mcause and mstatus registers in assertions
volatile uint32_t wmcause, wmstatus;
// standard value for the mstatus register
#define MSTATUS_STD_VAL 0x1800
// mstatus.MPRV bit
#define MPRV_BIT 17
// Debug define
#define DEBUG_REQ_CONTROL_REG *((volatile uint32_t *) (CV_VP_DEBUG_CONTROL_BASE))
// external assembly symbol which defines a generous region for user mode execution
extern volatile void setup_pmp();
// external assembly symbol which sets core into user mode.
extern volatile void set_u_mode();
// mstatus.MPP bit-field
int MPP_FIELD [2] = {11, 12};
// dcsr.prv bit-field
int PRV_FIELD [2] = {0, 1};

// declaration of the assert function
static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}

/*
Retuns specific bit-field from [bit_indx_low : bit_indx_high] in register x
*/
unsigned int get_field(unsigned int x, int bit_indx_low, int bit_indx_high){
    int field = ( 1 << ( (bit_indx_high - bit_indx_low) + 1) )  - 1;
    x = (x & (field << bit_indx_low) ) >> bit_indx_low;
    return x;
}


/*
Checks the mepc for compressed instructions and increments appropriately
*/
void increment_mepc(void){
  volatile unsigned int insn, mepc;

    __asm__ volatile("csrrs %0, mepc, x0" : "=r"(mepc)); // read the mepc
    __asm__ volatile("lw %0, 0(%1)" : "=r"(insn) : "r"(mepc)); // read the contents of the mepc pc.
    if ((insn & 0x3) == 0x3) { // check for compressed instruction before increment.
      mepc += 4;
    } else {
      mepc += 2;
    }
    __asm__ volatile("csrrw x0, mepc, %0" :: "r"(mepc)); // write to the mepc
}


// Rewritten interrupt handler
__attribute__ ((interrupt ("machine")))
void u_sw_irq_handler(void) {

    __asm__ volatile("csrrs %0, mcause, x0" : "=r"(wmcause));
    __asm__ volatile("csrrs %0, mstatus, x0" : "=r"(wmstatus));
    __asm__ volatile("csrrw x0, mstatus, %0" :: "r"(MSTATUS_STD_VAL)); // set machine mode
    increment_mepc();
}

// Declaration of the debug struct
typedef union {
  struct {
    unsigned int start_delay      : 15; // 14: 0
    unsigned int rand_start_delay : 1;  //    15
    unsigned int pulse_width      : 13; // 28:16
    unsigned int rand_pulse_width : 1;  //    29
    unsigned int pulse_mode       : 1;  //    30    0 = level, 1 = pulse
    unsigned int value            : 1;  //    31
  } fields;
  unsigned int bits;
}  debug_req_control_t;

/*
When called it starts debug_mode
*/
void run_debug_mode(void) {
  // debug control struct
  debug_req_control_t debug_req_control;
  debug_req_control = (debug_req_control_t) {
    .fields.value            = 1,
    .fields.pulse_mode       = 1, //PULSE Mode
    .fields.rand_pulse_width = 0,
    .fields.pulse_width      = 5,// FIXME: BUG: one clock pulse cause core to lock up
    .fields.rand_start_delay = 0,
    .fields.start_delay      = 200
  };

  // this will initiate debug mode
  DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
  // waits for debug to finish
  while(glb_debug_status != 1){
      ;
  }
  // resets the debug status bit
  glb_debug_status = 0;
}

int main(void){// TODO: test will failed until issue #278 in core-v-verif/cv32e40s is fixed
  setup_pmp();



  // Test start:
  /*
  Have dcsr.ebreaku=0, be in U-mode, execute ebreak, ensure "normal" ebreak behavior and no debug entry.
  */
  assert_or_die(glb_debug_status, 0, "Error: Core was in debug mode before test start!\n");
  set_u_mode();
  asm volatile("ebreak");
  assert_or_die(glb_debug_status, 0, "Error: core unexpectedly entered debug mode!\n");
  assert_or_die(wmcause, 0x3, "Error: Illegal 'ebreak' did not trigger breakpoint exception!\n");



  // Test start:
  /*
  Transition out of D-mode (dret) into U-mode, while mstatus.mprv=1, ensure that when execution continues outside D-mode that mstatus.mprv=0.
  */
  glb_setmprv_test = 1; // flag the MRPRV-test for the debug module.
  run_debug_mode();
  asm volatile("ecall");
  int mprvfield = get_field(wmstatus, MPRV_BIT, MPRV_BIT);
  assert_or_die(mprvfield, 0x0, "Error: MPRV did not change to 0 after Debug --> User mode change! "); // check that MPRV = 0 after debug exit.
  glb_setmprv_test = 0;



  // Test start:
  /*
  Transition out of D-mode, ensure that executions starts in the same privilege mode as was indicated in dcsr.prv (dcsr.prv=M and dcsr.prv=U).
  */
  // First check machine mode.
  glb_check_prv_test = 1;
  run_debug_mode();
  asm volatile("ecall");
  uint32_t check_MPP_bit = get_field(wmstatus, MPP_FIELD[0], MPP_FIELD[1]);
  assert_or_die(check_MPP_bit, 0x3, "Error: previous privilege mode did not match the one set in dcsr.prv before exiting debug mode!\n");
  uint32_t check_prv_bit = get_field(glb_check_prv_test_val, PRV_FIELD[0], PRV_FIELD[1]);
  assert_or_die(check_MPP_bit, check_prv_bit, "Error: previous privilege mode did not match the one set in dcsr.prv before exiting debug mode!\n");
  glb_check_prv_test = 0;

  // Now check user mode.
  glb_check_prv_test_2 = 1;
  run_debug_mode();
  asm volatile("ecall");
  check_MPP_bit = get_field(wmstatus, MPP_FIELD[0], MPP_FIELD[1]);
  assert_or_die(check_MPP_bit, 0x0, "Error: previous privilege mode did not match the one set in dcsr.prv before exiting debug mode!\n");
  check_prv_bit = get_field(glb_check_prv_test_val, PRV_FIELD[0], PRV_FIELD[1]);
  assert_or_die(check_MPP_bit, check_prv_bit, "Error: previous privilege mode did not match the one set in dcsr.prv before exiting debug mode!\n");
  glb_check_prv_test_2 = 0;




  // Test start:
  /*
  Write unsupported modes to dcsr.prv, ensure the value read back is unchanged from the previous value.
  */
  glb_unsupported_mode_test = 1;
  run_debug_mode();
  assert_or_die(glb_unsupported_check_failed, 0, "Error: unsupported privilege_mode was successfully written and then read back from dcsr.prv!\n");
  glb_unsupported_mode_test = 0;



  // TEST WILL FAIL UNTIL dcsr.ebreaku BIT IS IMPLEMENTED!
  // TODO: comment the test back in when the above is resolved.
  // Test start:
  /*
  Have dcsr.ebreaku=1, be in U-mode, execute ebreak, ensure debug entry happens instead of "normal" ebreak behavior.
  */
  /*
  glb_ebreaku_one_test = 1; // make debug mode set dcsr.ebreaku = 0
  run_debug_mode();
  glb_ebreaku_one_test = 0; // shut off flag
  glb_expect_ebreaku_exc = 1; // make debug aware we're coming from u-mode ebreak
  asm volatile("ebreak");
  assert_or_die(glb_ebreaku_one_check , 1, "Error: User mode could not enter Debug mode, even though dcsr.ebreaku == 0 !");
  glb_expect_ebreaku_exc = 0;
 */


  // Test start:
  /*
  Transition into D-mode from M-mode and U-mode, ensure dcsr.prv contains the privilege mode that was running before D-mode.
  */
  // First check machine mode
  asm volatile("ecall"); // trap handler will force machine mode
  glb_check_previous_prv_test = 1;
  run_debug_mode();
  int privilege_mode = get_field(glb_dcsr_register, PRV_FIELD[0], PRV_FIELD[1]);
  assert_or_die(privilege_mode, 0x3, "Error: dcsr.prv does not match previous privilege mode after entering debug mode!\n");

  // Now check user mode
  set_u_mode();
  run_debug_mode();
  privilege_mode = get_field(glb_dcsr_register, PRV_FIELD[0], PRV_FIELD[1]);
  assert_or_die(privilege_mode, 0x0, "Error: dcsr.prv does not match previous privilege mode after entering debug mode!\n");
  glb_check_previous_prv_test = 0;


  return(EXIT_SUCCESS);
}
