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
** Several tests checking different privilege mode (U and M) accesses and csr behavior.
**
*******************************************************************************
*/


#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "corev_uvmt.h"



// Declaration of assert
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



// Assembly function to setup a generous PMP-region for user mode.
extern volatile void  setup_pmp();
// Assembly function to change privilege-mode based on input (0, 1, 2, 3)
extern volatile void change_exec_mode(int);
// Assembly function to set privilege-mode to user-mode
extern volatile void set_u_mode();
// global values to hold registers for tests
volatile uint32_t mstatus, mscratchg, mie, mip, mcause;
// MPP bit-field
int MPP_FIELD [2] = {11, 12};
// Illegal instruction bit-field
int ILL_ACC_FIELD [2] = {0, 1};
// Tracks the number of trapped executions.
volatile uint32_t NUM_TRAP_EXECUTIONS;

typedef enum {

  READ_MIP,
  EXPECTED_TRAP,
  M_MODE_BEH,
  MSCRATCH_TEST_BEH,
  PRIVILEGE_TEST_BEH,
  TRAP_INCR_BEH
} trap_behavior_t;
// trap handler behavior definitions
volatile trap_behavior_t trap_handler_beh;
// standard value for the mstatus register
#define MSTATUS_STD_VAL 0x1800
// MPRV bit
#define MPRV_BIT 17
// machine mode bit-code b'11
#define M_MODE 0x3
//user mode bit-code b'00
#define U_MODE 0x0
// misa.N bit
#define N_BIT 13
// misa.U bit
#define U_BIT 20
//XS bit in the mstatus register
#define XS_BIT 15
//FS bit in the mstatus register
#define FS_BIT 13
//SD bit in the mstatus register
#define SD_BIT 31
// misa.SPP bit-field
#define SPP_BIT 18
// mstatus.TW bit
#define TW_BIT 21
// mcause ecall code bit-range
#define ECALL_BIT 3
// mcause instruction access fault bit
#define INSN_ACC_BIT 0
// mcause instruction access fault code
#define INSN_ACC_CODE 0x2



/* Checks the mepc for compressed instructions and increments appropriately */
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
  unsigned int mepc, tmstatus;

  switch(trap_handler_beh) {


    case READ_MIP : // read mip, mie, and move on  (6)
      __asm__ volatile("csrrs %0, mip, x0" : "=r"(mip));
      __asm__ volatile("csrrs %0, mie, x0" : "=r"(mie));

      increment_mepc();
      break;


    case EXPECTED_TRAP : // trapping is expected behavior, increment mepc and move on (5)
      increment_mepc();
      break;


    case M_MODE_BEH : // set Machine mode in the trap handler (4)
      __asm__ volatile("csrrs x0, mstatus, %0" :: "r"(MSTATUS_STD_VAL));
      increment_mepc();
      break;


    case MSCRATCH_TEST_BEH : // mscratch_reliable_check test behavior (2)
      __asm__ volatile("csrrs %0, mscratch, x0" : "=r"(mscratchg));
      __asm__ volatile("csrrs x0, mstatus, %0" :: "r"(MSTATUS_STD_VAL)); // set machine mode
      increment_mepc();
      break;


    case PRIVILEGE_TEST_BEH : // privilege_test test behavior (0)
      __asm__ volatile("csrrs %0, mcause, x0" : "=r"(mcause)); // read the mcause register
      __asm__ volatile("csrrs %0, mstatus, x0" : "=r"(mstatus)); // read the mstatus register
      __asm__ volatile("csrrs x0, mstatus, %0" :: "r"(MSTATUS_STD_VAL)); // set machine mode
      increment_mepc();
      break;


    case TRAP_INCR_BEH : // csr_privilege_loop behavior (1)
      NUM_TRAP_EXECUTIONS += 1;
      increment_mepc();
      break;
  }

}

/* Changes the handler functionality, and then calls an exception to change into m-mode. */
void set_m_mode(void) {
  trap_handler_beh = M_MODE_BEH;
  __asm__ volatile("ecall");
}



/*
 * Loops through the different spec modes (00, 01, 10, 11) and asserts that only the implemented modes User (00) and Machine (11) are entered.
 * vplan:SupportedLevels
 */
void privilege_test(void){
  int input_mode = 0;
  trap_handler_beh = PRIVILEGE_TEST_BEH;

  for (int i = 0; i <= 3; i++){
    input_mode = i << 11;

    change_exec_mode(input_mode);
    uint32_t MPP = get_field(mstatus, MPP_FIELD[0], MPP_FIELD[1]);
    if (i == 3) {
        assert_or_die(MPP, M_MODE, "error: core did not enter privilege mode as expected\n");
        }else {
        assert_or_die(MPP, U_MODE, "error: core did not enter privilege mode as expected\n");
      };
  };

}

/*
 * To satisfy the testing criteria this test must run first
 * this is to ensure 'Ensure that M-mode is the first mode entered after reset.
 * vplan:ResetMode
 */
void reset_mode(void){
  __asm__ volatile("csrrs %0, mstatus, x0" : "=r"(mstatus)); // read the mstatus register
  assert_or_die(mstatus, MSTATUS_STD_VAL, "error: core did not enter M-mode after reset\n");
}


/*
 * Try all kinds of access to all implemented U- and M-mode CSR registers while in U- and M-mode (cross), ensure appropriate access grant/deny. (Caveat) There is only one register, JVT.
 * vplan:???
 */
void JVT_cross_privilege(void) {

  NUM_TRAP_EXECUTIONS = 0;
  trap_handler_beh = TRAP_INCR_BEH;
  set_u_mode();
  unsigned int utest;
  __asm__ volatile("csrrs %0, 0x017, x0" : "=r"(utest)); // read
  __asm__ volatile("csrrw x0, 0x017, %0" :: "r"(utest)); // read-modify-write
  __asm__ volatile("csrrs x0, 0x017, %0" :: "r"(utest)); // set
  __asm__ volatile("csrrc x0, 0x017, %0" :: "r"(utest)); // clear
  __asm__ volatile("csrrw x0, 0x017, %0" :: "r"(utest)); // write again to 'reset' the initial value of the register before moving to another test
  assert_or_die(NUM_TRAP_EXECUTIONS, 0, "Some tests seem to have triggered the exception handler, user should have access to this register\n");

}


/*
 * Read misa and assert that "U" bit-field is high and "N" bit-field is low.
 * vplan:MisaU
 * vplan:MisaN
 */
void misa_check(void) {

  set_m_mode();
  unsigned int misa;
  __asm__ volatile("csrrw %0, misa, x0" : "=r"(misa));
  int umode = get_field(misa, U_BIT, U_BIT);
  int reserved = get_field(misa, N_BIT, N_BIT);
  assert_or_die(umode, 1, "error: User-mode not set in the misa register\n");
  assert_or_die(reserved, 0, "error: N-bit set in the misa register\n");

}


/*
 * F-extension, S-mode are not supported on the platform, FS and XS should therefore be 0, and if both of those are 0 then the SD field should also be 0.
 * vplan:UserExtensions
 */
void mstatus_implement_check(void){

  unsigned int mstatus, XS, FS, SD;
  __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus));
  XS = get_field(mstatus, XS_BIT, XS_BIT);
  FS = get_field(mstatus, FS_BIT, FS_BIT);
  SD = get_field(mstatus, SD_BIT, SD_BIT);
  assert_or_die(XS, 0x0, "error: XS set in the mstatus register\n");
  assert_or_die(FS, 0x0, "error: FS set in the mstatus register\n");
  assert_or_die(SD, 0x0, "error: SD set in the mstatus register\n");
}


/*
 * Check that mscratch never changes in U-mode.
 * change to u-mode, attempt to write to mscratch, trap and assert that mscratch is the same.
 * vplan:MscratchReliable
 */
void mscratch_reliable_check(void){

  trap_handler_beh = MSCRATCH_TEST_BEH; // set the exception handler behavior.
  volatile unsigned int mscratch,
  mscratchg = 0; // zero global mscratch value

  __asm__ volatile("csrrs %0, mscratch, x0" : "=r"(mscratch));
  set_u_mode();
  __asm__ volatile("csrrw x0, mscratch, %0" :: "r"(MSTATUS_STD_VAL)); // write to the mscratch (in user mode) (dummy value)
  // mscratchg is read from the trap handler.
  assert_or_die(mscratch, mscratchg, "error: mscratch register changed after attempted user mode read\n");

}

/*
 * Catch-all function for registers which should not exist according to the intern v-plan (Summer 2022) for the cv32e40s core.
 * vplan:NExt
 * vplan:Mcounteren
 * vplan:MedelegMideleg
 */
void csr_should_not_exist_check(void) {

  uint32_t csr_acc, s_mode_bit, misa;
  csr_acc = MSTATUS_STD_VAL; // some std value
  set_m_mode();
  trap_handler_beh = EXPECTED_TRAP; // sets the behavior of the exception handler.
  __asm__ volatile("csrrw %0, misa, x0" : "=r"(misa));
  s_mode_bit = get_field(misa, SPP_BIT, SPP_BIT);
  assert_or_die(s_mode_bit, 0, "error: Supervisor-mode should not be set in the misa register\n");


  trap_handler_beh = TRAP_INCR_BEH; // setting the trap handler behaviour
  NUM_TRAP_EXECUTIONS = 0; // resetting the trap handler count

  //TODO: attempts to Read, Write, Set and Clear all th register

  // mcounteren should exist
  __asm__ volatile("csrrs %0, mcounteren, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, mcounteren, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, mcounteren, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, mcounteren, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, mcounteren, %0" : "=r"(csr_acc)); // write the value back
  assert_or_die(NUM_TRAP_EXECUTIONS, 0, "error: reading the mcounteren register should not trap in M-mode\n");

  /*csrrs  t0, 0x100, x0 Read
    csrrw  x0, 0x100, t0 Write
    csrrs  x0, 0x100, t0 Set
    csrrc  x0, 0x100, t0 Clear */

  // mideleg and medeleg register should not be implemented
  __asm__ volatile("csrrs %0, mideleg, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, mideleg, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, mideleg, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, mideleg, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, medeleg, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, medeleg, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, medeleg, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, medeleg, %0" : "=r"(csr_acc));


  //various N-mode register should not exist anymore.
  __asm__ volatile("csrrs %0, ustatus, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, ustatus, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, ustatus, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, ustatus, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, uie, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, uie, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, uie, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, uie, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, utvec, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, utvec, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, utvec, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, utvec, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, uscratch, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, uscratch, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, uscratch, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, uscratch, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, uepc, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, uepc, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, uepc, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, uepc, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, ucause, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, ucause, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, ucause, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, ucause, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, utval, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, utval, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, utval, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, utval, %0" : "=r"(csr_acc));

  __asm__ volatile("csrrs %0, uip, x0" : "=r"(csr_acc));
  __asm__ volatile("csrrw x0, uip, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrs x0, uip, %0" : "=r"(csr_acc));
  __asm__ volatile("csrrc x0, uip, %0" : "=r"(csr_acc));

  // 10 registers and 4 operations per register
  assert_or_die(NUM_TRAP_EXECUTIONS, 40, "error: some of the unimplemented registers did not trap on instrs attempt\n");
}

/*
 * U-mode interrupts are not supported. The 'zero-bits' in the 'mip' and 'mie' should remain zero.
 * vplan:SoftwareInterrupts
 */
void no_u_traps(void) {
  unsigned int mask, garb, mipr, mier;
  mip = 1; // dummy values for the mip and mie
  mie = 1; // these are both read by the trap handler

  mask = 0xF777; // bit_mask for the mip zero-bits
  trap_handler_beh = READ_MIP; // set trap handler behaviour

  // Core is expected to trap when u-mode tries to read mstatus
  set_u_mode();
  __asm__ volatile("csrrs %0, mstatus, x0" : "=r"(garb)); // illegal read
  mip = mip & mask; // And over the Hardcoded zero bit-fields
  // mie register is supposed  to be 0
  assert_or_die(mie, 0x0, "error: zero-fields in the mier changed after interrrupts\n");
  assert_or_die(mip, 0x0, "error: zero-fields in the mipr changed after interrupts\n");

}


/*
 * Assert that U-mode is set in the MPP after returning from M-mode.
 * vplan:MretLeastPrivileged
 */
void proper_ret_priv(void) {

  uint32_t MPP, MPRV;
  trap_handler_beh = PRIVILEGE_TEST_BEH;
  set_u_mode();
  __asm__ volatile("mret");
  __asm__ volatile("csrrs %0, mstatus, x0" : "=r"(mstatus));
  MPP = get_field(mstatus, MPP_FIELD[0], MPP_FIELD[1]);
  assert_or_die(MPP, 0x0, "error: MPP is not set to least privileged mode after executing mret\n");
  MPRV = get_field(mstatus, MPRV_BIT, MPRV_BIT);
  assert_or_die(MPRV, 0x0, "error: MPRV is not set to 0 after executing mret\n");
}


/*
 * When in U-mode and TW=1 in mstatus, executing a WFI should trap to an illegal exception.
 * vplan:WfiIllegal
 */
void check_wfi_trap(void) {

  trap_handler_beh = PRIVILEGE_TEST_BEH;
  uint32_t set_tw, pmstatus;
  set_tw = 0x200000; // mask for mstatus.TW bit
  set_m_mode();

  //Read add and write back mstatus with the TW bit set high
  __asm__ volatile("csrrs %0, mstatus, x0" : "=r"(mstatus));
  pmstatus = mstatus | set_tw;
  __asm__ volatile("csrrw x0, mstatus, %0" :: "r"(pmstatus));

  // Initiate the trap
  set_u_mode();
  __asm__ volatile("wfi");

  //Assert proper mcause
  int cause = get_field(mcause, 0, 1);
  assert_or_die(cause, 0x2, "error: mcause not showing illegal insn exception after TW WFI trap.\n");
}



/*
 * Be in U-mode, execute ecall, ensure that an exception is taken and mcause is set correctly.
 * vplan:Ecall
 */
void correct_ecall(void) {

  trap_handler_beh = PRIVILEGE_TEST_BEH;
  uint32_t cause;
  set_u_mode();
  __asm__ volatile("ecall");
  cause = get_field(mcause, ECALL_BIT, ECALL_BIT);
  // ECALL_BIT is expected to be high (1)
  assert_or_die(cause, 1, "error: mcause not showing ecall code after U-mode ecall.\n");

}


/*
 * Be in U-mode, execute MRET, ensure that it does not execute like it does in M-mode: Raise illegal exception, priv mode goes to M and not MPP, MPP becomes U, MPRV is unchanged.
 * vplan:Mret
 */
void correct_xret(void) {

  trap_handler_beh = PRIVILEGE_TEST_BEH;
  volatile int MPRV_from_M_mode, mcode, MPP, MPRV_from_U_mode;

  //CHeck MPRV bit while in Machine mode
  __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus));
  MPRV_from_M_mode = get_field(mstatus, MPRV_BIT, MPRV_BIT);

  // Call an illegal MRET
  set_u_mode();
  __asm__ volatile("mret");
  __asm__ volatile("csrrw %0, mstatus, x0" : "=r"(mstatus));

  // Get the MPP and MPRV value after the illegal MRET
  MPP = get_field(mstatus, MPP_FIELD[0], MPP_FIELD[1]);
  MPRV_from_U_mode = get_field(mstatus, MPRV_BIT, MPRV_BIT);
  __asm__ volatile("csrrw %0, mcause, x0" : "=r"(mcause));
  mcode = get_field(mcause, ILL_ACC_FIELD[0], ILL_ACC_FIELD[1]);

  // Assert core behaved like vplan expects
  assert_or_die(MPRV_from_U_mode, MPRV_from_M_mode, "error: MPRV changed state after illegal mret\n");
  assert_or_die(mcode, INSN_ACC_CODE, "error: mcause did not report illegal instruction\n");
  assert_or_die(MPP, 0x0, "error: MPP not set to U-mode after illegal insn.\n");

}

/*
 * Executing uret should give an illegal instruction exception.
 * vplan:Uret
 */
void check_uret(){
  trap_handler_beh = PRIVILEGE_TEST_BEH;
  uint32_t mcode;
  __asm__ volatile("uret");
  mcode = get_field(mcause, ILL_ACC_FIELD[0], ILL_ACC_FIELD[1]);
  assert_or_die(mcode, INSN_ACC_CODE, "error: mcause did not report illegal instrunction after 'uret' call\n");
}


/*
 * Access to all trigger registers should be illegal while the core is in usermode.
 * vplan:TriggersAccess
 */
void access_trigger(){
  trap_handler_beh = TRAP_INCR_BEH;
  NUM_TRAP_EXECUTIONS = 0;
  uint32_t csr_acc; // dummy value holder

  set_u_mode();
  __asm__ volatile("csrrw %0, tselect, x0"      : "=r"(csr_acc));
  __asm__ volatile("csrrw %0, tdata1, x0"       : "=r"(csr_acc));
  __asm__ volatile("csrrw %0, tdata2, x0"       : "=r"(csr_acc));
  __asm__ volatile("csrrw %0, tdata3, x0"       : "=r"(csr_acc));
  __asm__ volatile("csrrw %0, etrigger, x0"     : "=r"(csr_acc));
  __asm__ volatile("csrrw %0, tinfo, x0"        : "=r"(csr_acc));
  __asm__ volatile("csrrw %0, tcontrol, x0"     : "=r"(csr_acc));
  __asm__ volatile("csrrw %0, tinfo, x0"        : "=r"(csr_acc));
  __asm__ volatile("csrrw %0, tcontrol, x0"     : "=r"(csr_acc));
  // there are 9 registers checked
  assert_or_die(NUM_TRAP_EXECUTIONS, 9, "error: not all u-mode attempts to access trigger registers trapped\n");
}

int main(void){

  setup_pmp();

  reset_mode();
  privilege_test();
  // sr_cross_privilege(); // TODO: This test will fail until the JVT-register is implemented.
  misa_check();
  mstatus_implement_check();
  mscratch_reliable_check();
  csr_should_not_exist_check();
  no_u_traps();
  proper_ret_priv();
  check_wfi_trap();
  correct_ecall();
  correct_xret();
  check_uret();

  return EXIT_SUCCESS;
}
