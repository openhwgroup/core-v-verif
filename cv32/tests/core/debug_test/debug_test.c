/*
**
** Copyright 2020 OpenHW Group
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
** Basic debugger test. Needs more work and bugs fixed
** It will launch a debug request and have debugger code execute (debugger.S)
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

volatile int glb_hart_status  = 0; // Written by main code only, read by debug code
volatile int glb_debug_status = 0; // Written by debug code only, read by main code
volatile int glb_ebreak_status = 0; // Written by ebreak code only, read by main code
volatile int glb_illegal_insn_status = 0; // Written by illegal instruction code only, read by main code
volatile int glb_expect_illegal_insn = 0;
volatile int glb_expect_ebreak_handler = 0;


#define TEST_FAILED  *(volatile int *)0x20000000 = 1
#define TEST_PASSED  *(volatile int *)0x20000000 = 123456789

extern int __stack_start; 

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

#define DEBUG_REQ_CONTROL_REG *(volatile int *)0x15000008



typedef union {
  struct {
    unsigned int uie   : 1;  //     0 // Implemented if USER mode enabled
    unsigned int sie   : 1;  //     1
    unsigned int wpri  : 1;  //     2
    unsigned int mie   : 1;  //     3 // Implemented
    unsigned int upie  : 1;  //     4 // Implemented if USER mode enabled
    unsigned int spie  : 1;  //     5
    unsigned int wpri0 : 1;  //     6
    unsigned int mpie  : 1;  //     7 // Implemented
    unsigned int spp   : 1;  //     8
    unsigned int wpri1 : 2;  // 10: 9
    unsigned int mpp   : 2;  // 12:11 // Implemented
    unsigned int fs    : 2;  // 14:13
    unsigned int xs    : 2;  // 16:15
    unsigned int mprv  : 1;  //    17
    unsigned int sum   : 1;  //    18
    unsigned int mxr   : 1;  //    19
    unsigned int tvm   : 1;  //    20
    unsigned int tw    : 1;  //    21
    unsigned int tsr   : 1;  //    22
    unsigned int wpri3 : 8;  // 30:23
    unsigned int sd    : 1;  //    31
  } fields;
  unsigned int bits;
}  mstatus_t;

typedef union {
  struct {
    unsigned int prv       : 2; //  1: 0
    unsigned int step      : 1; //     2
    unsigned int nmip      : 1; //     3
    unsigned int mprven    : 1; //     4
    unsigned int rsvd5     : 1; //     5
    unsigned int cause     : 3; //  8: 6
    unsigned int stoptime  : 1; //     9
    unsigned int stopcount : 1; //    10
    unsigned int stepie    : 1; //    11
    unsigned int ebreaku   : 1; //    12
    unsigned int ebreaks   : 1; //    13
    unsigned int rsvd14    : 1; //    14
    unsigned int ebreakm   : 1; //    15
    unsigned int rsvd27_16 :12; // 27:16
    unsigned int xdebugver : 4; // 31:28
  } fields;
  unsigned int bits;
}  dcsr_t;

// Tag is simply to help debug and determine where the failure came from
void check_debug_status(int tag, int value)
{
  if(glb_debug_status != value){
    printf("ERROR: check_debug_status(%d, %d): Tag=% status=%d, exp=%d \n\n",
           tag, value, tag, glb_debug_status, value);
    TEST_FAILED;
  }
}
void check_hart_status(int tag, int value)
{
  if(glb_hart_status != value){
    printf("ERROR: check_hart_status(%d, %d): Tag=% status=%d, exp=%d \n\n",
           tag, value, tag, glb_hart_status, value);
    TEST_FAILED;
  }
}
void check_ebreak_status(int tag, int value)
{
  if(glb_ebreak_status != value){
    printf("ERROR: check_ebreak_status(%d, %d): Tag=% status=%d, exp=%d \n\n",
           tag, value, tag, glb_ebreak_status, value);
    TEST_FAILED;
  }
}
void check_illegal_insn_status(int tag, int value)
{
  if(glb_illegal_insn_status != value){
    printf("ERROR: check_illegal_insn_status(%d, %d): Tag=% status=%d, exp=%d \n\n",
           tag, value, tag, glb_illegal_insn_status, value);
    TEST_FAILED;
  }
}


#define MACHINE 3
int main(int argc, char *argv[])
{
   //dcsr_cmp = (dcsr_t) {
   //  .fields.prv       = MACHINE, // Privelege Machine Level
   //  .fields.xdebugver = 4        // External debug support matches version 13.2
   //};
    //FIXME: BUG: bug xdebugver: if(dcsr_cmp.bits != dcsr.bits) {printf("ERROR: init dcsr mismatch exp=%x val=%x\n",
    //               dcsr_cmp.bits, dcsr.bits); TEST_FAILED;}
  //   dcsr_t dcsr, dcsr_cmp;
  // __asm__ volatile("csrr %0, dcsr"    : "=r"(dcsr.bits));

    unsigned int temp,temp1,temp2,temp3;

    debug_req_control_t debug_req_control;
    mstatus_t mstatus, mstatus_cmp;
    dcsr_t dcsr, dcsr_cmp;

    printf("\nBasic test checking debug functionality.\n");

    printf("------------------------\n");
    printf(" Test1: check initilazation values\n");
    //check_debug_status(0,0);

    temp1 = 0xFFFFFFFF;
    /* get relevant CSRs and compare init values*/
    __asm__ volatile("csrr %0, mstatus" : "=r"(temp1));
    __asm__ volatile("csrw mstatus, %0 " : "=r"(temp1));
    __asm__ volatile("csrr %0, mstatus" : "=r"(mstatus.bits));
    __asm__ volatile("csrr %0, mie" : "=r"(temp));
    __asm__ volatile("csrw mie, %0 " : "=r"(temp1));
    __asm__ volatile("csrr %0, mie" : "=r"(temp1));
    printf("\tmstats_rval = 0x%0x 0x%0x 0x%0x 0x%0x\n",temp2,mstatus.bits,temp,temp1);
    
    check_debug_status(0,0);
    printf("------------------------\n");
    printf(" Test2: check access to Debug and Trigger registers\n");
    // debug specifcation 13.2: 4.8 Core Debug Registers are not accessable unless in debug mode
    // debug specifcation 13.2: 5.2 Trigger Registers are not accessable unless in debug mode and machine mode

    // Attempt to access each debug and trigger csr. We should expect an illegal instruction
    // on each access attempt. The illegal instruction will increment the glb_illegal_insn_status.

    // Check Read Access
    temp1 = glb_illegal_insn_status+1;
    // Allow illegal instruction handler to run
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, dcsr"    : "=r"(temp)); // Debug DCSR
    check_illegal_insn_status(1,temp1++);
    __asm__ volatile("csrr %0, dpc"     : "=r"(temp)); // Debug DPC
    check_illegal_insn_status(2,temp1++);
    __asm__ volatile("csrr %0, dscratch": "=r"(temp)); // Debug DSCRATCH0
    check_illegal_insn_status(3,temp1++);
    __asm__ volatile("csrr %0, 0x7b3"   : "=r"(temp)); // Debug DSCRATCH1
    check_illegal_insn_status(4,temp1++);

    __asm__ volatile("csrr %0, 0x7a0"   : "=r"(temp)); // Trigger TSELECT
    check_illegal_insn_status(5,temp1++);
    __asm__ volatile("csrr %0, 0x7a1"   : "=r"(temp)); // Trigger TDATA1
    check_illegal_insn_status(6,temp1++);
    __asm__ volatile("csrr %0, 0x7a2"   : "=r"(temp)); // Trigger TDATA2
    check_illegal_insn_status(7,temp1++);
    __asm__ volatile("csrr %0, 0x7a3"   : "=r"(temp)); // Trigger TDATA3
    check_illegal_insn_status(8,temp1++);
    __asm__ volatile("csrr %0, 0x7a8"   : "=r"(temp)); // Trigger MCONTEXT
    check_illegal_insn_status(9,temp1++);
    __asm__ volatile("csrr %0, 0x7aa"   : "=r"(temp)); // Trigger SCONTEXT
    check_illegal_insn_status(10,temp1++);

    // ----------------------
    // Check Write Access
    temp = 0xFFFFFFFF;
    __asm__ volatile("csrw  dcsr, %0"     : "=r"(temp)); // Debug DCSR     
     check_illegal_insn_status(11,temp1++);
    __asm__ volatile("csrw  dpc, %0"      : "=r"(temp)); // Debug DPC      
    check_illegal_insn_status(12,temp1++);
    __asm__ volatile("csrw  dscratch, %0" : "=r"(temp)); // Debug DSCRATCH0
    check_illegal_insn_status(13,temp1++);
    __asm__ volatile("csrw  0x7b3, %0" : "=r"(temp));    // Debug DSCRATCH1
    check_illegal_insn_status(14,temp1++);

    __asm__ volatile("csrw  0x7a0, %0"     : "=r"(temp)); // Trigger TSELECT
    check_illegal_insn_status(15,temp1++);
    __asm__ volatile("csrw  0x7a1, %0"     : "=r"(temp)); // Trigger TDATA1
    check_illegal_insn_status(16,temp1++);
    __asm__ volatile("csrw  0x7a2, %0"     : "=r"(temp)); // Trigger TDATA2
    check_illegal_insn_status(17,temp1++);
    __asm__ volatile("csrw  0x7a3, %0"     : "=r"(temp)); // Trigger TDATA3
    check_illegal_insn_status(18,temp1++);
    __asm__ volatile("csrw  0x7a8, %0"     : "=r"(temp)); // Trigger MCONTEXT
    check_illegal_insn_status(19,temp1++);
    __asm__ volatile("csrw  0x7aa, %0"     : "=r"(temp)); // Trigger SCONTEXT
    check_illegal_insn_status(20,temp1++);
    // Do not expect or allow any more illegal instructions
    glb_expect_illegal_insn = 0;


    mstatus_cmp = (mstatus_t) {
    .fields.mpp   = MACHINE  // 
    };
    if(mstatus_cmp.bits != mstatus.bits) {printf("ERROR: init mstatus mismatch exp=%x val=%x\n",
                                           mstatus_cmp.bits, mstatus.bits); TEST_FAILED;}

    printf("------------------------\n");
    printf(" Test3: check hart ebreak executes ebreak handler but does not execute debugger code\n");
    check_debug_status(31,0);
    glb_expect_ebreak_handler = 1;
    asm volatile("c.ebreak");
    glb_expect_ebreak_handler = 0;
    check_ebreak_status(32,1);
    check_debug_status(33,0);

    //FIXME: complier cannot generate 32 ebreak instruction
    //  Need to test both 16bit and 32bit ebreak instruction

    printf("------------------------\n");
    printf(" Test4: request hardware debugger\n");

    glb_hart_status = 4; // Basic test
    debug_req_control = (debug_req_control_t) {
      .fields.value            = 1,
      .fields.pulse_mode       = 1, //PULSE Mode
      .fields.rand_pulse_width = 0,
      .fields.pulse_width      = 5,// FIXME: BUG: one clock pulse cause core to lock up
      .fields.rand_start_delay = 1,
      .fields.start_delay      = 200
    };
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;

    while(!glb_debug_status){
      printf("Wait for Debugger\n");
    }
    check_debug_status(41,1);

    printf("------------------------\n");
    printf(" Test5: have debugger execute ebreak 3 more times\n");

    glb_hart_status = 5;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != 4){
      printf("Wait for Debugger\n");
    }
    check_debug_status(41,4);
    check_ebreak_status(35,1);

    printf("------------------------\n");
    printf(" Test6: Test CSR access and default values in debug mode\n");
    glb_hart_status = 6;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != 5){
      printf("Wait for Debugger\n");
    }
    check_debug_status(61,5);

    printf("------------------------\n");
    printf(" Test7: Test Trigger\n");
    glb_hart_status = 7;

    printf("  test7.1: Don't expect trigger\n");
    _trigger_test(0); // don't expect trigger match

    printf("  test7.2: setup trigger in debugger\n");
    // Setup trigger for _trigger_code function address
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != 6){
      printf("Wait for Debugger\n");
    }
    check_debug_status(72,6);

    printf("  test7.3: Expect Trigger\n");
    glb_hart_status = 8;
    _trigger_test(1); //  trigger match enabled
    // We should have also incremented debug status
    check_debug_status(73,7);


    printf("  test7.4: Disable Trigger\n");
    glb_hart_status = 9;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != 8){
      printf("Wait for Debugger\n");
    }
    check_debug_status(74,8);
    _trigger_test(0); //  trigger disabled

    // Don't expect to enter debug (debug status stays the same value)
    check_debug_status(75,8);

    //--------------------------------
    //return EXIT_FAILURE;
    printf("------------------------\n");
    printf("Finished \n");
    return EXIT_SUCCESS;
}
