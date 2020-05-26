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
volatile int glb_debug_exception_status = 0; // Written by debug code during exception only

// Expectation flags. Raise an error if handler or routine is enterred when not expected,
volatile int glb_expect_illegal_insn    = 0;
volatile int glb_expect_ebreak_handler  = 0;
volatile int glb_expect_debug_entry     = 0;
volatile int glb_expect_debug_exception = 0;


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


// Tag is simply to help debug and determine where the failure came from
void check_debug_status(int tag, int value)
{
  if(glb_debug_status != value){
    printf("ERROR: check_debug_status(%d, %d): Tag=% status=%d, exp=%d \n\n",
           tag, value, tag, glb_debug_status, value);
    TEST_FAILED;
  }
}
void check_debug_exception_status(int tag, int value)
{
  if(glb_debug_exception_status != value){
    printf("ERROR: check_debug_exception_status(%d, %d): Tag=% status=%d, exp=%d \n\n",
           tag, value, tag, glb_debug_exception_status, value);
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
    unsigned int temp,temp1,temp2,temp3;

    debug_req_control_t debug_req_control;
    mstatus_t mstatus, mstatus_cmp;

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
    // Trigger Registers are not accessable due to dmode==DEBUG access only

    // Attempt to access each debug and trigger csr. We should expect an illegal instruction
    // on each access attempt. The illegal instruction will increment the glb_illegal_insn_status.

    // Check Read Access
    temp1 = glb_illegal_insn_status+1;
    // Allow illegal instruction handler to run
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, dcsr"    : "=r"(temp)); // Debug DCSR
    check_illegal_insn_status(1,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, dpc"     : "=r"(temp)); // Debug DPC
    check_illegal_insn_status(2,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, dscratch": "=r"(temp)); // Debug DSCRATCH0
    check_illegal_insn_status(3,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, 0x7b3"   : "=r"(temp)); // Debug DSCRATCH1
    check_illegal_insn_status(4,temp1++);

    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, 0x7a0"   : "=r"(temp)); // Trigger TSELECT
    check_illegal_insn_status(5,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, 0x7a1"   : "=r"(temp)); // Trigger TDATA1
    check_illegal_insn_status(6,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, 0x7a2"   : "=r"(temp)); // Trigger TDATA2
    check_illegal_insn_status(7,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, 0x7a3"   : "=r"(temp)); // Trigger TDATA3
    check_illegal_insn_status(8,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, 0x7a8"   : "=r"(temp)); // Trigger MCONTEXT
    check_illegal_insn_status(9,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, 0x7aa"   : "=r"(temp)); // Trigger SCONTEXT
    check_illegal_insn_status(10,temp1++);

    // ----------------------
    // Check Write Access
    temp = 0xFFFFFFFF;
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrw  dcsr, %0"     : "=r"(temp)); // Debug DCSR     
     check_illegal_insn_status(11,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrw  dpc, %0"      : "=r"(temp)); // Debug DPC      
    check_illegal_insn_status(12,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrw  dscratch, %0" : "=r"(temp)); // Debug DSCRATCH0
    check_illegal_insn_status(13,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrw  0x7b3, %0" : "=r"(temp));    // Debug DSCRATCH1
    check_illegal_insn_status(14,temp1++);

    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrw  0x7a0, %0"     : "=r"(temp)); // Trigger TSELECT
    check_illegal_insn_status(15,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrw  0x7a1, %0"     : "=r"(temp)); // Trigger TDATA1
    check_illegal_insn_status(16,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrw  0x7a2, %0"     : "=r"(temp)); // Trigger TDATA2
    check_illegal_insn_status(17,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrw  0x7a3, %0"     : "=r"(temp)); // Trigger TDATA3
    check_illegal_insn_status(18,temp1++);
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrw  0x7a8, %0"     : "=r"(temp)); // Trigger MCONTEXT
    check_illegal_insn_status(19,temp1++);
     glb_expect_illegal_insn = 1;
   __asm__ volatile("csrw  0x7aa, %0"     : "=r"(temp)); // Trigger SCONTEXT
    check_illegal_insn_status(20,temp1++);
    // Do not expect or allow any more illegal instructions


    mstatus_cmp = (mstatus_t) {
    .fields.mpp   = MACHINE  // 
    };
    if(mstatus_cmp.bits != mstatus.bits) {printf("ERROR: init mstatus mismatch exp=%x val=%x\n",
                                           mstatus_cmp.bits, mstatus.bits); TEST_FAILED;}

    printf("------------------------\n");
    printf(" Test3: check hart ebreak executes ebreak handler but does not execute debugger code\n");
    glb_expect_ebreak_handler = 1;
    asm volatile("c.ebreak");
    check_ebreak_status(32,1);

    //FIXME: complier cannot generate 32 ebreak instruction
    //  Need to test both 16bit and 32bit ebreak instruction

    printf("------------------------\n");
    printf(" Test4: request hardware debugger\n");

    debug_req_control = (debug_req_control_t) {
      .fields.value            = 1,
      .fields.pulse_mode       = 1, //PULSE Mode
      .fields.rand_pulse_width = 0,
      .fields.pulse_width      = 5,// FIXME: BUG: one clock pulse cause core to lock up
      .fields.rand_start_delay = 1,
      .fields.start_delay      = 200
    };
    glb_expect_debug_entry = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;

    glb_hart_status = 4; // Basic test
    while(glb_debug_status != glb_hart_status){
      printf("Wait for Debugger\n");
    }
    check_debug_status(41,glb_hart_status);

    printf("------------------------\n");
    printf(" Test5: have debugger execute ebreak 3 more times\n");

    glb_hart_status = 5;
    glb_expect_debug_entry = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != (5+3)){
      printf("Wait for Debugger\n");
    }
    check_debug_status(51,(5+3));

    printf("------------------------\n");
    printf(" Test6: Test CSR access and default values in debug mode\n");
    glb_hart_status = 6;
    glb_expect_debug_entry = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != glb_hart_status){
      printf("Wait for Debugger\n");
    }
    check_debug_status(61,glb_hart_status);



    printf("------------------------\n");
    printf(" Test7: Test Trigger\n");

    printf("  test7.1: Don't expect trigger\n");
    _trigger_test(0); // 0 = don't expect trigger match

    printf("  test7.2: setup trigger in debugger\n");
    // Setup trigger for _trigger_code function address
    glb_hart_status = 7;
    glb_expect_debug_entry = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != glb_hart_status){
      printf("Wait for Debugger\n");
    }
    check_debug_status(72,glb_hart_status);

    printf("  test7.3: Expect Trigger\n");
    glb_hart_status = 8;
    glb_expect_debug_entry = 1;
    _trigger_test(1); //  trigger match enabled
    // We should have also incremented debug status
    check_debug_status(73,glb_hart_status);


    printf("  test7.4: Disable Trigger\n");
    glb_hart_status = 9;
    glb_expect_debug_entry = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != glb_hart_status){
      printf("Wait for Debugger\n");
    }
    check_debug_status(74,glb_hart_status);
    _trigger_test(0); //  trigger disabled

    // Don't expect to enter debug (debug status stays the same value)
    check_debug_status(75,glb_hart_status);


    printf("------------------------\n");
    printf(" Test10: check hart ebreak executes debugger code\n");
    glb_hart_status = 10;
    glb_expect_debug_entry = 1;
    asm volatile("c.ebreak");
    check_debug_status(33,glb_hart_status);

    printf("------------------------\n");
    printf(" Test11: check illegal csr exception during debug launches debugger exception and no csr modified\n");
    glb_hart_status = 11;
    glb_expect_debug_entry = 1;
    glb_expect_debug_exception = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != glb_hart_status){
      printf("Wait for Debugger\n");
    }
    check_debug_status(111,glb_hart_status);
    check_debug_exception_status(111,glb_hart_status);
    //FIXME TBD BUG : need to update test to check actual csrs not modified.

    printf("------------------------\n");
    printf(" Test12: check ecall exception during debug launches debugger exception and no csr modified\n");
    glb_hart_status = 12;
    glb_expect_debug_entry = 1;
    glb_expect_debug_exception = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != glb_hart_status){
      printf("Wait for Debugger\n");
    }
    check_debug_status(112,glb_hart_status);
    check_debug_exception_status(112,glb_hart_status);
    //FIXME TBD BUG : need to update test to check actual csrs not modified.

    printf("------------------------\n");
    printf(" Test13: check mret during debug launches debugger exception and no csr modified\n");
    glb_hart_status = 13;
    glb_expect_debug_entry = 1;
    glb_expect_debug_exception = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != glb_hart_status){
      printf("Wait for Debugger\n");
    }
    check_debug_status(113,glb_hart_status);
    check_debug_exception_status(113,glb_hart_status);
    //FIXME TBD BUG : need to update test to check actual csrs not modified.

    //--------------------------------
    //return EXIT_FAILURE;
    printf("------------------------\n");
    printf("Finished \n");
    return EXIT_SUCCESS;
}
