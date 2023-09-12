/*
**
** Copyright 2020,2022 OpenHW Group
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
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
volatile int glb_hart_status  = 0; // Written by main code only, read by debug code
volatile int glb_debug_status = 0; // Written by debug code only, read by main code
volatile int glb_ebreak_status = 0; // Written by ebreak code only, read by main code
volatile int glb_illegal_insn_status = 0; // Written by illegal instruction code only, read by main code
volatile int glb_debug_exception_status = 0; // Written by debug code during exception only
volatile int glb_exception_ebreak_status = 0; // Written by main code, read by exception handler
volatile int glb_previous_dpc = 0; // holds last dpc, used for checking correctness of stepping
volatile int glb_step_info = 0; // info to dbg code about actions to take on stepping
volatile int glb_step_count = 0; //  Written by debug code for each time single step is entered

// Expectation flags. Raise an error if handler or routine is enterred when not expected,
// The handler/routine is expected to clear these flags, so this test must set them each time
// and event (such as an illegal instruction, etc.) is triggered.
volatile int glb_expect_illegal_insn    = 0;
volatile int glb_expect_ebreak_handler  = 0;
volatile int glb_expect_debug_entry     = 0;
volatile int glb_expect_debug_exception = 0;
volatile int glb_expect_irq_entry = 0; 
volatile int glb_irq_timeout = 0;
// Counter values
// Checked at start and end of debug code
// Only lower 32 bits checked, as simulation cannot overflow on 32 bits
volatile int glb_mcycle_start = 0;
volatile int glb_mcycle_end = 0;
volatile int glb_minstret_start = 0;
volatile int glb_minstret_end = 0;
// generic loop counter
volatile int wait_cnt = 0;

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
#define TIMER_REG_ADDR         ((volatile uint32_t *) 0x15000000)  
#define TIMER_VAL_ADDR         ((volatile uint32_t *) 0x15000004) 
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

extern void _single_step(int d);
// Tag is simply to help debug and determine where the failure came from
void check_debug_status(int tag, int exp_value)
{
  if(glb_debug_status != exp_value){
    printf("ERROR: check_debug_status(%d, %d): Tag=%d glb_debug_status=%d, exp_value=%d \n\n",
           tag, exp_value, tag, glb_debug_status, exp_value);
    TEST_FAILED;
  }
}
void check_debug_exception_status(int tag, int value)
{
  if(glb_debug_exception_status != value){
    printf("ERROR: check_debug_exception_status(%d, %d): Tag=%d debug_exception_status=%d, exp=%d \n\n",
           tag, value, tag, glb_debug_exception_status, value);
    TEST_FAILED;
  }
}
void check_hart_status(char tag[], int exp_value)
{
  if(glb_hart_status != exp_value){
    printf("ERROR: check_hart_status(\"%s\", %d): Tag=\"%s\", glb_hart_status=%d, exp_value=%d \n\n",
           tag, exp_value, tag, glb_hart_status, exp_value);
    TEST_FAILED;
  }
}
void check_ebreak_status(char tag[], int exp_value)
{
  if(glb_ebreak_status != exp_value){
    printf("ERROR: check_ebreak_status(\"%s\", %d): Tag=\"%s\", glb_ebreak_status=%d, exp_value=%d \n\n",
           tag, exp_value, tag, glb_ebreak_status, exp_value);
    TEST_FAILED;
  }
}
void check_illegal_insn_status(char tag[], int exp_value)
{
  if(glb_illegal_insn_status != exp_value){
    printf("ERROR: check_illegal_insn_status(\"%s\", %d): Tag=\"%s\", illegal_insn_status=%d, exp_value=%d \n\n",
           tag, exp_value, tag, glb_illegal_insn_status, exp_value);
    TEST_FAILED;
  }
}
void delay(int count) {
    for (volatile int d = 0; d < count; d++);
}
void mstatus_mie_enable() {
    int mie_bit = 0x1 << 3;
    asm volatile("csrrs x0, mstatus, %0" : : "r" (mie_bit));
}
void mstatus_mie_disable() {
    int mie_bit = 0x1 << 3;
    asm volatile("csrrc x0, mstatus, %0" : : "r" (mie_bit));
}
void mie_enable_all() {
    uint32_t mie_mask = (uint32_t) -1;
    asm volatile("csrrs x0, mie, %0" : : "r" (mie_mask));
}
void mie_disable_all() {
    uint32_t mie_mask = (uint32_t) -1;
    asm volatile("csrrc x0, mie, %0" : : "r" (mie_mask));
}
void mie_enable(uint32_t irq) {
    // Enable the interrupt irq in MIE
    uint32_t mie_bit = 0x1 << irq;
    asm volatile("csrrs x0, mie, %0" : : "r" (mie_bit));
}
void mie_disable(uint32_t irq) {
    // Disable the interrupt irq in MIE
    uint32_t mie_bit = 0x1 << irq;
    asm volatile("csrrc x0, mie, %0" : : "r" (mie_bit));
}
void mm_ram_assert_irq(uint32_t mask, uint32_t cycle_delay) {
    *TIMER_REG_ADDR = mask;
    *TIMER_VAL_ADDR = 1 + cycle_delay;
}
void counters_enable() {
    // Enable counters mcycle (bit0) and minstret (bit2)
    uint32_t mask = 1<<2 | 1<<0;
    asm volatile("csrrc x0, 0x320, %0" : : "r" (mask));
}

#define MACHINE 3

int main(int argc, char *argv[])
{
    unsigned int temp,temp1,temp2;
    unsigned int expected_illegal_instruction_count;
    debug_req_control_t debug_req_control;
    mstatus_t mstatus, mstatus_cmp;
    counters_enable();
    printf("\nBasic test checking debug functionality.\n");

    printf("------------------------\n");
    printf(" Test1: check initilazation values\n");

    temp1 = 0xFFFFFFFF;
    /* get relevant CSRs and compare init values*/
    __asm__ volatile("csrr %0, mstatus" : "=r"(temp1));
    __asm__ volatile("csrw mstatus, %0 " : "=r"(temp1));
    __asm__ volatile("csrr %0, mstatus" : "=r"(mstatus.bits));
    __asm__ volatile("csrr %0, mie" : "=r"(temp));
    __asm__ volatile("csrw mie, %0 " : "=r"(temp1));
    __asm__ volatile("csrr %0, mie" : "=r"(temp2));
    printf("\tmstats_rval = 0x%0x 0x%0x 0x%0x 0x%0x\n",temp2,mstatus.bits,temp,temp1);

    printf("------------------------\n");
    printf(" Test2: Debug and Trigger CSRs\n");
    check_debug_status(0,0);
    printf("------------------------\n");
    printf(" Test2.1: check access to Debug CSRs\n");
    // debug specifcation 13.2: 4.8 Core Debug Registers are not accessable unless in debug mode

    // Check Write Access of Debug CSRs:
    //    We are _not_ in debug-mode, so each of these writes should invoke
    //    an illegal instruction exception.
    temp = 0xFFFFFFFF;
    expected_illegal_instruction_count = glb_illegal_insn_status+1;
    glb_expect_illegal_insn = 1; // will be reset by Handler
    __asm__ volatile("csrw  dcsr, %0"     : "=r"(temp)); // Debug DCSR
    check_illegal_insn_status("Test 2.1: DCSR write", expected_illegal_instruction_count++);

    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrw  dpc, %0"      : "=r"(temp)); // Debug DPC
    check_illegal_insn_status("Test 2.1: DPC write", expected_illegal_instruction_count++);

    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrw  dscratch, %0" : "=r"(temp)); // Debug DSCRATCH0
    check_illegal_insn_status("Test 2.1: DSCRATCH0 write", expected_illegal_instruction_count++);

    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrw  0x7b3, %0" : "=r"(temp));    // Debug DSCRATCH1
    check_illegal_insn_status("Test 2.1: DSCRATCH1 write", expected_illegal_instruction_count++);

    // Check Read Access of Debug CSRs:
    //    We are _not_ in debug-mode, so each of these reads should invoke
    //    an illegal instruction exception.
    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, dcsr"    : "=r"(temp)); // Debug DCSR
    check_illegal_insn_status("Test 2.1: DCSR read", expected_illegal_instruction_count++);

    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, dpc"     : "=r"(temp)); // Debug DPC
    check_illegal_insn_status("Test 2.1: DPC read", expected_illegal_instruction_count++);

    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, dscratch": "=r"(temp)); // Debug DSCRATCH0
    check_illegal_insn_status("Test 2.1: DSCRATCH0 read", expected_illegal_instruction_count++);

    glb_expect_illegal_insn = 1;
    __asm__ volatile("csrr %0, 0x7b3"   : "=r"(temp)); // Debug DSCRATCH1
    check_illegal_insn_status("Test 2.1: DSCRATCH1 read", expected_illegal_instruction_count++);

    printf("------------------------\n");
    printf(" Test2.2: check write access to Trigger CSRs\n");
    glb_expect_illegal_insn = 0;
    // These writes to Trigger CSRs should be ignored when not in Debug mode.
    temp = 0xFFFFFFFF;
    printf("        - Trigger TSELECT write check (should be ignored)\n");
    __asm__ volatile("csrw  0x7a0, %0"     : "=r"(temp)); // Trigger TSELECT
    printf("        - Trigger TDATA1 write check (should be ignored)\n");
    __asm__ volatile("csrw  0x7a1, %0"     : "=r"(temp)); // Trigger TDATA1
    printf("        - Trigger TDATA2 write check (should be ignored)\n");
    __asm__ volatile("csrw  0x7a2, %0"     : "=r"(temp)); // Trigger TDATA2
    printf("        - Trigger TDATA3 write check (should be ignored)\n");
    __asm__ volatile("csrw  0x7a3, %0"     : "=r"(temp)); // Trigger TDATA3
    // CV32E20 does not implement TINFO, so we expect an illegal instruction
    // expection here.
    glb_expect_illegal_insn = 1;
    printf("        - Trigger TINFO write check (illegal instruction expected)\n");
    __asm__ volatile("csrw  0x7a4, %0"     : "=r"(temp)); // Trigger TINFO
    check_illegal_insn_status("Test 2.2: TINFO read", expected_illegal_instruction_count++);

    // CVE2 does not support the features requiring MCONTEXT or MSCONTEXT, so
    // writes to these CSRs are ignored and reads will always return 0x0.
    glb_expect_illegal_insn = 0;
    printf("        - Trigger MCONTEXT write check (should be ignored)\n");
    __asm__ volatile("csrw  0x7a8, %0"     : "=r"(temp)); // Trigger MCONTEXT
    printf("        - Trigger MSCONTEXT write check (should be ignored)\n");
    __asm__ volatile("csrw  0x7aa, %0"     : "=r"(temp)); // Trigger MSCONTEXT

    printf("------------------------\n");
    printf(" Test2.3: check read access to Trigger CSRs\n");
    // If the above writes were truly ignored, as they should have been,
    // then the following reads should return the Trigger CSR default values.
    printf("        - Trigger TSELECT read check\n");
    __asm__ volatile("csrr %0, 0x7a0"   : "=r"(temp)); // Trigger TSELECT
    if(temp != 0x0){printf("ERROR: TSELET Read\n");TEST_FAILED;}

    printf("        - Trigger TDATA1 read check\n");
    __asm__ volatile("csrr %0, 0x7a1"   : "=r"(temp)); // Trigger TDATA1
    // TBC: does CV32E20 support matching in User Mode?
    //   31:28 type      = 2
    //      27 dmode     = 1
    //   15:12 action    = 1
    //      6  m(achine) = 1
    //      3  u(ser)    = 1
    if(temp !=  (2<<28 | 1<<27 | 1<<12 | 1<<6 | 1<<3)) {
        printf(": ERROR!  Expected 0x2800_1048\n");
        TEST_FAILED;
    }

    printf("        - Trigger TDATA2 read check\n");
    __asm__ volatile("csrr %0, 0x7a2"   : "=r"(temp)); // Trigger TDATA2
    if(temp != 0x0){printf("ERROR: TDATA2 Read\n");TEST_FAILED;}

    printf("        - Trigger TDATA3 read check\n");
    __asm__ volatile("csrr %0, 0x7a3"   : "=r"(temp)); // Trigger TDATA3
    if(temp != 0x0){printf("ERROR: TDATA3 Read\n");TEST_FAILED;}

    // CV32E20 does not implement TINFO, so we expect an illegal instruction
    // expection here.
    glb_expect_illegal_insn = 1;
    printf("        - Trigger TINFO read check (expecting illegal instruction exception)\n");
    __asm__ volatile("csrr %0, 0x7a4"   : "=r"(temp)); // Trigger TINFO
    check_illegal_insn_status("Test 2.3: TINFO read", expected_illegal_instruction_count++);

    // CV32E20 does not implement a CSR at addr 0xea8, so we expect an illegal instruction
    // expection here.
    glb_expect_illegal_insn = 1;
    printf("        - CSR 0xea8 read check (expecting illegal instruction exception)\n");
    __asm__ volatile("csrr %0, 0xea8"   : "=r"(temp)); // non-existant CSR
    check_illegal_insn_status("Test 2.3: Non-existant CSR read", expected_illegal_instruction_count++);

    // CVE2 does not support the features requiring MCONTEXT or MSCONTEXT, so
    // writes to these CSRs are ignored and reads will always return 0x0.
    glb_expect_illegal_insn = 0;
    printf("        - Trigger MCONTEXT read check\n");
    __asm__ volatile("csrr %0, 0x7a8"   : "=r"(temp)); // Trigger MCONTEXT
    if(temp != 0x0){printf("ERROR: MCONTEXT Read\n");TEST_FAILED;}

    glb_expect_illegal_insn = 0;
    printf("        - Trigger MSCONTEXT read check\n");
    __asm__ volatile("csrr %0, 0x7aa"   : "=r"(temp)); // Trigger MSCONTEXT
    if(temp != 0x0){printf("ERROR: MSCONTEXT Read\n");TEST_FAILED;}

    printf("------------------------\n");
    printf(" Test3: EBREAKS\n");
    // Do not expect or allow any more illegal instructions
    glb_expect_illegal_insn = 0;

    mstatus_cmp = (mstatus_t) {
      .fields.mpp = MACHINE
    };
    if(mstatus_cmp.bits != mstatus.bits) {
      printf("ERROR: init mstatus mismatch exp=%x val=%x\n",
               mstatus_cmp.bits, mstatus.bits);
      TEST_FAILED;
    }

    printf("------------------------\n");
    printf(" Test3.1: check hart c.ebreak executes ebreak handler but does not execute debugger code\n");
    glb_expect_ebreak_handler = 1;
    asm volatile("c.ebreak");
    check_ebreak_status("Test 3.1", 1);

    printf("------------------------\n");
    printf(" Test3.2: check hart ebreak executes ebreak handler but does not execute debugger code\n");
    // TBD: why does the handler reset glb_expect_ebreak_handler, but not glb_expect_illegal_insn?
    glb_expect_ebreak_handler = 1;
    asm volatile(".4byte 0x00100073"); // ebreak
    check_ebreak_status("Test 3.2", 2);

    // Control register for the debug_request virtual peripheral
    debug_req_control = (debug_req_control_t) {
      .fields.value            = 1,
      .fields.pulse_mode       = 1, //PULSE Mode
      .fields.rand_pulse_width = 0,
      .fields.pulse_width      = 5,// FIXME: BUG: one clock pulse cause core to lock up
      .fields.rand_start_delay = 0,
      .fields.start_delay      = 200
    };

    printf("------------------------\n");
    printf(" Test4 - Debugger Simple: assert debug_req_i (Halt Request)\n");

    // glb_hart_status == 4 selects the "_debugger_simple" test in debugger.S
    // This test merely checks dcsr and then sets glb_debug_status to glb_hart_status.
    glb_hart_status = 4;
    glb_expect_debug_entry = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != glb_hart_status) {
      printf("   ...Waiting for Halt Request (debug_req_i assertion)...\n");
      if (wait_cnt++ > 10) {
          printf("ERROR! Halt Request did not happen as expected\n");
          TEST_FAILED;
      }
    }
    printf("   ...detected Halt Request.\n");
    check_debug_status(41, glb_hart_status);

    printf("------------------------\n");
    printf(" Test5 - Debugger Ebreak: have debugger execute ebreak 3 times\n");

    // glb_hart_status == 5 selects the "_debugger_ebreak" test in debugger.S
    // This test checks dcsr, sets glb_debug_status to 5 and then calls ebreak
    // three times (once using the compressed version of ebreak), incrementing
    // glb_debug_status each time.
    glb_hart_status = 5;
    glb_expect_debug_entry = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != (glb_hart_status+3)) {
      printf("   ...Waiting for Debugger Ebreak test to complete)...\n");
      if (wait_cnt++ > 10) {
          printf("ERROR! Debugger Ebreak did not return as expected\n");
          TEST_FAILED;
      }
    }
    check_debug_status(51, (glb_hart_status+3)); // redundant

    printf("------------------------\n");
    printf(" Test6 - Debugger CSR: Test CSR access and default values in debug mode\n");
    // glb_hart_status == 6 selects the "_debugger_csr" test in debugger.S
    // The test reads a set of Machine CSRs and all of the Debug and Trigger
    // CSRs (just to check that this works in debug-mode) and also checks the
    // values of DCSR and TDATA1.
    glb_hart_status = 6;
    glb_expect_debug_entry = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;

    while(glb_debug_status != glb_hart_status) {
      printf("   ...Waiting for Debugger CSR test to complete...\n");
      if (wait_cnt++ > 10) {
          printf("ERROR! Debugger CSR test did not return as expected\n");
          TEST_FAILED;
      }
    }
    check_debug_status(61, glb_hart_status); // redundant

    printf("\n Tests 7..9 not implemented\n\n");

    // glb_hart_status == 10 selects the "_debugger_ebreak_entry" test in debugger.S
    // This test reads DCSR to check that the proper cause for entering Debug mode is captured.
    printf("------------------------\n");
    printf(" Test10 - Debugger Ebreak Entry: check hart ebreak executes debugger code\n");
    glb_hart_status = 10;
    glb_expect_debug_entry = 1;
    glb_expect_ebreak_handler = 1;
    asm volatile(".4byte 0x00100073"); //ebreak
    check_debug_status(10, glb_hart_status);

    // glb_hart_status == 11 selects the "_debugger_csr_exception" test in debugger.S
    printf("------------------------\n");
    printf(" Test11: check illegal csr exception during debug launches debugger exception and no csr modified\n");
    // TODO : check CSRs not modified.
    glb_hart_status = 11;
    glb_expect_debug_entry = 1;
    glb_expect_debug_exception = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != glb_hart_status){
      printf("Wait for Debugger\n");
    }
    check_debug_status(111,glb_hart_status);
    check_debug_exception_status(111,glb_hart_status);

    printf("------------------------\n");
    printf(" Test12: check ecall exception during debug launches debugger exception and no csr modified\n");
    // TODO : check CSRs not modified.
    glb_hart_status = 12;
    glb_expect_debug_entry = 1;
    glb_expect_debug_exception = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != glb_hart_status){
      printf("Wait for Debugger\n");
    }
    check_debug_status(112,glb_hart_status);
    check_debug_exception_status(112,glb_hart_status);

//
    printf("------------------------\n");
    printf(" Test13: check mret during debug launches debugger exception and no csr modified\n");
    printf("         TODO: mret has been replaced by ecall in debugger.S\n");
    glb_hart_status = 13;
    glb_expect_debug_entry = 1;
    glb_expect_debug_exception = 1;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    while(glb_debug_status != glb_hart_status) {
      printf("Wait for Debugger\n");
    }
    check_debug_status(113,glb_hart_status);
    check_debug_exception_status(113,glb_hart_status);

    printf("------------------------\n");
    printf(" Test14: Check exception ebreak enters debug mode\n");
    glb_hart_status = 14;
    glb_expect_illegal_insn = 1;
    glb_exception_ebreak_status = 1;
    glb_expect_debug_entry = 1;
    // DCSR read will cause illegal instruction. 
    // Exception routine reads glb_exception_ebreak_status=1 and executes c.ebreak
    __asm__ volatile("csrr %0, dcsr"    : "=r"(temp)); // Debug DCSR
    while(glb_debug_status != glb_hart_status){
        printf("Wait for Debugger\n");
    } 
    check_illegal_insn_status("Test 14", expected_illegal_instruction_count++);
    check_debug_status(114, glb_hart_status);

    printf("\n Test 15 not implemented\n\n");

    printf("----------------------\n");
    printf("Test 16: dret in m-mode causes exception\n");

    glb_expect_illegal_insn = 1;
    __asm__ volatile("dret");
    check_illegal_insn_status("Test 16", expected_illegal_instruction_count++); 

    printf("------------------------\n");
    printf("Test 17: WFI before debug_req_i and WFI in debug mode\n");
    printf("If test hangs, WFI is NOT converted to NOP\n");
    
    glb_expect_debug_entry = 1;
    glb_hart_status = 17;
    // start_delay is set to 200, should get the wfi executing before dbg request is asserted
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    // Execute WFI, when debug is asserted, it will act as NOP and enter debug mode
    // If not, test will hang
    __asm__ volatile("wfi");
    check_debug_status(117, glb_hart_status);
    printf("----------------------\n");
    printf("Checking interrupt, as this is needed by later tests\n");
    // Assert and check irq, as this is needed by some tests.
    mstatus_mie_enable();
    mie_enable(30);
    glb_expect_irq_entry = 1;
    mm_ram_assert_irq(0x40000000, 1);
    while(glb_expect_irq_entry == 1);
    mm_ram_assert_irq(0,0);
    printf("Irq check done\n");
    
    printf("\n Jumping to Test 21\n\n");

    // Check that stoupcount bit (10) in dcsr has no affect
    printf("-------------------------\n");
    printf("Test 21: Setting stopcount bit=1\n");
    glb_expect_debug_entry = 1;
    glb_hart_status = 21;
    
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
     while(glb_debug_status != glb_hart_status){
        printf("Wait for Debugger\n");
    }
    check_debug_status(121, glb_hart_status);

    printf("\n\nTEST DELIBERATELY ENDED PREMATURELY (several tests still outstanding...)\n\n");
    TEST_PASSED;

    printf("------------------------\n");
    printf("Test 18: Single stepping\n");
    glb_hart_status = 18;
    // Run single step code (in single_step.S)
    _single_step(0); 

    // Single step code should generate 2 illegal insn
    temp1++;
    check_illegal_insn_status("Test 18", temp1++);
    check_debug_status(118, glb_hart_status);

    printf("Stepped %d times\n", glb_step_count);    
    printf("------------------------\n");
    printf("Test 19: irq in debug\n");
    glb_hart_status = 19;
    glb_expect_debug_entry = 1;
    // Does not expect irq to be taken while in debug mode
    // but it will be taken when we exit from debug.
    // Timeout added in debug code to check for taken irq or not
    glb_expect_irq_entry = 1;
    DEBUG_REQ_CONTROL_REG=debug_req_control.bits;
   
    while(glb_debug_status != glb_hart_status){
        printf("Wait for Debugger\n");
    } 
   
    check_debug_status(119, glb_hart_status);
    if(glb_irq_timeout != 0) {
        printf("glb_irq_timeout != 0, interrupt taken in debug.\n");
        TEST_FAILED;
    } 
 
    // Test debug req vs irq timing
    printf("-----------------------\n");
    printf("Test 20: Asserting debug_req and irq at the same cycle\n");
    glb_expect_debug_entry = 1;
    glb_expect_irq_entry = 1;
    glb_hart_status = 20;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    // 170 halts on first instuction in interrupt handler
    // 175 gives same timing for interrupt and debug_req_i
    mm_ram_assert_irq(0x40000000, 175+20);
    while(glb_debug_status != glb_hart_status){
        printf("Wait for Debugger\n");
    }
    check_debug_status(120, glb_hart_status);
    // Execute fence instruction in debug
    printf("-----------------------------\n");
    printf("Test 22: Execute fence in debug mode\n");
    glb_expect_debug_entry = 1;
    glb_hart_status = 22;
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    
    while(glb_debug_status != glb_hart_status) {
        printf("Wait for debugger\n");
    }    
    
    check_debug_status(121, glb_hart_status);
    printf("------------------------\n");
    printf("Test 23: trigger match in debug mode with match disabled\n");
    glb_hart_status = 23;
    glb_expect_debug_entry = 1;
    // Request debug
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    
    while(glb_debug_status != glb_hart_status){
        printf("Wait for Debugger\n");
    } 
    
    check_debug_status(123, glb_hart_status);
    printf("------------------------\n");
    printf("Test 24: trigger register access in D-mode\n");
    glb_hart_status = 24;
    glb_expect_debug_entry = 1;
    // Request debug
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    
    while(glb_debug_status != glb_hart_status){
        printf("Wait for Debugger\n");
    } 
    check_debug_status(124, glb_hart_status);
    //--------------------------------
    //return EXIT_FAILURE;
    printf("------------------------\n");
    printf("Finished \n");
    return EXIT_SUCCESS;
}
