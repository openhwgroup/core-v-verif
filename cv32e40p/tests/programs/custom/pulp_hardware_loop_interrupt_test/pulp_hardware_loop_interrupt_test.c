// Copyright 2020 OpenHW Group
// Copyright 2023 Dolphin Design
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0
// 
// Description : Interrupt during PULP Hardware Loops execution with save/restore
// 

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "pulp_hardware_loop_interrupt_test.h"

volatile uint32_t irq_id                  = 0;
volatile uint32_t irq_id_q[IRQ_NUM];
volatile uint32_t irq_id_q_ptr            = 0;
volatile uint32_t mmcause                 = 0;
volatile uint32_t active_test             = 0;
volatile uint32_t nested_irq              = 0;
volatile uint32_t nested_irq_valid        = 0;
volatile uint32_t in_direct_handler       = 0;
volatile uint32_t nested_hwloop_error     = 0;

uint32_t IRQ_ID_PRIORITY [IRQ_NUM] = {
    FAST15_IRQ_ID   ,
    FAST14_IRQ_ID   ,
    FAST13_IRQ_ID   ,
    FAST12_IRQ_ID   ,
    FAST11_IRQ_ID   ,
    FAST10_IRQ_ID   ,
    FAST9_IRQ_ID    ,
    FAST8_IRQ_ID    ,
    FAST7_IRQ_ID    ,
    FAST6_IRQ_ID    ,
    FAST5_IRQ_ID    ,
    FAST4_IRQ_ID    ,
    FAST3_IRQ_ID    ,
    FAST2_IRQ_ID    ,
    FAST1_IRQ_ID    ,
    FAST0_IRQ_ID    ,
    EXTERNAL_IRQ_ID ,
    SOFTWARE_IRQ_ID ,
    TIMER_IRQ_ID
};

void mstatus_mie_enable() {
    int mie_bit = 0x1 << MSTATUS_MIE_BIT;
    asm volatile("csrrs x0, mstatus, %0" : : "r" (mie_bit));
}

void mm_ram_assert_irq(uint32_t mask, uint32_t cycle_delay) {
    *TIMER_REG_ADDR = mask;
    *TIMER_VAL_ADDR = 1 + cycle_delay;
}

extern void __no_irq_handler();

void nested_hwloop_use() {
    volatile uint32_t in_result = 0, out_result = 0;
    // First stack start, end and count for both hardware loops
    volatile uint32_t start[2], end[2], count[2];    
    asm volatile("csrr %0, 0xCC0" : "=r" (start[0]));
    asm volatile("csrr %0, 0xCC1" : "=r" (end[0]));
    asm volatile("csrr %0, 0xCC2" : "=r" (count[0]));
    asm volatile("csrr %0, 0xCC4" : "=r" (start[1]));
    asm volatile("csrr %0, 0xCC5" : "=r" (end[1]));
    asm volatile("csrr %0, 0xCC6" : "=r" (count[1]));

    asm volatile(".align 4\n\t"
                 "cv.setupi 1, 10, endO_1\n\t"
                 "startO_1:\n\t"
                 "    cv.setupi 0, 10, endZ_1\n\t"
                 "    .option norvc\n\t"
                 "    startZ_1:\n\t"
                 "        addi %0, %0, 1\n\t"
                 "        addi %0, %0, 1\n\t"
                 "        addi %0, %0, 1\n\t"
                 "        addi %0, %0, 1\n\t"
                 "    endZ_1:\n\t"
                 "    addi %1, %1, 2\n\t"
                 "    addi %1, %1, 2\n\t"
                 "    addi %1, %1, 2\n\t"
                 "endO_1:\n\t"
                 : "+r" (in_result), "+r" (out_result));

    if (in_result != 400) nested_hwloop_error++;
    if (out_result != 60) nested_hwloop_error++;

    // Restore from critical section
    asm volatile("add t6, x0, %0\n\t"
                 "cv.start 0, t6\n\t"
                 : : "r" (start[0]));

    asm volatile("add t6, x0, %0\n\t"
                 "cv.end 0, t6\n\t"
                 : : "r" (end[0]));

    asm volatile("add t6, x0, %0\n\t"
                 "cv.count 0, t6\n\t"
                 : : "r" (count[0]));

    asm volatile("add t6, x0, %0\n\t"
                 "cv.start 1, t6\n\t"
                 : : "r" (start[1]));

    asm volatile("add t6, x0, %0\n\t"
                 "cv.end 1, t6\n\t"
                 : : "r" (end[1]));

    asm volatile("add t6, x0, %0\n\t"
                 "cv.count 1, t6\n\t"
                 : : "r" (count[1]));
}

void generic_irq_handler(uint32_t id) {
    asm volatile("csrr %0, mcause": "=r" (mmcause));
    irq_id = id;

    if (active_test == 1) {
        nested_hwloop_use();
    }    
}

void m_software_irq_handler(void) { generic_irq_handler(SOFTWARE_IRQ_ID); }
void m_timer_irq_handler(void) { generic_irq_handler(TIMER_IRQ_ID); }
void m_external_irq_handler(void) { generic_irq_handler(EXTERNAL_IRQ_ID); }
void m_fast0_irq_handler(void) { generic_irq_handler(FAST0_IRQ_ID); }
void m_fast1_irq_handler(void) { generic_irq_handler(FAST1_IRQ_ID); }
void m_fast2_irq_handler(void) { generic_irq_handler(FAST2_IRQ_ID); }
void m_fast3_irq_handler(void) { generic_irq_handler(FAST3_IRQ_ID); }
void m_fast4_irq_handler(void) { generic_irq_handler(FAST4_IRQ_ID); }
void m_fast5_irq_handler(void) { generic_irq_handler(FAST5_IRQ_ID); }
void m_fast6_irq_handler(void) { generic_irq_handler(FAST6_IRQ_ID); }
void m_fast7_irq_handler(void) { generic_irq_handler(FAST7_IRQ_ID); }
void m_fast8_irq_handler(void) { generic_irq_handler(FAST8_IRQ_ID); }
void m_fast9_irq_handler(void) { generic_irq_handler(FAST9_IRQ_ID); }
void m_fast10_irq_handler(void) { generic_irq_handler(FAST10_IRQ_ID); }
void m_fast11_irq_handler(void) { generic_irq_handler(FAST11_IRQ_ID); }
void m_fast12_irq_handler(void) { generic_irq_handler(FAST12_IRQ_ID); }
void m_fast13_irq_handler(void) { generic_irq_handler(FAST13_IRQ_ID); }
void m_fast14_irq_handler(void) { generic_irq_handler(FAST14_IRQ_ID); }
void m_fast15_irq_handler(void) { generic_irq_handler(FAST15_IRQ_ID); }

// A Special version of the SW Handler (vector 0) used in the direct mode
__attribute__((interrupt ("machine"))) void u_sw_direct_irq_handler(void)  {
    in_direct_handler = 1;
    asm volatile("csrr %0, mcause" : "=r" (mmcause));
}

    asm (
        ".global alt_vector_table\n"
        ".option norvc\n"
        ".align 8\n"
        "alt_vector_table:\n"
	    "j u_sw_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j m_software_irq_handler\n"
	    "j __no_irq_handler\n"        
        "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j m_timer_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j m_external_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j __no_irq_handler\n"
	    "j m_fast0_irq_handler\n"
	    "j m_fast1_irq_handler\n"
	    "j m_fast2_irq_handler\n"
	    "j m_fast3_irq_handler\n"
	    "j m_fast4_irq_handler\n"
	    "j m_fast5_irq_handler\n"
	    "j m_fast6_irq_handler\n"
	    "j m_fast7_irq_handler\n"
	    "j m_fast8_irq_handler\n"
	    "j m_fast9_irq_handler\n"
	    "j m_fast10_irq_handler\n"
	    "j m_fast11_irq_handler\n"
	    "j m_fast12_irq_handler\n"
	    "j m_fast13_irq_handler\n"
	    "j m_fast14_irq_handler\n"
	    "j m_fast15_irq_handler\n"
    );

    asm (
        ".global alt_direct_vector_table\n"
        ".option norvc\n"
        ".align 8\n"
        "alt_direct_vector_table:\n"
	    "j u_sw_direct_irq_handler\n"	
    );

    asm (
        ".global alt_direct_ecall_table\n"
        ".option norvc\n"
        ".align 8\n"
        "alt_direct_ecall_table:\n"
        "wfi\n"
	    "j u_sw_irq_handler\n"	
    );

#ifdef FPU
#define MSTATUS_FS_INITIAL 0x00002000

void fp_enable ()
{
  unsigned int fs = MSTATUS_FS_INITIAL;

  asm volatile("csrs mstatus, %0;"
               "csrwi fcsr, 0;"
               "csrs mstatus, %0;"
               : : "r"(fs)
              );
}
#endif

int main(int argc, char *argv[]) {
    int retval;

#ifdef FPU
    // Floating Point enable
    fp_enable();
#endif

    // Test 1
    retval = test1();
    if (retval != EXIT_SUCCESS)
        return retval;

    return EXIT_SUCCESS;
}

    //-------------------------------------------------------------------------------------------------------------------------------------------
    //-------------------------------------------------------------------------------------------------------------------------------------------

// Test 1 will check Hardware loops use inside Interrupt handler
int test1() {
    volatile uint32_t error = 0;
    volatile uint32_t in_result = 0, out_result = 0;
    printf("TEST 1 - TRIGGER ONE IRQ DURING HARDWARE LOOP:\n");

    active_test = 1;

    // Enable all interrupts (MIE and MSTATUS.MIE)
    uint32_t mie = (uint32_t) -1;
    asm volatile("csrw mie, %0" : : "r" (mie));            
    mstatus_mie_enable();

    mm_ram_assert_irq(0x1 << 31, 40);

    asm volatile(".align 4\n\t"
                 "cv.setupi 1, 10, endO_0\n\t"
                 "startO_0:\n\t"
                 "    cv.setupi 0, 10, endZ_0\n\t"
                 "    .option norvc\n\t"
                 "    startZ_0:\n\t"
                 "        addi %0, %0, 1\n\t"
                 "        addi %0, %0, 1\n\t"
                 "        addi %0, %0, 1\n\t"
                 "    endZ_0:\n\t"
                 "    addi %1, %1, 2\n\t"
                 "    addi %1, %1, 2\n\t"
                 "endO_0:\n\t"
                 : "+r" (in_result), "+r" (out_result));

    if (in_result != 300) error++;
    if (out_result != 40) error++;
    if (nested_hwloop_error != 0) error++;
    if (error != 0)
        return ERR_CODE_TEST_1;

    return EXIT_SUCCESS;
}

