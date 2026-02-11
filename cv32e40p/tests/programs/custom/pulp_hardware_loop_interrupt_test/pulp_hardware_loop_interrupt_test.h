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

#ifndef __INTERRUPT_TEST_H__
#define __INTERRUPT_TEST_H__

#include <stdint.h>
#include <stdbool.h>

// Enable debug messages, note that this will change test timing
//#define DEBUG_MSG

#define ERR_CODE_TEST_1      1
#define ERR_CODE_TEST_2      2
#define ERR_CODE_TEST_3      3
#define ERR_CODE_TEST_4      4
#define ERR_CODE_TEST_5      5
#define ERR_CODE_TEST_6      6
#define ERR_CODE_TEST_7      7

#define TIMER_REG_ADDR         ((volatile uint32_t *) 0x15000000)  
#define TIMER_VAL_ADDR         ((volatile uint32_t *) 0x15000004) 

#define MSTATUS_MIE_BIT 3

#define MCAUSE_IRQ_MASK 0x1f

#define IRQ_NUM 19
#define IRQ_MASK 0xFFFF0888

#define SOFTWARE_IRQ_ID  3
#define TIMER_IRQ_ID     7
#define EXTERNAL_IRQ_ID  11
#define FAST0_IRQ_ID     16
#define FAST1_IRQ_ID     17
#define FAST2_IRQ_ID     18
#define FAST3_IRQ_ID     19
#define FAST4_IRQ_ID     20
#define FAST5_IRQ_ID     21
#define FAST6_IRQ_ID     22
#define FAST7_IRQ_ID     23
#define FAST8_IRQ_ID     24
#define FAST9_IRQ_ID     25
#define FAST10_IRQ_ID    26
#define FAST11_IRQ_ID    27
#define FAST12_IRQ_ID    28
#define FAST13_IRQ_ID    29
#define FAST14_IRQ_ID    30
#define FAST15_IRQ_ID    31

void mstatus_mie_enable();
void mm_ram_assert_irq(uint32_t mask, uint32_t cycle_delay);
extern void __no_irq_handler();
void nested_hwloop_use();
void generic_irq_handler(uint32_t id);

__attribute__((interrupt ("machine"))) void m_software_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_timer_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_external_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast0_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast1_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast2_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast3_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast4_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast5_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast6_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast7_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast8_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast9_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast10_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast11_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast12_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast13_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast14_irq_handler(void);
__attribute__((interrupt ("machine"))) void m_fast15_irq_handler(void);

// A Special version of the SW Handler (vector 0) used in the direct mode
__attribute__((interrupt ("machine"))) void u_sw_direct_irq_handler(void);

extern void alt_vector_table();
extern void alt_direct_vector_table();
extern void alt_direct_ecall_table();

// Function prototypes for individual tests
int test1();
int test2();
int test3();
int test4();
int test5();
int test6();
int test7();
int test8();
int test9();
int test10();

// Test1 (all irqs in sequence) used in multiple tests so break out implementation
int test1_impl(int direct_mode);

#endif

