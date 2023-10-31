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
**
** Directed test for Zc extension   exersizes instructions and scenarios
**                                  not likely to becovered by randomly
**                                  generated tests.
**
*******************************************************************************
*/


#ifndef __ZC_TEST_H__
#define __ZC_TEST_H__

#include <stdint.h>
#include <stdbool.h>
#include "corev_uvmt.h"
// Enable debug messages, note that this will change test timing
//#define DEBUG_MSG

#define TIMER_REG_ADDR       ((volatile uint32_t *) (CV_VP_INTR_TIMER_BASE))
#define TIMER_VAL_ADDR       ((volatile uint32_t *) (CV_VP_INTR_TIMER_BASE + 4))
#define EX_IRQ_LINE       11


#define PUSH_RLIST_MIN     4
#define PUSH_RLIST_MAX     15

enum ttype{
  pushpop,
  popret,
  popretz,
  mvsa,
  mvas
};


//       Global Variables                 //
volatile uint32_t ex_traps_entered;
volatile enum ttype test_active;
volatile uint32_t test_instr_num;
volatile uint32_t exp_irq;
volatile uint32_t failureCount;
volatile uint32_t rnd0;
volatile uint32_t rnd1;
volatile uint32_t iteratorVault;
extern volatile uint32_t glb_irq_line;
extern volatile uint32_t glb_irq_delay;


//       Functions from Assebly file      //

// Assembly function to enable interrupts
extern volatile void  enable_all_irq();

void vp_assert_irq(uint32_t mask, uint32_t cycle_delay);
uint32_t vp_random_num(uint32_t upper_bound, uint32_t lower_bound);

__attribute__((interrupt ("machine"))) void m_external_irq_handler(void);

//       End of manual section      //

//Generated test functions
//functions time interrupts to hit atomic part of named instruction type
extern volatile void interrupt_push_pop(uint32_t);
extern volatile void interrupt_popret(uint32_t);
extern volatile void interrupt_popretz(uint32_t);
extern volatile void interrupt_mvsa(uint32_t, uint32_t, uint32_t);
extern volatile void interrupt_mvas(uint32_t, uint32_t, uint32_t);


//Generated list of push/pop instr addresses
#define PUSHPOP_INSTR_SIZE 24

extern uint32_t push_0;
extern uint32_t pop_0;
extern uint32_t push_1;
extern uint32_t pop_1;
extern uint32_t push_2;
extern uint32_t pop_2;
extern uint32_t push_3;
extern uint32_t pop_3;
extern uint32_t push_4;
extern uint32_t pop_4;
extern uint32_t push_5;
extern uint32_t pop_5;
extern uint32_t push_6;
extern uint32_t pop_6;
extern uint32_t push_7;
extern uint32_t pop_7;
extern uint32_t push_8;
extern uint32_t pop_8;
extern uint32_t push_9;
extern uint32_t pop_9;
extern uint32_t push_10;
extern uint32_t pop_10;
extern uint32_t push_11;
extern uint32_t pop_11;

uint32_t pushpop_instr_list[PUSHPOP_INSTR_SIZE] = {
    (uint32_t)&push_0,
    (uint32_t)&pop_0,
    (uint32_t)&push_1,
    (uint32_t)&pop_1,
    (uint32_t)&push_2,
    (uint32_t)&pop_2,
    (uint32_t)&push_3,
    (uint32_t)&pop_3,
    (uint32_t)&push_4,
    (uint32_t)&pop_4,
    (uint32_t)&push_5,
    (uint32_t)&pop_5,
    (uint32_t)&push_6,
    (uint32_t)&pop_6,
    (uint32_t)&push_7,
    (uint32_t)&pop_7,
    (uint32_t)&push_8,
    (uint32_t)&pop_8,
    (uint32_t)&push_9,
    (uint32_t)&pop_9,
    (uint32_t)&push_10,
    (uint32_t)&pop_10,
    (uint32_t)&push_11,
    (uint32_t)&pop_11
};
//Generated list of popret instr addresses
#define POPRET_INSTR_SIZE 12

extern uint32_t popret_0;
extern uint32_t popret_1;
extern uint32_t popret_2;
extern uint32_t popret_3;
extern uint32_t popret_4;
extern uint32_t popret_5;
extern uint32_t popret_6;
extern uint32_t popret_7;
extern uint32_t popret_8;
extern uint32_t popret_9;
extern uint32_t popret_10;
extern uint32_t popret_11;

uint32_t popret_instr_list[POPRET_INSTR_SIZE] = {
    (uint32_t)&popret_0,
    (uint32_t)&popret_1,
    (uint32_t)&popret_2,
    (uint32_t)&popret_3,
    (uint32_t)&popret_4,
    (uint32_t)&popret_5,
    (uint32_t)&popret_6,
    (uint32_t)&popret_7,
    (uint32_t)&popret_8,
    (uint32_t)&popret_9,
    (uint32_t)&popret_10,
    (uint32_t)&popret_11
};
//Generated list of popretz instr addresses
#define POPRETZ_INSTR_SIZE 12

extern uint32_t popretz_0;
extern uint32_t popretz_1;
extern uint32_t popretz_2;
extern uint32_t popretz_3;
extern uint32_t popretz_4;
extern uint32_t popretz_5;
extern uint32_t popretz_6;
extern uint32_t popretz_7;
extern uint32_t popretz_8;
extern uint32_t popretz_9;
extern uint32_t popretz_10;
extern uint32_t popretz_11;

uint32_t popretz_instr_list[POPRET_INSTR_SIZE] = {
    (uint32_t)&popretz_0,
    (uint32_t)&popretz_1,
    (uint32_t)&popretz_2,
    (uint32_t)&popretz_3,
    (uint32_t)&popretz_4,
    (uint32_t)&popretz_5,
    (uint32_t)&popretz_6,
    (uint32_t)&popretz_7,
    (uint32_t)&popretz_8,
    (uint32_t)&popretz_9,
    (uint32_t)&popretz_10,
    (uint32_t)&popretz_11
};
//Generated list of mvsa instr addresses
#define MVSA_INSTR_SIZE 16

extern uint32_t mvsa_0;
extern uint32_t mvsa_1;
extern uint32_t mvsa_2;
extern uint32_t mvsa_3;
extern uint32_t mvsa_4;
extern uint32_t mvsa_5;
extern uint32_t mvsa_6;
extern uint32_t mvsa_7;
extern uint32_t mvsa_8;
extern uint32_t mvsa_9;
extern uint32_t mvsa_10;
extern uint32_t mvsa_11;
extern uint32_t mvsa_12;
extern uint32_t mvsa_13;
extern uint32_t mvsa_14;
extern uint32_t mvsa_15;

uint32_t mvsa_instr_list[MVSA_INSTR_SIZE] = {
    (uint32_t)&mvsa_0,
    (uint32_t)&mvsa_1,
    (uint32_t)&mvsa_2,
    (uint32_t)&mvsa_3,
    (uint32_t)&mvsa_4,
    (uint32_t)&mvsa_5,
    (uint32_t)&mvsa_6,
    (uint32_t)&mvsa_7,
    (uint32_t)&mvsa_8,
    (uint32_t)&mvsa_9,
    (uint32_t)&mvsa_10,
    (uint32_t)&mvsa_11,
    (uint32_t)&mvsa_12,
    (uint32_t)&mvsa_13,
    (uint32_t)&mvsa_14,
    (uint32_t)&mvsa_15
};
//Generated list of mvas instr addresses
#define MVAS_INSTR_SIZE 16

extern uint32_t mvas_0;
extern uint32_t mvas_1;
extern uint32_t mvas_2;
extern uint32_t mvas_3;
extern uint32_t mvas_4;
extern uint32_t mvas_5;
extern uint32_t mvas_6;
extern uint32_t mvas_7;
extern uint32_t mvas_8;
extern uint32_t mvas_9;
extern uint32_t mvas_10;
extern uint32_t mvas_11;
extern uint32_t mvas_12;
extern uint32_t mvas_13;
extern uint32_t mvas_14;
extern uint32_t mvas_15;

uint32_t mvas_instr_list[MVAS_INSTR_SIZE] = {
    (uint32_t)&mvas_0,
    (uint32_t)&mvas_1,
    (uint32_t)&mvas_2,
    (uint32_t)&mvas_3,
    (uint32_t)&mvas_4,
    (uint32_t)&mvas_5,
    (uint32_t)&mvas_6,
    (uint32_t)&mvas_7,
    (uint32_t)&mvas_8,
    (uint32_t)&mvas_9,
    (uint32_t)&mvas_10,
    (uint32_t)&mvas_11,
    (uint32_t)&mvas_12,
    (uint32_t)&mvas_13,
    (uint32_t)&mvas_14,
    (uint32_t)&mvas_15
};
#endif

