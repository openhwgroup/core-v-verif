// Copyright 2022 Silicon Labs, Inc.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you
// may not use this file except in compliance with the License, or, at your
// option, the Apache License version 2.0.
//
// You may obtain a copy of the License at
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.


#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include "bsp.h"

#define CSRADDR_CPUCTRL     0xBF0
#define CSRADDR_SECURESEED0 0xBF9
#define CSRADDR_SECURESEED1 0xBFA
#define CSRADDR_SECURESEED2 0xBFC

// Macros for using defines in inline asm
#define S(x) #x
#define STR(s) S(s)


volatile uint32_t  g_got_illegal_instruction_exception;
volatile uint32_t  g_got_trap;


__attribute__((interrupt("machine")))
void u_sw_irq_handler(void){
  uint32_t  exccode;
  uint32_t  instr_word;
  uint32_t  mcause;
  uint32_t  ret_addr;
  uint32_t *mepc;


  // Read CSRs

  __asm__ volatile(
    "csrr %[mcause], mcause"
    : [mcause] "=r" (mcause)
  );

  exccode = mcause & 0xFFF;


  // Handle causes

  g_got_trap = 1;

  if (exccode == EXC_CAUSE_ILLEGAL_INSTR) {
    g_got_illegal_instruction_exception = 1;
  }


  // Setup mepc

  __asm__ volatile(
    "csrr %[mepc], mepc"
    : [mepc] "=r" (mepc)
  );

  instr_word = *mepc;

  if ((instr_word & 0x3) == 0x3) {
    ret_addr = ((uint32_t)mepc) + 4;
  } else {
    ret_addr = ((uint32_t)mepc) + 2;
  }

  __asm__ volatile(
    "csrw  mepc, %[ret_addr]"
    : : [ret_addr] "r" (ret_addr)
  );

  return;
}

static void turn_on_dummies(void){
  // "cpuctrl.rnddummy"
  __asm__ volatile( "csrrs x0, 0xBF0, 2" );
}

static void  test_csr_accesses(void) {
  uint32_t rd;
  const uint32_t rs1 = 0xFFFFFFFF;

  printf("Test cpuctrl\n");
  __asm__ volatile("csrr  %0, " STR(CSRADDR_CPUCTRL)          : "=r"(rd));
  __asm__ volatile("csrwi     " STR(CSRADDR_CPUCTRL) ", 0xF");
  __asm__ volatile("csrrs %0, " STR(CSRADDR_CPUCTRL) ", %1"   : "=r"(rd) : "r"(rs1));
  __asm__ volatile("csrrc %0, " STR(CSRADDR_CPUCTRL) ", %1"   : "=r"(rd) : "r"(rs1));

  printf("Test secureseed0\n");
  __asm__ volatile("csrr  %0, " STR(CSRADDR_SECURESEED0)          : "=r"(rd));
  __asm__ volatile("csrwi     " STR(CSRADDR_SECURESEED0) ", 0xF");
  __asm__ volatile("csrrs %0, " STR(CSRADDR_SECURESEED0) ", %1"   : "=r"(rd) : "r"(rs1));
  __asm__ volatile("csrrc %0, " STR(CSRADDR_SECURESEED0) ", %1"   : "=r"(rd) : "r"(rs1));

  printf("Test secureseed1\n");
  __asm__ volatile("csrr  %0, " STR(CSRADDR_SECURESEED1)          : "=r"(rd));
  __asm__ volatile("csrwi     " STR(CSRADDR_SECURESEED1) ", 0xF");
  __asm__ volatile("csrrs %0, " STR(CSRADDR_SECURESEED1) ", %1"   : "=r"(rd) : "r"(rs1));
  __asm__ volatile("csrrc %0, " STR(CSRADDR_SECURESEED1) ", %1"   : "=r"(rd) : "r"(rs1));

  printf("Test secureseed2\n");
  __asm__ volatile("csrr  %0, " STR(CSRADDR_SECURESEED2)          : "=r"(rd));
  __asm__ volatile("csrwi     " STR(CSRADDR_SECURESEED2) ", 0xF");
  __asm__ volatile("csrrs %0, " STR(CSRADDR_SECURESEED2) ", %1"   : "=r"(rd) : "r"(rs1));
  __asm__ volatile("csrrc %0, " STR(CSRADDR_SECURESEED2) ", %1"   : "=r"(rd) : "r"(rs1));
}

static void  test_previous_issues(void) {
  // This particular line has previously caught a problem
  __asm__ volatile("csrwi 0xBF0, 0x2");
}

static void test_lfsr_lockup(void){
  volatile uint32_t  zero = 0;

  turn_on_dummies();


  // "secureseed0"  (Have to copy-paste because csr instr...)

  g_got_trap = 0;

  __asm__ volatile(
    "csrrw x0, 0xBF9, %[zero]"
    : : [zero] "r" (zero)
  );

  if (g_got_trap) {
    printf("error: writing 0 to secureseed0 shouldn't trap\n");
    exit(EXIT_FAILURE);
  }


  // "secureseed1"

  g_got_trap = 0;

  __asm__ volatile(
    "csrrw x0, 0xBFA, %[zero]"
    : : [zero] "r" (zero)
  );

  if (g_got_trap) {
    printf("error: writing 0 to secureseed1 shouldn't trap\n");
    exit(EXIT_FAILURE);
  }


  // "secureseed2"

  g_got_trap = 0;

  __asm__ volatile(
    "csrrw x0, 0xBFC, %[zero]"
    : : [zero] "r" (zero)
  );

  if (g_got_trap) {
    printf("error: writing 0 to secureseed2 shouldn't trap\n");
    exit(EXIT_FAILURE);
  }


  // These checks of LFSR lockups could include an additional check that a
  // minor alert gets signaled on each lockup.
  // (E.g. make a new virtual peripheral for it.)
  // It is not done now, as the primary goal is only to close a coverage hole.
}

static void test_secureseed_rs1_x0(void){
  // "secureseed0"  (Have to copy-paste because csr instr...)

  g_got_illegal_instruction_exception = 0;

  __asm__ volatile( "csrrw x0, 0xBF9, x0" );

  if (g_got_illegal_instruction_exception == 0) {
    printf("error: 'secureseed0' access w/ rs1=x0 should trap\n");
    exit(EXIT_FAILURE);
  }


  // "secureseed1"

  g_got_illegal_instruction_exception = 0;

  __asm__ volatile( "csrrw x0, 0xBFA, x0" );

  if (g_got_illegal_instruction_exception == 0) {
    printf("error: 'secureseed1' access w/ rs1=x0 should trap\n");
    exit(EXIT_FAILURE);
  }


  // "secureseed2"

  g_got_illegal_instruction_exception = 0;

  __asm__ volatile( "csrrw x0, 0xBFC, x0" );

  if (g_got_illegal_instruction_exception == 0) {
    printf("error: 'secureseed2' access w/ rs1=x0 should trap\n");
    exit(EXIT_FAILURE);
  }
}

int main(void) {
  test_csr_accesses();
  test_previous_issues();
  test_lfsr_lockup();
  test_secureseed_rs1_x0();

  printf("Test 'xsecure_csrs' done\n");
  return EXIT_SUCCESS;
}
