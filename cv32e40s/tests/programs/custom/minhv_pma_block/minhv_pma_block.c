//
// Copyright 2023 Silicon Labs, Inc.
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
///////////////////////////////////////////////////////////////////////////////
//
// Author: Kristine Døsvik
//
// Test minhv=1 and pma block of mepc address.
//
/////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "bsp.h"

#define RND_ADDRS_IN_PMA_CFG_2_IO_REGION 0xE0100010

extern volatile uint32_t recovery_pt_mret;
volatile uint32_t g_entered_trap_handler;
volatile uint32_t g_trapped_mcause;

int execute_from_io_region();
__attribute__((interrupt ("machine"))) void u_sw_irq_handler(void);
void trap_handler(void);


int main(int argc, char **argv){

  int is_failure = 0;

  is_failure += execute_from_io_region();

  if(is_failure){
    return EXIT_FAILURE;
  } else {
    return EXIT_SUCCESS;
  }
}


int execute_from_io_region() {

  volatile uint32_t io_addr = RND_ADDRS_IN_PMA_CFG_2_IO_REGION;
  volatile uint32_t mcause_excode = 0x0;
  volatile uint32_t mcause_excode_expected = EXC_CAUSE_INSTR_ACC_FAULT; //Execution attempt from I/O region.
  volatile uint32_t mret_dont_trap = 0;
  volatile uint32_t test_fail = 0;
  g_entered_trap_handler = 0;

  // Load an IO memory address into mepc
  __asm__ volatile ( R"(
    csrrw zero, mepc, %[io_addr]
  )" :: [io_addr] "r"(io_addr));

  // Set minhv and mpp = M
  __asm__ volatile ( R"(
    lui t0, 0x70000
    csrrs zero, mcause, t0
  )"::: "t0");

  __asm__ volatile ( R"(
    mret
  )":::);

  // Mret traps.

  // This should never execute (deliberate dead code), as the mret make the pc take a jump
  mret_dont_trap += 1;

  // Execution should continue here
  __asm__ volatile ( R"(
    .global recovery_pt_mret
    recovery_pt_mret: add x0, x0, x0
  )":::);


  mcause_excode = g_trapped_mcause & 0x7ff;

  printf("Mret traps: %08lx, expected: 1\n", g_entered_trap_handler);
  printf("Mret dont trap: %08lx, expected: 0\n", mret_dont_trap);
  printf("mcause excode: %08lx, expected: %08lx (execution attempt from I/O region).\n", mcause_excode, mcause_excode_expected);
  test_fail += (g_entered_trap_handler != 1) || mret_dont_trap || (mcause_excode != mcause_excode_expected);

  printf("g_trapped_mcause: %08lx", g_trapped_mcause);

  return test_fail;
}


__attribute__((interrupt ("machine")))
void  u_sw_irq_handler(void) {
  __asm__ volatile (R"(
    # Backup all GPRs
    sw a0, -4(sp)
    sw a1, -8(sp)
    sw a2, -12(sp)
    sw a3, -16(sp)
    sw a4, -20(sp)
    sw a5, -24(sp)
    sw a6, -28(sp)
    sw a7, -32(sp)
    sw t0, -36(sp)
    sw t1, -40(sp)
    sw t2, -44(sp)
    sw t3, -48(sp)
    sw t4, -52(sp)
    sw t5, -56(sp)
    sw t6, -60(sp)
    addi sp, sp, -64
    cm.push {ra, s0-s11}, -64

    # Call the handler actual
    call ra, trap_handler

    # Restore all GPRs
    cm.pop {ra, s0-s11}, 64
    addi sp, sp, 64
    lw a0, -4(sp)
    lw a1, -8(sp)
    lw a2, -12(sp)
    lw a3, -16(sp)
    lw a4, -20(sp)
    lw a5, -24(sp)
    lw a6, -28(sp)
    lw a7, -32(sp)
    lw t0, -36(sp)
    lw t1, -40(sp)
    lw t2, -44(sp)
    lw t3, -48(sp)
    lw t4, -52(sp)
    lw t5, -56(sp)
    lw t6, -60(sp)

    # Restore "sp"
    # csrr sp, dscratch0

    # Done
    mret
  )");
}

void trap_handler(void) {

  g_entered_trap_handler += 1;

  __asm__ volatile ( R"(
   # Get recovery mepc and replace mepc
    la t0, recovery_pt_mret
    csrrw zero, mepc, t0

    # read and clear mcause except mpp, which is set
    4: lui t0, 0x30000
    csrrw %[g_trapped_mcause], mcause, t0

  )" : [g_trapped_mcause]"=r"(g_trapped_mcause) :: "t0");

  return;
}

