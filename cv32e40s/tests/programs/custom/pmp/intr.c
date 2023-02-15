// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
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

#include "pmp.h"

volatile CSRS glb_csrs; // only used for exception check

// volatile int glb_trap_expected = 0;

__attribute__((interrupt("machine"))) void u_sw_irq_handler(void)
{
  uint32_t instr_word;
  printf("\tu_sw_irq_handler\n");
  __asm__ volatile("csrrs %0, mcause, x0"
                   : "=r"(glb_csrs.mcause));

  if (glb_csrs.mcause == 0)
  {
    printf("\tInstruction address misaligned\n");
  }
  else if (glb_csrs.mcause == 1)
  {
    printf("\tInstruction access fault\n");
  }
  else if (glb_csrs.mcause == 2)
  {
    printf("\tIllegal instruction\n");
  }
  else if (glb_csrs.mcause == 3)
  {
    printf("\tBreakpoint\n");
  }
  else if (glb_csrs.mcause == 4)
  {
    printf("\tLoad address misaligned\n");
  }
  else if (glb_csrs.mcause == 5)
  {
    printf("\tLoad access fault\n");
  }
  else if (glb_csrs.mcause == 6)
  {
    printf("\tStore/AMO address misaligned\n");
  }
  else if (glb_csrs.mcause == 7)
  {
    printf("\tStore/AMO access fault\n");
  }
  else if (glb_csrs.mcause == 8)
  {
    printf("\tEnvironment call from U-Mode (ECALL)\n");
  }
  else if (glb_csrs.mcause == 11)
  {
    printf("\tEnvironment call from M-Mode (ECALL)\n");
  }
  else
  {
    printf("\t(some other mcause reason, %lu)\n", glb_csrs.mcause);
  }

  // Increment "mepc"
  __asm__ volatile("csrrw %0, mepc, x0"
                   : "=r"(glb_csrs.mepc));
  instr_word = *(uint32_t *)glb_csrs.mepc;
  if ((instr_word & 3) == 3)
  {
    glb_csrs.mepc += 4;
  }
  else
  {
    glb_csrs.mepc += 2;
  }

  __asm__ volatile("csrrw x0, mepc, %0"
                   :
                   : "r"(glb_csrs.mepc));

  // Set mmode again
  __asm__ volatile("csrrw %0, mstatus, x0"
                   : "=r"(glb_csrs.mstatus));
  // mstatus |= (3 << 11);
  glb_csrs.mstatus = 0x1800;
  __asm__ volatile("csrrw x0, mstatus, %0"
                   :
                   : "r"(glb_csrs.mstatus));

  return;
}
