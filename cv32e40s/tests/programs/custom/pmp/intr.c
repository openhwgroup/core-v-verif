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
  printf("\n\t u_sw_irq_handler ");
  __asm__ volatile("csrrs %0, mcause, x0"
                   : "=r"(glb_csrs.mcause));

  if (glb_csrs.mcause == 0)
  {
    printf("\n\t Instruction address misaligned ");
  }
  else if (glb_csrs.mcause == 1)
  {
    printf("\n\t Instruction access fault ");
  }
  else if (glb_csrs.mcause == 2)
  {
    printf("\n\t Illegal instruction ");
  }
  else if (glb_csrs.mcause == 3)
  {
    printf("\n\t Breakpoint ");
  }
  else if (glb_csrs.mcause == 4)
  {
    printf("\n\t Load address misaligned ");
  }
  else if (glb_csrs.mcause == 5)
  {
    printf("\n\t Load access fault ");
  }
  else if (glb_csrs.mcause == 6)
  {
    printf("\n\t Store/AMO address misaligned ");
  }
  else if (glb_csrs.mcause == 7)
  {
    printf("\n\t Store/AMO access fault ");
  }
  else if (glb_csrs.mcause == 8)
  {
    printf("\n\t Environment call from U-Mode (ECALL)\n");
  }
  else if (glb_csrs.mcause == 11)
  {
    printf("\n\t Environment call from M-Mode (ECALL)\n");
  }
  else
  {
    printf("\n\t (some other mcause reason, %lu)", glb_csrs.mcause);
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
