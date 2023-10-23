// Copyright 2022 OpenHW Group
// Copyright 2022 Silicon Labs, Inc.
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

// Feature Description: "If pmpaddri−1 ≥ pmpaddri and pmpcfgi.A=TOR, then PMP entry i matches no addresses."
// Verification Goal: Set up tor regions where the addresses are not in increasing order, try accesses on or within the designated "reverse" regions, ensure that they are treated as if there is no match.

void tor_nomatch()
{
  volatile uint32_t  temp[64] = {0};
  uint32_t           mcause   = 11111;
  uint32_t           upperaddr;
  uint32_t           loweraddr;
  uint32_t           res0;
  uint32_t           res1;


  printf("\n\t--------\n\tTorNomatch test\n");


  // Init

  // to  make sure temp values are not the same.
  for (int i = 0; i < 64; i++)
  {
    temp[i] = i + 1;
  }

  // designate "orderly" region up through first half of "temp[]", "torXWR"
  upperaddr = ((uint32_t)(&temp[31])) >> 2;
  loweraddr = 0;
  asm volatile("csrw pmpaddr4, %0" : : "r"(upperaddr));
  asm volatile("csrw pmpaddr3, %0" : : "r"(loweraddr));
  asm volatile("csrw pmpcfg1,  %0" : : "r"(0xF));  // Entry 4

  // designate "reverse" region for second half of "temp[]", "torXWR"
  upperaddr = ((uint32_t)(&temp[32])) >> 2;  // Upper addr is "below" lower addr
  loweraddr = ((uint32_t)(&temp[63])) >> 2;
  asm volatile("csrw pmpaddr1, %0" ::"r"(upperaddr));
  asm volatile("csrw pmpaddr0, %0" ::"r"(loweraddr));
  asm volatile("csrw pmpcfg0,  %0" ::"r"(0xF00));  // Entry 1

  // designate "orderly" region after second half of "temp[]" and up, "torXWR"
  upperaddr = 0xFFFFffff;
  loweraddr = ((uint32_t)(&temp[64])) >> 2;
  __asm__ volatile("csrw 0x3EF, %0" : : "r"(upperaddr));  // 0x3EF=pmpaddr63
  __asm__ volatile("csrw 0x3EE, %0" : : "r"(loweraddr));
  __asm__ volatile("csrw 0x3AF, %0" : : "r"(0x0f000000));  // TOR+XWR on entry 63, 0x3AF=pmpcfg15


  // try to access orderly region

  glb_csrs.mcause = 0;

  umode();
  asm volatile("nop");
  if (glb_csrs.mcause) {
    printf("\n\t unexpected trap, in 'orderly' test after umode\n");
    exit(EXIT_FAILURE);
  }

  store2addr(13, (uint32_t *)&temp[1]);
  if (glb_csrs.mcause) {
    printf("\n\t store should not except\n");
    exit(EXIT_FAILURE);
  }
  load4addr((uint32_t *)&temp[2], (uint32_t *)&temp[1]);
  if (glb_csrs.mcause) {
    printf("\n\t loadstore should not except\n");
    exit(EXIT_FAILURE);
  }

  // to trap and bring back to M mode
  asm volatile("ecall");
  if (glb_csrs.mcause != 8) {  // Environment call from U-Mode (ECALL)
    printf("\n\t unexpected trap, in 'orderly' test after ecall\n");
    exit(EXIT_FAILURE);
  }

  // to read from 0xfff1
  if (temp[0] == temp[1]) {
    printf("\n\t badly initialized test, temp0==temp1\n");
    exit(EXIT_FAILURE);
  }
  asm volatile("lw %0, 0(%1)"
               : "=r"(res0)
               :  "r"(temp[1]));
  asm volatile("lw %0, 0(%1)"
               : "=r"(res1)
               :  "r"(temp[2]));
  if (temp[1] == temp[2]) {
    printf("\n\t orderly region access test pass ");
    printf("\n\t Back in M mode ");
  } else {
    printf("\n\t 'orderly' test, unexpected results\n");
    exit(EXIT_FAILURE);
  }


  // try to access reversed region 0xffff_ff-0xffff_f

  glb_csrs.mcause = 0;

  umode();
  asm volatile("nop");
  if (glb_csrs.mcause) {
    printf("\n\t unexpected trap, in 'reverse' test after umode\n");
    exit(EXIT_FAILURE);
  }

  // this should trap and bring to M mode
  store2addr(13, (uint32_t *)&temp[33]);

  asm volatile("csrrs %0, mcause, x0"
               : "=r"(mcause));
  if (mcause == 7) {  // Store/AMO access fault
    printf("\n\t reverse region access denied, test pass ");
    printf("\n\t Back in M mode ");
  } else {
    printf("\n\t 'reverse' test, unexpected results\n");
    exit(EXIT_FAILURE);
  }
}
