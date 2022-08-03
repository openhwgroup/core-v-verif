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

void tor_nomatch()
{
  int temp[64] = {0};
  // to  make sure temp values are not the same.
  for (int i = 0; i < 64; i++)
  {
    temp[i] = i + 1;
  }

  uint32_t mcause = 11111;
  // designate region0 and region 63 to be XWR for TEXT and stack to fucntio normally
  asm volatile("csrrw x0, 0x3b0, %0" ::"r"((0xffffff >> 2)));
  asm volatile("csrrw x0, 0x3b1, %0" ::"r"((0xfffff >> 2)));

  // set cfg0.torXWR
  asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0xf07));

  umode();
  // // try to access orderly region 0x0 - 0xffff_f
  store2addr(13, 0xffff);
  load4addr((uint32_t*)0xfff1, 0xffff);

  // to trap and bring back to M mode
  asm volatile("csrrs %0, mstatus, x0"
               : "=r"(mcause));
  // to read from 0xfff1
  asm volatile("lw %0, 0(%1)"
               : "=r"(temp[0])
               : "r"(0xffff));
  asm volatile("lw %0, 0(%1)"
               : "=r"(temp[1])
               : "r"(0xfff1));
  if (temp[0] == temp[1])
  {
    printf("\n\t orderly region access test pass ");
    printf("\n\t Back in M mode ");
    printf("\n\t --------------------------------------------- \n");
  }
  else
  {
    exit(EXIT_FAILURE);
  }

  // try to access reversed region 0xffff_ff-0xffff_f
  umode();
  // this should trap and bring to M mode
  store2addr(13, 0xfffff0);

  asm volatile("csrrs %0, mcause, x0"
               : "=r"(mcause));
  if (mcause == 1)
  {
    printf("\n\t reverse region access denied, test pass ");
    printf("\n\t Back in M mode ");
    printf("\n\t --------------------------------------------- \n");
  }
  else
  {
    exit(EXIT_FAILURE);
  }
}
