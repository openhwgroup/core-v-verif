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
  uint32_t mcause = 11111;
  // designate region0 and region 63 to be XWR for TEXT and stack to fucntio normally
  asm volatile("csrrw x0, 0x3b0, %0" ::"r"((0xffffff >> 2)));
  asm volatile("csrrw x0, 0x3b1, %0" ::"r"((0xfffff >> 2)));

  // asm volatile("csrrw x0, 0x3ef, %0" ::"r"((0xffffffff >> 2)));
  // set cfg0.torXWR
  asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0xf0f));
  // set cfg63.torXWR
  // asm volatile("csrrw x0, 0x3ef, %0" ::"r"(0xf000000));

  // designate region 9, stack_end = 0x400000
  // asm volatile("csrrw x0, 0x3b9, %0" ::"r"((0xf00000 >> 2)));
  // designate region 10
  // asm volatile("csrrw x0, 0x3ba, %0" ::"r"((0x100000 >> 2)));

  // write values to reversed region 0xf00000-0x100000
  // for (int i = 0; i < 6; i++)
  // {
  //   asm volatile("sw %0, 0(%1)" ::"r"(i + 4), "r"(0x200000 + i * 4));
  // }
  // verify values to designated gions are correctly stored
  // for (int i = 0; i < 6; i++)
  // {
  //   asm volatile("lw %0, 0(%1)"
  //                : "=r"(temp[i])
  //                : "r"(0x200000 + i * 4));
  //   if (temp[i] != (i + 4))
  //   {
  //     exit(EXIT_FAILURE);
  //   }
  // }

  // config cfg9.torXWR and cfg10.torXWR
  // asm volatile("csrrw x0, 0x3a2, %0" ::"r"(0xf0f00));

  // umode();
  // // try to access orderly region 0x0 - 0xffff_ff
  // store2addr(13, 0xffff);
  // load4addr(0xfff1, 0xffff);

  // // to trap and bring back to M mode
  // asm volatile("csrrs %0, mstatus, x0"
  //              : "=r"(mcause));
  // // to read from 0xfff1
  // load4addr((unsigned int *)temp[0], 0xffff);
  // load4addr((unsigned int *)temp[1], 0xfff1);
  // if (temp[0] == temp[1])
  // {
  //   printf("\n\t orderly region access test pass ");
  //   printf("\n\t Back in M mode ");
  //   printf("\n\t --------------------------------------------- \n");
  // }
  // else
  // {
  //   exit(EXIT_FAILURE);
  // }

  // try to access reversed region 0xffff_ff-0xffff_f
  umode();
  // store2addr(13, 0xfffff0); // this should trap and bring to M mode
  // load4addr(0xffffa, 0xffff0);
  asm volatile("sw %0, 0(%1)" ::"r"(13), "r"(0xfffff0));
  asm volatile("lw %0, 0(%1)" ::"r"(0xffffa), "r"(0xfffff0));
  // asm volatile("csrrs %0, mcause, x0"
  //              : "=r"(mcause));
  // if (mcause == 7)
  // {
  //   printf("\n\t reverse region access test pass \n");
  //   printf("\n\t Back in M mode \n");
  //   printf("\n\t --------------------------------------------- \n");
  // }
  // else
  // {
  //   exit(EXIT_FAILURE);
  // }
}
