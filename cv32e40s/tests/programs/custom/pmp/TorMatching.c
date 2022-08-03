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

void tor_macthing(){

  int temp[64] = {0};
  // to  make sure temp values are not the same.
  for (int i = 0; i < 64; i++)
  {
    temp[i] = i + 1;
  }
  // asign mcause an abiturary value
  uint32_t mcause = 11111;

  // // 0 regions, verify the entire RAM
  // umode();
  // //  to trap and bring back to M mode
  // store2addr(13, 0xffff);
  // asm volatile("csrrs %0, mcause, x0"
  //              : "=r"(mcause));
  // if (mcause == 1)
  // {
  //   printf("\n\t 0 region access test pass ");
  //   printf("\n\t Back in M mode ");
  //   printf("\n\t --------------------------------------------- \n");
  // }
  // else
  // {
  //   exit(EXIT_FAILURE);
  // }

  // 1 region to cover the entire RAM cfg0.XWR = 111
  asm volatile("csrrw x0, 0x3b0, %0" ::"r"((0xffffffff >> 2)));
  asm volatile("csrrwi x0, 0x3a0, 0x7");
  umode();
  // write to RAM
  for (int i = 0; i < 64; i++)
  {
    temp[i] = i + 11;
  }
  // read from RAM and compare
  for (int i = 0; i < 64; i++)
  {
    if (temp[i] != i + 11)
    {
      exit(EXIT_FAILURE);
    }
  }
  // to trap and bring back to M mode
  asm volatile("csrrs %0, mstatus, x0"
               : "=r"(temp[63]));
  asm volatile("csrrs %0, mcause, x0"
               : "=r"(mcause));
  if (mcause == 2)
  {
    printf("\n\t 1 region access test pass ");
    printf("\n\t Back in M mode ");
    printf("\n\t --------------------------------------------- \n");
  }

  // designate region0 and region 63 to be XWR for TEXT and stack to fucntio normally
  // asm volatile("csrrw x0, 0x3b0, %0" ::"r"((0x200000 >> 2))); // set to half of heap size
  // asm volatile("csrrw x0, 0x3b1, %0" ::"r"((0xfffff >> 2)));
  // asm volatile("csrrw x0, 0x3ee, %0" ::"r"((0xffdfffff >> 2))); // set to half of stack size
  // asm volatile("csrrw x0, 0x3ef, %0" ::"r"((0xffffffff >> 2)));
  // set cfg0.XWR
  // asm volatile("csrrwi x0, 3a0, 0x7");
  // set cfg60/61/62 off, cfg63.torXWR
  // asm volatile("csrrw x0, 0x3af, %0" ::"r"(0xf000000));

  // test region0 and region63

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

  // asm volatile("sw %0, 0(%1)" ::"r"(13), "r"(0xffff));
  // asm volatile("lw %0, 0(%1)" ::"r"(0xffff1), "r"(0xffff));

  // load4addr((unsigned int *)&temp[0], 0xffff);
  // load4addr((unsigned int *)&temp[1], 0xfff1);

  // load4addr(0xffffa, 0xffff0);
  // asm volatile("sw %0, 0(%1)" ::"r"(13), "r"(0xfffff0));
  // asm volatile("lw %0, 0(%1)" ::"r"(0xffffa), "r"(0xfffff0));
}