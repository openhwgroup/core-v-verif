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

// stay away from 0x0-0xFFF, addresses close to your stack pointer, and within 0x1000-0x40_0000 and not 0x1A11_0800-0x1A11_1800 (Debug)
// Feature Description: "If PMP entry 0’s A field is set to TOR, zero is used for the lower bound, and so it matches any address y < pmpaddr0."
// Verification Goal: Configure entry 0 as tor regions of different sizes, try accesses within and outside the regions, ensure that the outcomes corresponds to the designated ranges.

#define RAMSPACE 0X100000000
#define ARBITARY 0XFFFF

// int x[100]

void tor_zero()
{
  uint32_t temp[64] = {0};
  int value = 4; // used to add to value for disdinguishing from 0
  uint32_t mcause = 1111;
  printf("\n\t testing TorZero\n");

  // temp[63] = *((uint32_t *)RANDOM_REG);

  // designate a range for addr0, addr1
  asm volatile("csrrw x0, 0x3b0, %0" ::"r"((ARBITARY >> 2)));
  asm volatile("csrrw x0, 0x3b1, %0" ::"r"((RAMSPACE >> 2)));
  for (int i = 0; i < 64; i++)
  {
    // store value (i + value) to address ARBITARY/2
    asm volatile("sw %0, 0(%1)" ::"r"(i + value), "r"((uint32_t)(ARBITARY / 4 + i * 4)));
  }

  // set cfg0.torXWR-torXR
  asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0xf0d));
  umode();
  // load one value from the address range (ARBITARY/2) -- (ARBITARY/2+63*4)
  load4addr((uint32_t *)&temp[0], (ARBITARY / 4));
  // asm volatile("lw %0, 0(%1)"
  //              : "=r"(temp[0])
  //              : "r"(ARBITARY / 2 + 63 * 4));

  // to trap, store abitary value to address ARBITARY/4
  asm volatile("sw t0, 0(t1)");
  asm volatile("csrrw %0, mcause, x0"
               : "=r"(mcause));
  printf("\n\t back in M mode ");
  if (mcause == 7)
  {
    printf("\n\t pmpaddr0 store permission test pass ");
    if (temp[0] == value)
    {
      printf("\n\t pmpaddr0 load permission test pass ");
    }
    else
    {
      exit(EXIT_FAILURE);
    }
  }
  else
  {
    exit(EXIT_FAILURE);
  }
  printf("\n\t ------------------------------------------------- \n");

  // // set cfg1.torXWR, cfg0.torWR
  // asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0xf0b));
  // change_mode();
  // // trap
  // store2addr(11, 0x7770);
  // asm volatile("csrrs %0, mcause, x0"
  //              : "=r"(mcause));
  // if (mcause == 1)
  // {
  //   printf("\n\t pmpaddr0 WR test passed");
  // }
  // else
  // {
  //   exit(EXIT_FAILURE);
  // }
  // printf("\n\t ------------------------------------------------- \n");

  // access outside region0
  store2addr(14, 0x9999);
  load4addr((uint32_t *)&temp[8], 0x9999);
  if (temp[8] == 14)
  {
    printf("\n\t access outside pmpaddr0 test passed");
  }
  else
  {
    exit(EXIT_FAILURE);
  }
  printf("\n\t ------------------------------------------------- \n");

  // TODO: try different pmpaddr0 sizes
}
