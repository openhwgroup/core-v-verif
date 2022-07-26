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

#define torregion 0x2000

__attribute__((naked)) void loadram(int loop)
{
  int temp;
  for (int i = 0; i < loop; i++)
  {
    asm volatile("lw %0, 0(%1)"
                 : "=r"(temp)
                 : "r"(torregion + 4 * i));
    // printf("\t\ntemp of interation %d = %d\n", i, temp);
    if (temp != (i + 3))
    {
      // printf("\t\nloaded value does not match stored @0x%x\n", torregion + 4 * i);
      exit(EXIT_FAILURE);
    }
  }
}

void tor_zero()
{
  int temp;
  // designate a range for addr0
  asm volatile("csrrw x0, 0x3b0, %0" ::"r"((torregion >> 2) + 4 * 500));
  for (int i = 0; i < 64; i++)
  {
    asm volatile("sw %0, 0(%1)" ::"r"(i + 4), "r"(torregion + 4 * i));
  }

  // TODO: R
  // set cfg0.LtorR, L to enforce rule in Mmode
  asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0x19));
  change_mode();
  // loadram(64);
  // for (int i = 0; i < 64; i++)
  // {
  //   asm volatile("lw %0, 0(%1)"
  //                : "=r"(temp)
  //                : "r"(torregion + 4 * i));
    // printf("\t\ntemp of interation %d = %d\n", i, temp);
    // if (temp != (i + 4))
    // {
      // printf("\t\nloaded value does not match stored @0x%x\n", torregion + 4 * i);
      // exit(EXIT_FAILURE);
  //   }
  // }
  // printf("\n\tload store test passed on the designated RAM space\n");

  // trying to write again after rule implelemted
  // for (int i = 0; i < 64; i++)
  // {
  //   asm volatile("sw %0, 0(%1)" ::"r"(i + 3), "r"(torregion + 4 * i));
  // }

  // TODO: RW

  // TODO: RX

  // TODO: X

  // TODO: RWX
}
