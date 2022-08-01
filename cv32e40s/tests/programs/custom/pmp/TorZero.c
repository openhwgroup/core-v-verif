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

extern void load4addr(unsigned int *output_addr, unsigned int addr);
extern void store2addr(int input, unsigned int addr);

void tor_zero()
{
  int temp[64] = {0};
  // designate a range for addr0
  asm volatile("csrrw x0, 0x3b0, %0" ::"r"((0x8888 >> 2)));
  asm volatile("csrrw x0, 0x3b1, %0" ::"r"((0xffffffff >> 2)));
  for (int i = 0; i < 64; i++)
  {
    asm volatile("sw %0, 0(%1)" ::"r"(i + 4), "r"(0x7777 + i * 4));
  }

  // set cfg0.torXWR-torXR
  asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0xf0d));
  change_mode();

  load4addr((unsigned int)&temp[63], 0x7777 + 63 * 4);

  // to trap
  store2addr(11, 0x4444);
  if (glb_csr.mcause == 7)
  {
    printf("\n\t entry0 XR test passed");
  }
  else
  {
    exit(EXIT_FAILURE);
  }
  printf("\n\t back in M mode ");
  printf("\n\t temp[63] = %d @0x%x", temp[63], (unsigned int)&temp[63]);
  printf("\n\t ------------------------------------------------- \n");

  // set cfg0.torXWR-torWR
  asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0xf0b));
  change_mode();

  store2addr(11, 0x7770);
  if (glb_csr.mcause == 1)
  {
    printf("\n\t entry0 WR test passed");
  }
  else
  {
    exit(EXIT_FAILURE);
  }
  printf("\n\t ------------------------------------------------- \n");

  // TODO: try different entry0 sizes
}
