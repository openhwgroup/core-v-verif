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
// #define ARBITARY 0XFFFF

// used to split address, lower half to be included in region0, upper to be included in region1
uint32_t split_addr[64] = {0};

void tor_zero()
{
  // int value = 4; // used to add to value for disdinguishing from 0
  uint32_t mcause = 1111;
  uint32_t mepc = 0;

  printf("\n\t--------\n\tTorZero test\n");
  // array split_addr is splitted into region0 and region1 at split_addr[30]
  uint32_t out_region0_addr = (uint32_t)(split_addr + 31);

  // designate a range for addr0, out_region0_addr
  asm volatile("csrrw x0, 0x3b0, %0" ::"r"(out_region0_addr >> 2));
  asm volatile("csrrw x0, 0x3b1, %0" ::"r"((RAMSPACE >> 2)));

  asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0xf0b));

  // Try exec outside of region0  (should NOT trap)
  // alternative: split_addr[31] = 0x ? ? ? ? ? ? ? ? ;
  umode_jmp(&split_addr[31]);
  printf("\tback in M mode\n");
  asm volatile("csrrw %0, mcause, x0"
               : "=r"(mcause));
  asm volatile("csrrw %0, mepc, x0"
               : "=r"(mepc));
  if ((mcause == 1) && (mepc != (uint32_t)&split_addr[31]))
  {
    printf("\toutside region0 access permission test pass\n");
  }
  else
  {
    exit(EXIT_FAILURE);
  }

  // Try exec inside of region0 (should trap)
  umode();
  asm volatile("nop");

  printf("\tback in M mode\n");
  asm volatile("csrrw %0, mcause, x0"
               : "=r"(mcause));
  if (mcause == 1)
  {
    printf("\tinside region0 access permission test pass\n");
  }
  else
  {
    exit(EXIT_FAILURE);
  }

  // TODO: try different pmpaddr0 sizes
}
