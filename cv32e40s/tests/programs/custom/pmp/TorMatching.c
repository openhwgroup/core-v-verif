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

#define opns 0x10000

// stay away from 0x0-0xFFF, addresses close to your stack pointer, and within 0x1000-0x40_0000 and not 0x1A11_0800-0x1A11_1800 (Debug)
// do no use pmpaddr0 as of conflicting sticky bit in TorZero

void tor_macthing()
{
  int temp;

  asm volatile("sw %0, 0(%1)" ::"r"(1), "r"(opns));
  asm volatile("sw %0, 0(%1)" ::"r"(5), "r"(opns - 4 * 5));

  //  TODO:R range [addr0:addr1)
  //  set pmp regions from opns - opns+4*150
  asm volatile("csrrw x0, 0x3b1, %0\n"
               "csrrw x0, 0x3b2, %1\n" ::"r"(opns >> 2),
               "r"((opns >> 2) + 256));
  // set pmp mode to TOR for pmpaddr0 & pmpaddr1
  // set pmpcfg0/1 read and TOR
  // asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0x8900));

  // cfg1.Ltor, cfg2.LtorR
  asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0x999800));

  asm volatile("lw %0, 0(%1)"
               : "=r"(temp)
               : "r"(opns));
  printf("\t\n loading from address 0x%x\n", opns);
  printf("\t\n value %d\n\n", temp);

  asm volatile("lw %0, 0(%1)"
               : "=r"(temp)
               : "r"(opns - 4 * 5));
  printf("\t\n loading from address 0x%x\n", opns - 4 * 5);
  printf("\t\n value %d\n\n", temp);

  asm volatile("lw %0, 0(%1)"
               : "=r"(temp)
               : "r"(opns + 4 * 500));
  printf("\t\n loading from address 0x%x\n", opns + 4 * 500);
  printf("\t\n value %d\n\n", temp);

  // TODO:RW range [addr2:addr3)
  // asm volatile("csrrw x0, 0x3b2, %0\n"
  //              "csrrw x0, 0x3b3, %1\n" ::"r"(2*(opns >> 2)),
  //              "r"(2*(opns >> 2) + 256));

  // TODO:RX

  // TODO:X

  // umode();
  // asm volatile("csrrs %0, 0x3a , x0"
  //              : "=r"(temp));
  // printf("\t\n0x3a0 value is %x\n\n", temp);
}