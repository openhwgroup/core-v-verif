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

// #define torregion 0xffff

extern void xr_test(uint32_t *output_addr, uint32_t addr);
extern void xw_test(uint32_t *input_addr, uint32_t addr);
extern void loadtrap();

int temp[64] = {0};

void exps()
{
  if (glb_csrs.mcause == 1)
  {
    printf("\n\t execution not enabled \n");
  }
  else if (glb_csrs.mcause == 2)
  {
    printf("\n\t U mode instruction exception \n");
  }
  else if (glb_csrs.mcause == 5)
  {
    printf("\n\t Read not enabled \n");
  }
  else if (glb_csrs.mcause == 7)
  {
    printf("\n\t write not enabled \n");
  }
}

void tor_zero()
{
  // int temp[64] = {0};

  // designate a range for addr0
  asm volatile("csrrw x0, 0x3b0, %0" ::"r"((0x8888 >> 2)));
  asm volatile("csrrw x0, 0x3b1, %0" ::"r"((0xffffffff >> 2)));

  for (int i = 0; i < 64; i++)
  {
    asm volatile("sw %0, 0(%1)" ::"r"(i + 4), "r"(0x8888 + i));
  }

  // TODO: XRW
  // set cfg0.torX-torX
  // asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0xc0c));
  // change_mode();
  // should trap
  // asm volatile("lw %0, 0(%1)"
  //              : "=r"(temp[2])
  //              : "r"(0x8888 + 8));
  // try to write to R only region, trigger trap and switch back to Mmode
  // storeram();

  // set cfg0.torXWR-torXWR
  // asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0xf0f));
  // change_mode();
  // asm volatile("lw %0, 0(%1)"
  //              : "=r"(temp[2])
  //              : "r"(0x8888 + 8));

  // printf("\n\t execute tested and passed\n");
  // printf("\n\t temp[2] = %d, @x%x\n\n", temp[2], &temp[2]);

  // set cfg0.torXWR-torXR
  // asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0xf0d));
  // change_mode();

  // xr_test(&temp[2], 0x8888+8);
  // exps();

  // // asm volatile("sw t0, 0(s1)"); // to trap
  // loadtrap();

  // printf("\n\t entry0 XR test passed");
  // printf("\n\t back in M mode ");
  // printf("\n\t temp[2] = %d @0x%x", temp[2], (unsigned int)&temp[2]);
  // printf("\n\t ------------------------------------------------- \n");
  // asm volatile("lw %0, 0(%1)":"=r"(temp[2]):"r"(0x8888+8));
  // printf("\n\t reading from 0x888+8 = %d\n", temp[2]);
  // set cfg0.torXWR-torXW
  // asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0xf0e));
  // change_mode();
  // // asm volatile("sw a0, 0(s1)\n");
  // xw_test(11, 0x8888+8);
  // exps();

  // printf("\n\t entry0 XW test passed");
  // printf("\n\t back in M mode ");
  // printf("\n\t temp[2] = %d @0x%x", temp[2], (unsigned int)&temp[2]);
  // printf("\n\t ------------------------------------------------- \n\n");
}
