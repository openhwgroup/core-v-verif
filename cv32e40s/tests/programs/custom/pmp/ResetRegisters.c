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

// Feature Description: "Writable PMP registers’ A and L fields are set to 0, unless the platform mandates a different reset value for some PMP registers’ A and L fields."
// Verification Goal: Read the A and L values right after reset, check that the default reset values are 0. Note: Should also be visible on rvfi without specifically using csr instructions.
// extended test is to read all 8 bits for pmpxcfg

#include "pmp.h"

#define PMPCFGX 16

void reset_registers()
{
  printf("\n\t--------\n\tResetRegisters test\n");
  uint32_t pmpcfg[PMPCFGX];

  // read out pmpcfg register values with given address from 0x3a - 0x3af
  __asm__ volatile("csrr %0, 0x3A0" : "=r"(pmpcfg[0]));
  __asm__ volatile("csrr %0, 0x3A1" : "=r"(pmpcfg[1]));
  __asm__ volatile("csrr %0, 0x3A2" : "=r"(pmpcfg[2]));
  __asm__ volatile("csrr %0, 0x3A3" : "=r"(pmpcfg[3]));
  __asm__ volatile("csrr %0, 0x3A4" : "=r"(pmpcfg[4]));
  __asm__ volatile("csrr %0, 0x3A5" : "=r"(pmpcfg[5]));
  __asm__ volatile("csrr %0, 0x3A6" : "=r"(pmpcfg[6]));
  __asm__ volatile("csrr %0, 0x3A7" : "=r"(pmpcfg[7]));
  __asm__ volatile("csrr %0, 0x3A8" : "=r"(pmpcfg[8]));
  __asm__ volatile("csrr %0, 0x3A9" : "=r"(pmpcfg[9]));
  __asm__ volatile("csrr %0, 0x3Aa" : "=r"(pmpcfg[10]));
  __asm__ volatile("csrr %0, 0x3Ab" : "=r"(pmpcfg[11]));
  __asm__ volatile("csrr %0, 0x3Ac" : "=r"(pmpcfg[12]));
  __asm__ volatile("csrr %0, 0x3Ad" : "=r"(pmpcfg[13]));
  __asm__ volatile("csrr %0, 0x3Ae" : "=r"(pmpcfg[14]));
  __asm__ volatile("csrr %0, 0x3Af" : "=r"(pmpcfg[15]));

  // check for the specific bits
  for (int i = 0; i < PMPCFGX; i++)
  {
    if (pmpcfg[i] != 0)
    {
      printf("\n\tERROR: pmpcfg[%d] read as 0x%x != 0x0, test failed\n", i, (unsigned int)pmpcfg[i]);
      exit(EXIT_FAILURE);
    }
  }

  printf("\tResetRegisters pass\n");
}
