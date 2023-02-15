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

// Feature Description: "can revoke permissions from M-mode, which by default has full permissions"
// Verification Goal: Check that, out of/ after reset, given no extraordinary reset values, and given no change to the pmp csrs, then M-mode has full access permissions.

#include "pmp.h"
#define RANDOM_REG 0x00800040

void default_full()
{
  printf("\n\t--------\n\tDefaultFull test\n");

  volatile uint32_t temp[64] = {0};

  // get random address value
  __asm__ volatile("lw %0, 0(%1)"
                   : "=r"(temp[63])
                   : "r"(RANDOM_REG));

  // store an arbitrary value to an arbitrary address
  store2addr(13, (uint32_t *)temp[63]);
  load4addr((uint32_t *)&temp[0], (uint32_t *)temp[63]);

  if (temp[0] == 13)
  {
    printf("\tDefaultFull pass\n");
  }
  else
  {
    printf("\tRAM values are not as expected\n");
    exit(EXIT_FAILURE);
  }
}
