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

// Verification Goal: Check that, out of reset, given no extraordinary reset values, and given no change to the pmp csrs, then U-mode has no access permissions.
// Feature Description: "PMP can grant permissions to S and U modes, which by default have none"

void default_none()
{
  uint32_t mcause = 11111; // set an arbitrary value
  printf("\n\t testing DefaultNone\n");

  // execution permission test
  umode();
  // this line is supposed to trap
  asm volatile("addi t0, t1, 0x12"); // 0x12 as arbitary value

  printf("\n\t Back in M mode ");
  asm volatile("csrrw %0, mcause, x0"
               : "=r"(mcause));
  if (mcause == 1)
  {
    printf("\n\t Execution permission test pass ");
    printf("\n\t ------------------------------ \n");
  }
  else
  {
    printf("\n\t Execution permission test failed \n");
    exit(EXIT_FAILURE);
  }

  // store permission test
  umode();
  // this line is supposed to trap
  asm volatile("sw t0, 0(t1)"); // to be  improve: using a random value to replace t1

  printf("\n\t Back in M mode ");
  asm volatile("csrrw %0, mcause, x0"
               : "=r"(mcause));
  if (mcause == 1)
  {
    printf("\n\t Store permission test pass ");
    printf("\n\t ------------------------------ \n");
  }
  else
  {
    printf("\n\t Store permission test failed \n");
    exit(EXIT_FAILURE);
  }

  // load permission test
  umode();
  // this line is supposed to trap
  asm volatile("lw t0, 0(t1)"); // to be  improve: using a random value to replace t1
  printf("\n\t Back in M mode ");
  asm volatile("csrrw %0, mcause, x0"
               : "=r"(mcause));
  // printf("\n\t mcause = 0x%lx\n", mcause);

  if (mcause == 1)
  {
    printf("\n\t Load permission test pass");
    printf("\n\t ------------------------------ \n");
  }
  else
  {
    printf("\n\t Load permission test failed \n");
    exit(EXIT_FAILURE);
  }
  printf("\n\t DefaultNone test pass ");
  printf("\n\t --------------------------------------------- \n");
}