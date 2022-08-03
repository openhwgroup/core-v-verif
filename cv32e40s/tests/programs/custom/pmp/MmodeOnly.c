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

// Feature Description: "PMP CSRs are only accessible to M-mode."
// Verification Goal: Try to access any of the pmp CSRs from U-mode, ensure that it always gives "illegal instruction exception" and that the CSRs are not updated.

#include "pmp.h"

static CSRS csrs;

void pmpcfgxtest()
{
  int temp[64] = {0};
  uint32_t pmpcfgx;
  uint32_t mcause = 11111; // set an arbitrary value

  printf("\n\t U mode pmpcfg test");

  // load content from pmpcfgx and store in variable
  asm volatile("csrrs %0, 0x3A9, x0"
               : "=r"(pmpcfgx));
  // get random value to temp[63]
  __asm__ volatile("lw %0, 0(%1)"
                   : "=r"(temp[63])
                   : "r"(RANDOM_REG));
  umode();

  // attempting to read and write pmpcfg, should trap
  asm volatile("csrrw %0, 0x3a9, %1"
               : "=r"(pmpcfgx)
               : "r"(temp[63]));

  printf("\n\t Back in M mode ");
  if (glb_csrs.mcause == 2)
  {
    printf("\n\t Illegal instruction exception triggered as expected ");
    printf("\n\t Comparing pmpcfgx values M:U mode ");
    asm volatile("csrrs %0, 0x3A9, x0"
                 : "=r"(csrs.pmpcfgx[9]));
    if (pmpcfgx != csrs.pmpcfgx[9])
    {
      printf("\n\t pmpcfg value overwritten, test failed\n");
      exit(EXIT_FAILURE);
    }
    else
    {
      printf("\n\t U mode pmpcfg test pass ");
      printf("\n\t --------------------------------------------- \n");
    }
  }
  else
  {
    asm volatile("csrrw %0, mcause, x0"
                 : "=r"(mcause));
    printf("\n\t mcause read as 0x%lx != 0x2\n", mcause);
    exit(EXIT_FAILURE);
  }
}

void pmpaddrxtest()
{
  uint32_t pmpaddrx;
  int temp[64] = {0};
  uint32_t mcause = 11111; // set an arbitrary value
  printf("\n\t U mode pmpaddr test ");

  asm volatile("csrrs %0, 0x3Ba, x0\n"
               : "=r"(pmpaddrx));

  change_mode();
  // attempting to read and write pmpaddr, should trap
  asm volatile("csrrw %0, 0x3ba, %1"
               : "=r"(pmpaddrx)
               : "r"(temp[63]));

  printf("\n\t Back in M mode ");
  if (glb_csrs.mcause == 2)
  {
    printf("\n\t Illegal instruction exception triggered as expected ");
    printf("\n\t Comparing pmpaddr values M:U mode");
    asm volatile("csrrs %0, 0x3Ba, x0"
                 : "=r"(csrs.pmpaddrx[10]));
    if (pmpaddrx != csrs.pmpaddrx[10])
    {
      printf("\n\t pmpaddr value overwritten, test failed\n");
      exit(EXIT_FAILURE);
    }
    else
    {
      printf("\n\t U mode pmpaddr test pass ");
      printf("\n\t --------------------------------------------- \n");
    }
  }
  else
  {
    asm volatile("csrrw %0, mcause, x0"
                 : "=r"(mcause));
    printf("\n\t mcause read as 0x%lx != 0x2\n", mcause);
    exit(EXIT_FAILURE);
  }
}

void mseccfgtest()
{
  uint32_t mseccfg;
  int temp[64] = {0};
  uint32_t mcause = 11111; // set an arbitrary value
  asm volatile("csrrs %0, 0x747, x0"
               : "=r"(mseccfg));

  change_mode();
  printf("\t U mode mseccfg check");

  // attempting to read and write from mseccfg, should trap
  asm volatile("csrrw %0, 0x3ba, %1"
               : "=r"(mseccfg)
               : "r"(temp[63]));

  printf("\n\t Back in M mode ");
  if (glb_csrs.mcause == 2)
  {
    printf("\n\t Illegal instruction exception triggered as expected ");
    printf("\n\t Comparing pmpcfgx values M:U mode");
    asm volatile("csrrs %0, 0x3A9, x0"
                 : "=r"(csrs.mseccfg));
    if (mseccfg != csrs.mseccfg)
    {
      printf("\n\t mseccfg values overwritten, test failed\n");
      exit(EXIT_FAILURE);
    }
    else
    {
      printf("\n\t U mode mseccfg test pass ");
      printf("\n\t --------------------------------------------- \n");
    }
  }
  else
  {
    asm volatile("csrrw %0, mcause, x0"
                 : "=r"(mcause));
    printf("\n\t mcause read as 0x%lx != 0x2\n", mcause);
    exit(EXIT_FAILURE);
  }
}

void mmode_only()
{
  printf("\n\t testing MmodeOnly ");
  // set pmp addr to 0xffff-ffff
  asm volatile(
      "li t0, 0xFFFFFFFF\n"
      "csrrw x0, pmpaddr0, t0\n"
      "li t0, 0xf\n"
      "csrrw x0, 0x3a0, t0\n");

  pmpcfgxtest();
  pmpaddrxtest();
  mseccfgtest();
  printf("\n\t MmodeOnly test pass ");
  printf("\n\t --------------------------------------------- \n");
}
