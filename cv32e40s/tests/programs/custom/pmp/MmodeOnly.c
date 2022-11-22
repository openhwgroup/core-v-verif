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

// Feature Description: "PMP CSRs are only accessible to M-mode."
// Verification Goal: Try to access any of the pmp CSRs from U-mode, ensure that it always gives "illegal instruction exception" and that the CSRs are not updated.

void pmpcfgxtest()
{
  volatile uint32_t temp[64] = {0};
  volatile uint32_t pmpcfgx_before_test;
  volatile uint32_t pmpcfgx_after_test;
  uint32_t mcause = 11111; // set an arbitrary value other than mcause defaults
  volatile int illegal_count = 0;

  printf("\n\t U mode pmpcfg test");

  // load content from pmpcfgx and store in variable
  asm volatile("csrrs %0, 0x3A9, x0"
               : "=r"(pmpcfgx_before_test));
  // printf("\n\t pmpcfgx_before_test = 0x%lx\n", pmpcfgx_before_test);

  // get random value to temp[63]
  __asm__ volatile("lw %0, 0(%1)"
                   : "=r"(temp[63])
                   : "r"(RANDOM_REG));
  // printf("\n\t random reg = 0x%lx\n", temp[63]);

  // change to Umode and try to write to csr, should trap
  umode();
  asm volatile("csrrw x0, 0x3a9, %0" ::"r"(temp[63]));
  // trap end the first time
  asm volatile("csrrw %0, mcause, x0"
               : "=r"(mcause));
  if (mcause == 2)
  {
    illegal_count += 1;
  }
  // change to Umode and try to read to csr, should trap
  umode();
  asm volatile("csrrs %0, 0x3a9, x0"
               : "=r"(temp[62]));
  // trap end the second time
  asm volatile("csrrw %0, mcause, x0"
               : "=r"(mcause));
  if (mcause == 2)
  {
    illegal_count += 1;
  }

  printf("\n\t Back in M mode ");
  if (illegal_count != 2)
  {
    printf("\n\t Expected trap count = 2, but read as %d \n", illegal_count);
    exit(EXIT_FAILURE);
  }
  if (mcause == 2)
  {
    // printf("\n\t Illegal instruction exception triggered as expected ");
    // printf("\n\t Comparing pmpcfg values M:U mode ");

    asm volatile("csrrs %0, 0x3A9, x0"
                 : "=r"(pmpcfgx_after_test));
    // printf("\n\t pmpcfgx_after_test = 0x%lx\n", pmpcfgx_after_test);

    if (pmpcfgx_after_test != pmpcfgx_before_test)
    {
      printf("\n\t pmpcfg value overwritten, test failed\n");
      exit(EXIT_FAILURE);
    }
    else
    {
      printf("\n\t U mode pmpcfg test pass ");
      printf("\n\t ------------------------ \n");
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
  uint32_t pmpaddrx_before_test;
  uint32_t pmpaddrx_after_test;
  uint32_t temp[64] = {0};
  uint32_t mcause = 11111; // set an arbitrary value
  volatile int illegal_count = 0;
  printf("\n\t U mode pmpaddr test ");

  asm volatile("csrrs %0, 0x3Ba, x0\n"
               : "=r"(pmpaddrx_before_test));

  // change to Umode and try to write to csr, should trap
  umode();
  asm volatile("csrrw x0, 0x3ba, %0" ::"r"(temp[63]));
  // trap end the first time
  asm volatile("csrrw %0, mcause, x0"
               : "=r"(mcause));
  if (mcause == 2)
  {
    illegal_count += 1;
  }
  // change to Umode and try to read to csr, should trap
  umode();
  asm volatile("csrrs %0, 0x3ba, x0"
               : "=r"(temp[62]));
  // trap end the second time
  asm volatile("csrrw %0, mcause, x0"
               : "=r"(mcause));
  if (mcause == 2)
  {
    illegal_count += 1;
  }

  printf("\n\t Back in M mode ");
  if (illegal_count != 2)
  {
    printf("\n\t Expected trap count = 2, but read as %d \n", illegal_count);
    exit(EXIT_FAILURE);
  }
  if (mcause == 2)
  {
    // printf("\n\t Illegal instruction exception triggered as expected ");
    // printf("\n\t Comparing pmpaddr values M:U mode");
    asm volatile("csrrs %0, 0x3Ba, x0"
                 : "=r"(pmpaddrx_after_test));
    if (pmpaddrx_before_test != pmpaddrx_after_test)
    {
      printf("\n\t pmpaddr value overwritten, test failed\n");
      exit(EXIT_FAILURE);
    }
    else
    {
      printf("\n\t U mode pmpaddr test pass ");
      printf("\n\t ------------------------ \n");
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
  uint32_t mseccfg_before_test;
  uint32_t mseccfg_after_test;
  uint32_t temp[64] = {0};
  uint32_t mcause = 11111; // set an arbitrary value
  volatile int illegal_count = 0;
  // read the mseccfg(0x747) value before test and then to compare
  printf("\t U mode mseccfg check");
  asm volatile("csrrs %0, 0x747, x0"
               : "=r"(mseccfg_before_test));

  // change to Umode and try to write to csr, should trap
  umode();
  asm volatile("csrrs x0, 0x747, %0" ::"r"(temp[63]));
  // trap end the first time
  asm volatile("csrrw %0, mcause, x0"
               : "=r"(mcause));
  if (mcause == 2)
  {
    illegal_count += 1;
  }
  // change to Umode and try to read to csr, should trap
  umode();
  asm volatile("csrrs %0, 0x747, x0"
               : "=r"(temp[62]));
  // trap end the second time
  asm volatile("csrrw %0, mcause, x0"
               : "=r"(mcause));
  if (mcause == 2)
  {
    illegal_count += 1;
  }

  printf("\n\t Back in M mode ");
  if (illegal_count != 2)
  {
    printf("\n\t Expected trap count = 2, but read as %d \n", illegal_count);
    exit(EXIT_FAILURE);
  }
  if (mcause == 2)
  {
    // printf("\n\t Illegal instruction exception triggered as expected ");
    // printf("\n\t Comparing mseccfg values M:U mode");
    asm volatile("csrrs %0, 0x747, x0"
                 : "=r"(mseccfg_after_test));
    if (mseccfg_after_test != mseccfg_before_test)
    {
      printf("\n\t mseccfg values overwritten, test failed\n");
      exit(EXIT_FAILURE);
    }
    else
    {
      printf("\n\t U mode mseccfg test pass ");
      printf("\n\t ------------------------ \n");
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
