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

static CSRS csrs;

void user_code()
{
  printf("\tChecking U mode RAM acess\n");
  // initialize to 0
  uint32_t myarray[64] = {0};
  for (int i = 0; i < 64; i++)
  {
    if (myarray[i] != 0)
    {
      printf("\tInconsistant value to initializer!\n");
      printf("\tmyarray[%d] = %lx\n", i, myarray[i]);
    }
  }

  for (int i = 0; i < 64; i++)
  {
    myarray[i] = i;

    if (myarray[i] != i)
    {
      printf("\tValues are not updated accordingly!\n");
      printf("\tExpected values = %d\n", i);
      printf("\tmyarray[%d] = %lx\n", i, myarray[i]);
    }
  }
  printf("\tU-mode has the access to RAM\n");
}

void pmpcfgxtest()
{
  uint32_t pmpcfgx;

  asm volatile("csrrs %0, 0x3A9, x0\n"
               : "=r"(pmpcfgx));

  change_mode();
  printf("\tU mode pmpcfg check\n");
  user_code();


  printf("\tAttempting writing or reading CSRS in U mode\n\n");
  // back from the trap, reading mstatus
  asm volatile("csrrw x0, mstatus, %0\n"
               : "=r"(pmpcfgx));

  printf("\tout of  handler\n");


  if (glb_csrs.mcause == 2)
  {
    printf("\tIllegal instruction exception triggered as expected\n");
    printf("\tComparing pmpcfgx values M:U\n");
    asm volatile("csrrs %0, 0x3A9, x0\n"
                 : "=r"(csrs.pmpcfgx[9]));
    if (pmpcfgx == csrs.pmpcfgx[9])
    {
      printf("\tpmpcfg[9] value is not overwriten\n\n");
    }
    else
    {
      printf("\tpmpcfg value is overwriten\n");
      printf("\tpmpcfg test failed\n\n");
      exit(EXIT_FAILURE);
    }
  }
}

void pmpaddrxtest()
{
  uint32_t pmpaddrx;

  asm volatile("csrrs %0, 0x3Ba, x0\n"
               : "=r"(pmpaddrx));

  change_mode();
  printf("\tU mode pmpaddr check\n");
  user_code();

  printf("\tAttempting writing or reading CSRS in U mode\n\n");
  // back from the trap, reading mstatus
  asm volatile("csrrw x0, mstatus, %0\n" ::"r"(pmpaddrx));

  printf("\tout of  handler\n");


  if (glb_csrs.mcause == 2)
  {
    printf("\tIllegal instruction exception triggered as expected\n");
    printf("\tComparing pmpaddr values M:U\n");
    asm volatile("csrrs %0, 0x3Ba, x0\n"
                 : "=r"(csrs.pmpaddrx[10]));
    if (pmpaddrx == csrs.pmpaddrx[10])
    {
      printf("\tpmpaddr[9] value is not overwriten\n\n");
    }
    else
    {
      printf("\tpmpaddr value is overwriten\n");
      printf("\tpmpaddr test failed\n\n");
      exit(EXIT_FAILURE);
    }
  }
}

void mseccfgtest()
{
  uint32_t mseccfg;

  asm volatile("csrrs %0, 0x747, x0\n"
               : "=r"(mseccfg));

  change_mode();
  printf("\tU mode mseccfg check\n");
  user_code();

  printf("\tAttempting writing or reading CSRS in U mode\n\n");
  // back from the trap, reading mstatus
  asm volatile("csrrw x0, mstatus, %0\n"
               :
               : "r"(mseccfg));

  printf("\tout of  handler\n");

  if (glb_csrs.mcause == 2)
  {
    printf("\tIllegal instruction exception triggered as expected\n");
    printf("\tComparing pmpcfgx values M:U\n");
    asm volatile("csrrs %0, 0x3A9, x0\n"
                 : "=r"(csrs.mseccfg));
    if (mseccfg == csrs.mseccfg)
    {
      printf("\tmseccfg value is not overwriten\n\n");
    }
    else
    {
      printf("\tpmpcfg value is overwriten\n");
      printf("\tpmpcfg test failed\n\n");
      exit(EXIT_FAILURE);
    }
  }
}

void mmode_only()
{
  // set pmp addr to 0xffff-ffff
  asm volatile(
      "li t0, 0xFFFFFFFF\n"
      "csrrw x0, pmpaddr0, t0\n"
      "li t0, ((1<<3)+7)\n"
      "csrrw x0, 0x3a0, t0\n");

  pmpcfgxtest();
  printf("----------------------------------\n");
  pmpaddrxtest();
  printf("----------------------------------\n");
  mseccfgtest();

  exit(EXIT_SUCCESS);
}
