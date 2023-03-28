/*
**
** Copyright 2020 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
** SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
**
*******************************************************************************
**
** Performance counter directed test
**
** Very basic sanity check for:
**
**  - Retired Instruction Counter
**  - Cycle counter
**
** This test is derived from a test that also checked the hpmcounters on 40x; where it tested:
**  - Count load use hazards
**  - Count jump register hazards
**
** The test is therefore unnecessarily complex for the task
**
** Make sure to only run this test without wait states on instr_gnt_i/
** instr_rvalid_i. The test should tolerate wait states on data_gnt_i/
** data_rvalid_i.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int chck(unsigned int is, unsigned int should)
{
  int err;
  err = is == should ? 0 : 1;
  if (err)
    printf("fail\n");
  else
    printf("pass\n");
  return err;
}

int main(int argc, char *argv[])
{
  int err_cnt = 0;

  volatile unsigned int minstret;

  //////////////////////////////////////////////////////////////
  // Count load use hazards
  printf("\nCount load use hazards");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("lw x4, 0(sp)\n\t\
                    addi x5, x4, 1\n\t\
                    lw x6, 0(sp)\n\t\
                    addi x7, x0, 1" \
                    : : : "x4", "x5", "x6", "x7");
  __asm__ volatile("csrwi 0x320, 0x5");                         // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 5);

  //////////////////////////////////////////////////////////////
  // Count jump register hazards
  printf("\nCount Jump register hazards");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("auipc x4, 0x0\n\t\
                    addi x4, x4, 10\n\t\
                    jalr x28, x4, 0x0" \
                    : : : "x4");
  __asm__ volatile("csrwi 0x320, 0x5");                         // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  //////////////////////////////////////////////////////////////
  // Check for errors
  printf("\nDone");

  if (err_cnt)
    printf("FAILURE. %d errors\n\n", err_cnt);
  else
    printf("SUCCESS\n\n");

  return err_cnt;
}
