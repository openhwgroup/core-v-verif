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
**  - Count memory read transactions
**  - Count memory write transactions
**  - Count jumps
**  - Count branches (conditional)
**  - Count branches taken (conditional)
**  - Compressed instructions
**
** The test is therefore unnecessarily complex for the task
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define MAX_STALL_CYCLES 5

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

static int chck_with_pos_margin(unsigned int is, unsigned int should, unsigned int margin)
{
  int err;
  err = (is >= should) && (is <= should + margin) ? 0 : 1;
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
  volatile unsigned int count_while_on;

  volatile unsigned int mcycle_count;

  //////////////////////////////////////////////////////////////
  // Cycle count
  printf("\nCycle count");

  // Setup events and set csrs to 0
  __asm__ volatile("csrwi 0xB00, 0x0");
  __asm__ volatile("csrwi 0xB02, 0x0");

  // Readback Counter to verify 0
  __asm__ volatile("csrr %0, 0xB00" : "=r"(mcycle_count));
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));
  printf("\nCheck proper zeroization\n");
  err_cnt += chck(minstret, 0);

  // Enable counters
  __asm__ volatile("csrwi 0x320, 0x0");

  __asm__ volatile("csrr t0, minstret\n\t\
                    addi t1, x0, 0\n\t\
                    addi t2, x0, 0" \
                    : : : "t0", "t1", "t2");

  __asm__ volatile("csrwi 0x320, 0x5");
  __asm__ volatile("csrr %0, 0xB00" : "=r"(mcycle_count));
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);
  printf("\nMCYCLE counted cycles = %d\n", mcycle_count);
  err_cnt += chck_with_pos_margin(mcycle_count, 5, 4*MAX_STALL_CYCLES);

  //////////////////////////////////////////////////////////////
  // IF_INVALID
  printf("\nIF_INVALID");

  __asm__ volatile("csrwi 0xB02, 0x0");
  __asm__ volatile("csrwi 0x320, 0x0");

  __asm__ volatile("addi t1, x0, 0\n\t\
                    addi t0, x0, 5\n\t\
                    branch_target_ifinv_1: addi t1, t1, 1\n\t\
                    bne t0, t1, branch_target_ifinv_1\n\t\
                    nop" \
                    : : : "t0", "t1");

  __asm__ volatile("csrwi 0x320, 0x5");
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4+(2*5));


  //////////////////////////////////////////////////////////////
  // ID_INVALID - LD_STALL
  printf("\nID_INVALID");

  __asm__ volatile("csrwi 0xB02, 0x0");
  __asm__ volatile("csrwi 0x320, 0x0");

  __asm__ volatile("lw x4, 0(sp)\n\t\
                    addi x5, x4, 1\n\t\
                    lw x6, 0(sp)\n\t\
                    addi x7, x0, 1" \
                    : : : "x4", "x5", "x6", "x7");

  __asm__ volatile("csrwi 0x320, 0x5");
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 5);

  //////////////////////////////////////////////////////////////
  // ID_INVALID - JR STALL
  printf("\nID_INVALID");
  __asm__ volatile("csrwi 0xB02, 0x0");
  __asm__ volatile("csrwi 0x320, 0x0");

  __asm__ volatile("auipc x4, 0\n\t\
                    jalr x0, x4, 8\n\t\
                    nop" \
                    : : : "x4");

  __asm__ volatile("csrwi 0x320, 0x5");
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  //////////////////////////////////////////////////////////////
  // EX_INVALID
  printf("\nEX_INVALID");

  __asm__ volatile("csrwi 0xB02, 0x0");
  __asm__ volatile("csrwi 0x320, 0x0");

  __asm__ volatile("lw x0, 0(x0)");
  __asm__ volatile("lw x31, 0(x31)");
  __asm__ volatile("lw x30, 0(x30)");
  __asm__ volatile("lw x29, 0(x29)");
  __asm__ volatile("lw x28, 0(x28)");
  __asm__ volatile("mulh x0, x0, x0");                            // 3 cycles
  __asm__ volatile("li x31, 4");
  __asm__ volatile("li x30, 3");
  __asm__ volatile("mulh x0, x31, x30");                          // 3 cycles
  __asm__ volatile("li x31, 9");
  __asm__ volatile("li x30, 7");;
  __asm__ volatile("mulh x0, x31, x30");                          // 3 cycles
  __asm__ volatile("li x31, 47");
  __asm__ volatile("li x30, 17");
  __asm__ volatile("div x0, x31, x30");                           // 32 cycles
  __asm__ volatile("li x31, 1");
  __asm__ volatile("li x30, 1");
  __asm__ volatile("div x0, x31, x30");                           // 32 cycles
  __asm__ volatile("rem x0, x31, x30");                           // 32 cycles
  __asm__ volatile("lw x0, 0(sp)");

  __asm__ volatile("csrwi 0x320, 0x5");
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 21);

  //////////////////////////////////////////////////////////////
  // WB_INVALID Write port underutilization

  printf("\nWrite port underutilization");
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters

  __asm__ volatile("li x31, 1\n\t\
                    li x30, 1\n\t\
                    div x0, x31, x30\n\t\
                    lw x29, 0(sp)\n\t\
                    sw x29, 0(sp)" \
                    : : : "x28", "x29", "x30", "x31");

  __asm__ volatile("csrwi 0x320, 0x5");                        // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 6);

  //////////////////////////////////////////////////////////////
  // WB_DATA_STALL Write port underutilization due to data_rvalid_i (0)
  printf("\nWrite port underutilization due to data_rvalid_i");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters

  __asm__ volatile("li x31, 7\n\t\
                    li x30, 3\n\t\
                    addi x0, x31, 1\n\t\
                    lw x29, 0(sp)\n\t\
                    lw x28, -1(sp)\n\t\
                    srli x30, x29, 2\n\t\
                    slli x30, x30, 2\n\t\
                    xori x30, x30, 1\n\t\
                    sw x29, 0(x30)\n\t\
                    sw x29, 0(sp)\n\t\
                    lw x28, -1(sp)\n\t\
                    csrr x29, 0xB00\n\t\
                    div x0, x31, x30" \
                    : : : "x28", "x29", "x30", "x31");

  __asm__ volatile("csrwi 0x320, 0x5");                        // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 14);

  //////////////////////////////////////////////////////////////
  // Retired instruction count (0) - Immediate minstret read
  printf("\nRetired instruction count (0)");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters

  __asm__ volatile("csrr t0, minstret\n\t\
                    addi t1, x0, 0\n\t\
                    addi t2, x0, 0" \
                    : : : "t0", "t1", "t2");
  __asm__ volatile("csrwi 0x320, 0x5");                        // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("addi %0, t0, 0" : "=r"(count_while_on));    // count_while_on

  printf("\nminstret count while running = %d\n", count_while_on);
  err_cnt += chck(count_while_on, 0);

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  //////////////////////////////////////////////////////////////
  // Retired instruction count (1) - minstret read-after-write
  printf("\nRetired instruction count (1)");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("csrwi minstret, 0xA\n\t\
                    csrr t0, minstret\n\t\
                    addi t1, x0, 0\n\t\
                    addi t2, x0, 0\n\t\
                    nop" \
                    : : : "t0", "t1", "t2");
  __asm__ volatile("csrwi 0x320, 0x5");                         // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("addi %0, t0, 0" : "=r"(count_while_on));    //

  printf("\nminstret count while running = %d\n", count_while_on);
  err_cnt += chck(count_while_on, 0xA);

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 0xF);

  //////////////////////////////////////////////////////////////
  // Retired instruction count (2)
  printf("\nRetired instruction count (2)");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("sw x0, 0(sp)\n\t\
                    addi t0, x0, 5\n\t\
                    addi t1, x0, 0\n\t\
                    addi t2, x0, 0\n\t\
                    lw t2, 0(sp)\n\t\
                    branch_target: addi t2, t2, 1\n\t\
                    addi t1, t1, 1\n\t\
                    lw t2, 0(sp)\n\t\
                    sw t1, 0(sp)\n\t\
                    sw t1, 0(sp)\n\t\
                    bne t0, t1, branch_target\n\t\
                    j jump_target\n\t\
                    lw t2, 0(sp)\n\t\
                    lw t2, 0(sp)\n\t\
                    jump_target: nop\n\t\
                    nop\n\t\
                    nop" \
                    : : : "t0", "t1", "t2");
  __asm__ volatile("csrwi 0x320, 0x5");                        // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));         // minstret

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 5 + 6*5 + 4 + 1);

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
                    jalr x0, x4, 0x0" \
                    : : : "x4");
  __asm__ volatile("csrwi 0x320, 0x5");                         // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  //////////////////////////////////////////////////////////////
  // Count memory read transactions - Read while enabled
  printf("\nCount memory read transactions (0)");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("lw x0, 0(sp)\n\t\
                    csrr t0, mhpmcounter3\n\t\
                    addi t1, x0, 0\n\t\
                    addi t2, x0, 0" \
                    : : : "t0", "t1", "t2");
  __asm__ volatile("csrwi 0x320, 0x5");                         // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 5);

  //////////////////////////////////////////////////////////////
  // Count memory read transactions - Write after load event
  printf("\nCount memory read transactions (1)");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("lw x0, 0(sp)\n\t\
                    csrwi mhpmcounter3, 0xA\n\t\
                    addi t1, x0, 0\n\t\
                    addi t2, x0, 0" \
                    : : : "t0", "t1", "t2");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("addi %0, t0, 0" : "=r"(count_while_on));    // count_while_on

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 5);

  //////////////////////////////////////////////////////////////
  // Count memory read transactions
  printf("\nCount memory read transactions (2)");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("lw x0, 0(sp)");                             // count++
  __asm__ volatile("mulh x0, x0, x0");
  __asm__ volatile("j jump_target_memread");                    // do not count jump in mphmevent3
  __asm__ volatile("nop");                                      // do not count nop in instret
  __asm__ volatile("jump_target_memread:");
  __asm__ volatile("lw x0, 0(sp)");                             // count++
  __asm__ volatile("csrwi 0x320, 0x5");                        // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 5);

  //////////////////////////////////////////////////////////////
  // Count memory write transactions
  printf("\nCount memory write transactions");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("sw x0, 0(sp)");                             // count++
  __asm__ volatile("mulh x0, x0, x0");
  __asm__ volatile("sw x0, 0(sp)");                             // count++
  __asm__ volatile("csrwi 0x320, 0x5");                        // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  //////////////////////////////////////////////////////////////
  // Count jumps
  printf("\nCount jumps");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("j jump_target_0");                          // count++
  __asm__ volatile("jump_target_0:");
  __asm__ volatile("j jump_target_1");                          // count++
  __asm__ volatile("jump_target_1:");
  __asm__ volatile("csrwi 0x320, 0x5");                        // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 3);

  //////////////////////////////////////////////////////////////
  // Count branches (conditional)
  printf("\nCount branches (conditional)");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("beq x0, x0, branch_target_0");              // count++
  __asm__ volatile("branch_target_0:");
  __asm__ volatile("bne x0, x0, branch_target_1");              // count++
  __asm__ volatile("branch_target_1:");
  __asm__ volatile("beq x0, x0, branch_target_2");              // count++
  __asm__ volatile("branch_target_2:");
  __asm__ volatile("csrwi 0x320, 0x5");                         // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  //////////////////////////////////////////////////////////////
  // Count branches taken (conditional)
  printf("\nCount branches taken (conditional)");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("beq x0, x0, branch_target_3");              // count++
  __asm__ volatile("branch_target_3:");
  __asm__ volatile("bne x0, x0, branch_target_4");              // (not taken)
  __asm__ volatile("branch_target_4:");
  __asm__ volatile("beq x0, x0, branch_target_5");              // count++
  __asm__ volatile("branch_target_5:");
  __asm__ volatile("csrwi 0x320, 0x5");                         // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  //////////////////////////////////////////////////////////////
  // Compressed instructions
  printf("\nCompressed instructions");

  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("c.addi x15, 1\n\t\
                    c.nop\n\t\
                    c.addi x15, 1" \
                    : : : "x15");
  __asm__ volatile("csrwi 0x320, 0x5");                         // Inhibit mcycle, minstret
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  //////////////////////////////////////////////////////////////
  // Check for errors
  printf("\nDone\n\n");

  if (err_cnt)
    printf("FAILURE. %d errors\n\n", err_cnt);
  else
    printf("SUCCESS\n\n");

  return err_cnt;
}
