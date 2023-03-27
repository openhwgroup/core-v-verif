// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
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

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#define  EXCEPTION_INSN_ACCESS_FAULT      1
#define  EXCEPTION_LOAD_ACCESS_FAULT      5
#define  EXCEPTION_STOREAMO_ACCESS_FAULT  7

/* CFG Memory Layout
 *
 * [r0, "main"]
 * 0xFFFF_FFFF
 * 0x1A11_1000         <MEM_ADDR_1>
 *
 * [not a region]
 * 0x1A11_1000
 * 0x1A11_0800 + 16    <IO_ADDR>
 *
 * [r1, "main"]
 * 0x1A11_0800 + 16
 * 0x0000_0000         <MEM_ADDR_0>
 */
#define  MEM_ADDR_0        0
#define  IO_ADDR           (0x1A110800 + 16)
#define  MEM_ADDR_1        0x1A111000
#define  MTVAL_READ        0
#define  TBLJ_TARGET_ADDR  (IO_ADDR + 8)

static volatile uint32_t  g_mcause = 0;
static volatile uint32_t  g_mepc   = 0;
static volatile uint32_t  g_mtval  = 0;


// Exception-causing Instructions

static void (*instr_access_fault)(void) = (void (*)(void))IO_ADDR;

void misaligned_store(void) {
  uint32_t tmp;
  tmp = 0xBBBBBBBB;
  __asm__ volatile("sw %0, 1(%1)" : "=r"(tmp) : "r"(IO_ADDR));
}

void load_misaligned_io(void)     {__asm__ volatile("lw t0, 3(%0)" : : "r"(IO_ADDR) : "t0");}
static void load_aligned_io(void) {__asm__ volatile("lw t0, 0(%0)" : : "r"(IO_ADDR) : "t0");}
void load_misaligned_io2(void)    {__asm__ volatile("lw t0, 5(%0)" : : "r"(IO_ADDR) : "t0");}

void load_misaligned_iomem(void)     {__asm__ volatile("lw t0, 0(%0)" : : "r"(MEM_ADDR_1 - 2) : "t0");}
static void load_aligned_iomem(void) {__asm__ volatile("lh t0, 0(%0)" : : "r"(MEM_ADDR_1 - 2) : "t0");}

void load_misaligned_memio(void)     {__asm__ volatile("lw t0, 0(%0)" : : "r"(IO_ADDR - 1) : "t0");}
static void load_aligned_memio(void) {__asm__ volatile("lb t0, 0(%0)" : : "r"(IO_ADDR - 1) : "t0");}

void store_first_access(void)  {__asm__ volatile("sw %0,  2(%1)" : : "r"(0x11223344), "r"(IO_ADDR));}
void store_second_access(void) {__asm__ volatile("sw %0, -2(%1)" : : "r"(0x22334455), "r"(MEM_ADDR_1));}


// Utility Functions

__attribute__ ((interrupt))
void u_sw_irq_handler(void) {  // overrides a "weak" symbol in the bsp
  uint32_t ra;

  __asm__ volatile( R"(
    addi %[ra],     ra, 0
    csrr %[mcause], mcause
    csrr %[mepc],   mepc
    csrr %[mtval],  mtval
    )"
    : [ra]     "=r"(ra),
      [mcause] "=r"(g_mcause),
      [mepc]   "=r"(g_mepc),
      [mtval]  "=r"(g_mtval)
  );

  printf("(exec in u_sw_irq_handler: mcause=%lx, mepc=%lx)\n", g_mcause, g_mepc);

  __asm__ volatile("csrw mepc, %0" : : "r"(ra));
  return;
}

static void assert_or_die(uint32_t actual, uint32_t expect, char *msg) {
  if (actual != expect) {
    printf(msg);
    printf("pma: expected = 0x%lx (%ld), got = 0x%lx (%ld)\n", expect, (int32_t)expect, actual, (int32_t)actual);
    exit(EXIT_FAILURE);
  }
}

static void reset_volatiles(void) {
  g_mcause = -1;
  g_mepc   = -1;
  g_mtval  = -1;
}


// Tests

static void check_load_vs_regfile(void) {
  volatile uint32_t  tmp;
  volatile uint32_t  rd_pre;
  volatile uint32_t  rd_post;

  // check misaligned in IO
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0xAAAAAAAA), "r"(IO_ADDR) : "memory");
  __asm__ volatile("sw %0, 4(%1)" : : "r"(0xBBBBBBBB), "r"(IO_ADDR) : "memory");
  {
    // misaligned: regfile untouched
    __asm__ volatile( R"(
      mv   %[rd_pre],   t0
      jal  ra,          load_misaligned_io
      mv   %[rd_post],  t0
      )"
      : [rd_pre]  "=r"(rd_pre),
        [rd_post] "=r"(rd_post)
      :
      : "ra", "memory"
    );  // t0 must be "rd" in load_misaligned_io()
    assert_or_die(rd_post, rd_pre, "error: misaligned IO load shouldn't touch regfile\n");
  }
  {
    // aligned: regfile touched
    load_aligned_io();
    __asm__ volatile("mv %0, t0" : "=r"(tmp):: "t0", "memory");
    assert_or_die(tmp, 0xAAAAAAAA, "error: aligned IO load should touch regfile\n");
  }

  // check misaligned border from IO to MEM
  __asm__ volatile("sw %0, -4(%1)" : : "r"(0xAAAAAAAA), "r"(MEM_ADDR_1) : "memory");
  __asm__ volatile("sw %0,  0(%1)" : : "r"(0xBBBBBBBB), "r"(MEM_ADDR_1) : "memory");
  {
    // misaligned: regfile untouched
    __asm__ volatile( R"(
      mv   %[rd_pre],   t0
      jal  ra,          load_misaligned_iomem  # IO->MEM border
      mv   %[rd_post],  t0
      )"
      : [rd_pre]  "=r"(rd_pre),
        [rd_post] "=r"(rd_post)
      :
      : "ra", "memory"
    );
    assert_or_die(rd_post, rd_pre, "error: misaligned IO/MEM load shouldn't touch regfile\n");
  }
  {
    // aligned: regfile touched
    load_aligned_iomem();
    __asm__ volatile("mv %0, t0" : "=r"(tmp):: "t0", "memory");
    assert_or_die(tmp, 0xFFFFAAAA, "error: aligned IO/MEM load should touch regfile\n");
  }

  // check misaligned border from MEM to IO
  __asm__ volatile("sw %0, -4(%1)" : : "r"(0xAAAAAAAA), "r"(IO_ADDR) : "memory");
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0xBBBBBBBB), "r"(IO_ADDR) : "memory");
  {
    // misaligned: regfile untouched
    __asm__ volatile( R"(
      mv   %[rd_pre],   t0
      jal  ra,          load_misaligned_memio  # MEM->IO border
      mv   %[rd_post],  t0
      )"
      : [rd_pre]  "=r"(rd_pre),
        [rd_post] "=r"(rd_post)
      :
      : "ra", "memory"
    );
    assert_or_die(rd_post, rd_pre, "error: misaligned MEM/IO load shouldn't touch regfile\n");
  }
  {
    // aligned: regfile touched
    load_aligned_memio();
    __asm__ volatile("mv %0, t0" : "=r"(tmp):: "t0", "memory");
    assert_or_die(tmp, 0xFFFFFFAA, "error: aligned MEM/IO load should touch regfile\n");
  }

  // TODO:INFO:silabs-robin  can one programmatically confirm that these addresses are indeed in such regions as intended?
}


int main(void) {
  uint32_t tmp;

  printf("\nHello, PMA test!\n\n");
  assert_or_die(g_mcause, 0, "error: mcause variable should initially be 0\n");
  assert_or_die(g_mepc,   0, "error: mepc variable should initially be 0\n");
  assert_or_die(g_mtval,  0, "error: mtval variable should initially be 0\n");

  // TODO:INFO:silabs-robin  "mtval" could in the future not be read-only read-zero.


  printf("pma: 1. Exec should only work for 'main memory' regions\n");

  reset_volatiles();
  instr_access_fault();
  assert_or_die(g_mcause, EXCEPTION_INSN_ACCESS_FAULT, "error: expected instruction access fault\n");
  assert_or_die(g_mepc, IO_ADDR, "error: expected different mepc\n");
  assert_or_die(g_mtval, MTVAL_READ, "error: expected different mtval\n");


  printf("pma: 2. Non-naturally aligned stores to I/O regions\n");

  printf("pma: sanity check that aligned stores are ok\n");
  reset_volatiles();
  tmp = 0xAAAAAAAA;
  __asm__ volatile("sw %0, 0(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(g_mcause, -1, "error: aligned store should not change mcause\n");
  assert_or_die(g_mepc, -1, "error: aligned store should not change mepc\n");
  assert_or_die(g_mtval, -1, "error: aligned store should not change mtval\n");

  printf("pma: check that misaligned stores except\n");
  reset_volatiles();
  __asm__ volatile("jal ra, misaligned_store");
  assert_or_die(g_mcause, EXCEPTION_STOREAMO_ACCESS_FAULT, "error: misaligned store unexpected mcause\n");
  assert_or_die(g_mtval,  MTVAL_READ, "error: misaligned store unexpected mtval\n");

  printf("pma: check that misaligned store to MEM is alright\n");
  reset_volatiles();
  tmp = 0xCCCCCCCC;
  __asm__ volatile("sw %0, -9(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(g_mcause, -1, "error: misaligned store to main affected mcause\n");
  assert_or_die(g_mepc, -1, "error: misaligned store to main affected mepc\n");
  assert_or_die(g_mtval, -1, "error: misaligned store to main affected mtval\n");


  printf("pma: 3. Non-naturally aligned loads within I/O regions\n");

  printf("pma: sanity check that aligned load is no problem\n");
  reset_volatiles();
  tmp = 0;
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmp) : "r"(IO_ADDR));  // Depends on "store" test filling memory first
  assert_or_die(!tmp, 0, "error: load should not yield zero\n");  // TODO:WARNING:silabs-robin  ensure memory content matches
  assert_or_die(g_mcause, -1, "error: natty access should not change mcause\n");
  assert_or_die(g_mepc, -1, "error: natty access should not change mepc\n");
  assert_or_die(g_mtval, -1, "error: natty access should not change mtval\n");

  printf("pma: check that misaligned load will except\n");
  reset_volatiles();
  __asm__ volatile("jal ra, load_misaligned_io2");
  assert_or_die(g_mcause, EXCEPTION_LOAD_ACCESS_FAULT, "error: misaligned IO load should except\n");
  assert_or_die(g_mtval, MTVAL_READ, "error: misaligned IO load unexpected mtval\n");
  // TODO:INFO:silabs-robin  more kinds of |addr[0:1]? Try LH too?

  printf("pma: check that misaligned to MEM does not fail\n");
  reset_volatiles();
  tmp = 0;
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmp) : "r"(0x80));
  assert_or_die(!tmp, 0, "error: load from main should not yield zero\n");
  assert_or_die(g_mcause, -1, "error: main access should not change mcause\n");
  assert_or_die(g_mepc, -1, "error: main access should not change mepc\n");
  assert_or_die(g_mtval, -1, "error: main access should not change mtval\n");


  printf("pma: 4. Misaligned load fault shouldn't touch regfile\n");

  printf("pma: check that various split load access fault leaves regfile untouched\n");
  check_load_vs_regfile();


  printf("pma: 5. Misaligned store fault shouldn't reach bus in second access\n");

  printf("pma: check IO store failing in first access\n");
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0xAAAAAAAA), "r"(IO_ADDR));
  __asm__ volatile("sw %0, 4(%1)" : : "r"(0xBBBBBBBB), "r"(IO_ADDR));
  __asm__ volatile("jal ra, store_first_access");
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(tmp, 0xAAAAAAAA, "error: misaligned first store entered bus\n");
  __asm__ volatile("lw %0, 4(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(tmp, 0xBBBBBBBB, "error: misaligned second store entered bus\n");
  // TODO:INFO:silabs-robin  how to programmatically confirm that these region settings match as intended?

  printf("pma: check IO to MEM store failing in first access\n");
  __asm__ volatile("sw %0, -4(%1)" : : "r"(0xAAAAAAAA), "r"(MEM_ADDR_1));
  __asm__ volatile("sw %0, 0(%1)" : : "r"(0xBBBBBBBB), "r"(MEM_ADDR_1));
  __asm__ volatile("jal ra, store_second_access");
  __asm__ volatile("lw %0, -4(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
  assert_or_die(tmp, 0xAAAAAAAA, "error: misaligned IO/MEM first store entered bus\n");
  __asm__ volatile("lw %0, 0(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
  assert_or_die(tmp, 0xBBBBBBBB, "error: misaligned IO/MEM second store entered bus\n");
  // TODO:INFO:silabs-robin  how to programmatically confirm that these region settings match as intended?


/* A-ext not for 40s
  printf("pma: 6. Atomics should work only where it is allowed\n");

  printf("pma: Sanity check that atomic ops (lr/sc) to allowed regions is ok\n");
  reset_volatiles();
  __asm__ volatile("lr.w %0, 0(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
  __asm__ volatile("sc.w %0, %0, 0(%1)" : "=r"(tmp) : "r"(MEM_ADDR_1));
  assert_or_die(g_mcause, -1, "error: atomics to legal region should not except\n");
  assert_or_die(g_mepc, -1, "error: atomics to legal region unexpected mepc\n");
  assert_or_die(g_mtval, -1, "error: atomics to legal region unexpected mtval\n");

  printf("pma: Load-reserved to disallowed regions raises precise exception\n");
  reset_volatiles();
  __asm__ volatile("lr.w %0, 0(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(g_mcause, EXCEPTION_LOAD_ACCESS_FAULT, "error: load-reserved to non-atomic should except\n");
  assert_or_die(g_mepc, IO_ADDR, "error: load-reserved to non-atomic unexpected mepc\n");
  assert_or_die(g_mtval, MTVAL_READ, "error: load-reserved to non-atomic unexpected mtval\n");

  printf("pma: Store-conditional to disallowed regions raises precise exception\n");
  reset_volatiles();
  __asm__ volatile("sc.w %0, %0, 0(%1)" : "=r"(tmp) : "r"(IO_ADDR));
  assert_or_die(g_mcause, EXCEPTION_STOREAMO_ACCESS_FAULT, "error: store-conditional to non-atomic should except\n");
  assert_or_die(g_mepc, IO_ADDR, "error: store-conditional to non-atomic unexpected mepc\n");
  assert_or_die(g_mtval, MTVAL_READ, "error: store-conditional to non-atomic unexpected mtval\n");
*/


  // Zc features are in the vplan, but are much easier to check with assertions.


  printf("\nGoodbye, PMA test!\n\n");
  return EXIT_SUCCESS;
}
