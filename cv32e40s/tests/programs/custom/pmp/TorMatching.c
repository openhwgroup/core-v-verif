#include "pmp.h"

#define ABOVEDEBUG 0x10000

void tor_macthing()
{
  int temp;
  int tor = (1 << 3), read = 1, write = 1 << 1, exe = 1 << 2, lock = 1 << 7;
  // set pmp addr to 0xffff-ffff
  // asm volatile(
  //     "li t0, 0xFFFFFFFF\n"
  //     "csrrw x0, pmpaddr0, t0\n"
  //     "li t0, ((1<<3)+7)\n"
  //     "csrrw x0, 0x3a0, t0\n");

  // write certain values to designated RAM region in M mode
  // for (uint32_t i = ABOVEDEBUG; i <= ABOVEDEBUG + 4 * 150; i++)
  // {
  asm volatile("sw %0, 0(%1)" ::"r"(1), "r"(ABOVEDEBUG));
  asm volatile("sw %0, 0(%1)" ::"r"(5), "r"(ABOVEDEBUG - 5));

  // }

  //  TODO:R
  //  set pmp regions from ABOVEDEBUG - ABOVEDEBUG+4*150
  asm volatile("csrrw x0, 0x3b0, %0\n"
               "csrrw x0, 0x3b1, %1\n" ::"r"(ABOVEDEBUG>>2),
               "r"((ABOVEDEBUG>>2)+256));
  // set pmp mode to TOR for pmpaddr0 & pmpaddr1
  // asm volatile("csrrw x0, 0x3a0, %0" ::"r"(tor | tor << 8));
  // set RAM to read
  // asm volatile("csrrw x0, 0x3a0, %0" ::"r"(read | read << 8));
  // set pmp.l to enforce rules ???
  // asm volatile("csrrw x0, 0x3a0, %0" ::"r"(lock | lock << 8));
  // set pmpcfg0/1 read and TOR

  // asm volatile("csrrw x0, 0x3a0, %0" ::"r"(0x8900));
  asm volatile("csrrwi x0, 0x3a0, 0x8900");

  // umode();
  // asm volatile("csrrs %0, 0x3a , x0"
  //              : "=r"(temp));
  // printf("\t\n0x3a0 value is %x\n\n", temp);

  asm volatile("lw %0, 0(%1)"
               : "=r"(temp)
               : "r"(ABOVEDEBUG));
  printf("\t\n loading from address 0x%x\n", ABOVEDEBUG);
  printf("\t\n value %d\n\n", temp);

  asm volatile("lw %0, 0(%1)"
               : "=r"(temp)
               : "r"(ABOVEDEBUG - 5));
  printf("\t\n loading from address 0x%x\n", ABOVEDEBUG - 5);
  printf("\t\n value %d\n\n", temp);

  asm volatile("lw %0, 0(%1)"
               : "=r"(temp)
               : "r"(ABOVEDEBUG + 4 * 500));
  printf("\t\n loading from address 0x%x\n", ABOVEDEBUG +4*500);
  printf("\t\n value %d\n\n", temp);

  // TODO:RW

  // TODO:RX

  // TODO:X
}