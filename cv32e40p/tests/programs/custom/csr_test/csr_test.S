.globl _start
.globl main
.globl exit
.global debug
.section .text

#define mscratch  0x340
#define TEST_PASS 0
#define TEST_FAIL 1

main:

  li t0, 0x00000001
  csrw mscratch, t0
  csrr t1, mscratch
  bne t1, t0, .fail

  li t0, 0x80000001
  csrw mscratch, t0
  csrr t1, mscratch
  bne t1, t0, .fail

  li t0, 0x80000000
  csrw mscratch, t0
  csrr t1, mscratch
  bne t1, t0, .fail

  li t0, 0x01234567
  csrw mscratch, t0
  csrr t1, mscratch
  bne t1, t0, .fail

  li t0, 0xABCDEF98
  csrw mscratch, t0
  csrr t1, mscratch
  bne t1, t0, .fail

  li t0, 0xFFFFFFFF
  csrw mscratch, t0
  csrr t1, mscratch
  bne t1, t0, .fail

  li t0, 0x00000000
  csrw mscratch, t0
  csrr t1, mscratch
  bne t1, t0, .fail

  li t0, 0xAAAAAAAA
  csrw mscratch, t0
  csrr t1, mscratch
  bne t1, t0, .fail

  li t0, 0x55555555
  csrw mscratch, t0
  csrr t1, mscratch
  bne t1, t0, .fail

  # Passed tests
  li s1, TEST_PASS
  j _exit


.fail:
  li s1, TEST_FAIL
  j _exit
