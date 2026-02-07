# Copyright (c) 2026 Lennan Tuffy
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.globl _start
.globl main
.section .text
.global exit, exit_failure
.equ EXIT_SUCCESS, 123456789
.equ EXIT_FAILURE, 1
.equ EXIT_STATUS,  0x20000000

.macro test_rw testnum, data
  li a0, \testnum
  li t0, \data
  csrw mscratch, t0
  csrr t1, mscratch
  bne t0, t1, exit_failure
.endm

main:
  test_rw 0, 0x00000000
  test_rw 1, 0xffffffff
  test_rw 2, 0xaaaaaaaa
  test_rw 3, 0x55555555

  csrw mscratch, zero
  li t0, 0x00000001
  li a0, 0x4

loop:
  csrrs t1, mscratch, t0
  bne zero, t1, exit_failure
  addi a0, a0, 1

  csrrc t1, mscratch, t0
  bne t0, t1, exit_failure
  addi a0, a0, 1

  slli t0, t0, 1
  bne t0, zero, loop

  li a1, EXIT_SUCCESS
  j exit
exit_failure:
  li a1, EXIT_FAILURE
exit:
  li a2, EXIT_STATUS
  sw a1, 0(a2)
  wfi
