// Copyright (c) 2026 devalgupta4@gmail.com
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

#define TEST_PASS                     123456789
#define TEST_FAIL                             1
#define VIRT_PERIPH_STATUS_FLAG_ADDR 0x20000000

.section .text
.globl main
main:

    li  t0, 0x00000000                       // All zeros
    csrw 0x340, t0
    csrr t1, 0x340
    bne  t1, t0, fail

    li  t0, 0xFFFFFFFF                       // All ones
    csrw 0x340, t0
    csrr t1, 0x340
    bne  t1, t0, fail

    li  t0, 0x55555555                       // Alternating bits
    csrw 0x340, t0
    csrr t1, 0x340
    bne  t1, t0, fail

    li  t0, 0xAAAAAAAA                       // Alternating bits
    csrw 0x340, t0
    csrr t1, 0x340
    bne  t1, t0, fail

    li  t0, 1                                // walking ones
walking_ones:
    csrw 0x340, t0
    csrr t1, 0x340
    bne  t1, t0, fail
    slli t0, t0, 1
    bnez t0, walking_ones

    li  t2, 1                                // walking zeros
walking_zeros:
    not t0, t2
    csrw 0x340, t0
    csrr t1, 0x340
    bne  t1, t0, fail
    slli t2, t2, 1
    bnez t2, walking_zeros

    li   t0, 0                               // atomic CSR operations
    csrw 0x340, t0

    li   t0, 0xFF
    csrrs t1, 0x340, t0
    bnez t1, fail

    li   t0, 0xF0
    csrrc t1, 0x340, t0
    li   t2, 0x0F
    csrr t3, 0x340
    bne  t3, t2, fail

pass:
    li t0, TEST_PASS
    li t1, VIRT_PERIPH_STATUS_FLAG_ADDR
    sw t0, 0(t1)
    j pass

fail:
    li t0, TEST_FAIL
    li t1, VIRT_PERIPH_STATUS_FLAG_ADDR
    sw t0, 0(t1)
    j fail
