// Copyright (c) 2026 Abhay Partap Singh Gill
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

// -----------------------------------------------------------------------------
// mscratch CSR Read/Write test 
//
// This test validates correct behavior of the Machine Scratch CSR (mscratch,
// CSR address 0x340) using both register-based and immediate-based CSR
// instructions.
//
// The goal is to ensure:
//   - Correct read/write behavior
//   - Proper read-modify-write semantics
//   - No bit corruption across different access patterns
//   - Correct handling of immediate CSR masks (uimm[4:0])
//
// The test is fully self-checking and reports a unique FAIL ID on the first
// detected error.
// -----------------------------------------------------------------------------

// -----------------------------------------------------------------------------
// FAIL ID Reference
//
// Each failure jumps to a unique label that sets s0 to a specific ID.
// This allows quick identification of the failing test.
//
// SECTION A : Register CSR tests
//   1  -> Write 0x00000000 and read back
//   2  -> Write 0xFFFFFFFF and read back
//   3  -> Write 0xAAAAAAAA (alternating pattern)
//   4  -> Write 0x55555555 (inverse alternating pattern)
//   5  -> Walking-ones test failure
//   6  -> Walking-zeros test failure
//   7  -> Register-based SET (bit-by-bit) test failure
//   8  -> Register-based CLEAR (bit-by-bit) test failure
//
// SECTION B : Immediate CSR tests
//   9  -> Immediate write of zero failed
//  10  -> Immediate write of all ones (0x1F) failed
//  11  -> Immediate alternating pattern 0x15 failed
//  12  -> Immediate alternating pattern 0x0A failed
//  13  -> Immediate SET (bit-by-bit) test failed
//  14  -> Immediate CLEAR (bit-by-bit) test failed
//
// SECTION C : random set/reset tests
//  15  -> Register-based random SET test failed
//  16  -> Register-based random CLEAR test failed
//  17  -> Immediate random SET test failed
//  18  -> Immediate random CLEAR test failed
//
// PASS -> All mscratch CSR tests completed successfully
// -----------------------------------------------------------------------------

#define MSCRATCH_CSR   0x340
#define STATUS_ADDR    0x20000000
#define PRINT_PORT     0x10000000
#define PASS_CODE      123456789
#define FAIL_CODE      1

.section .text
.globl main

main:

/* ============================================================================
 * SECTION A : REGISTER-OPERAND CSR INSTRUCTIONS
 * ============================================================================ */

/* --- A.1 Read / Write ------------------------------------------------------ */

    li t0, 0x00000000
    csrrw x0, MSCRATCH_CSR, t0
    csrrw t1, MSCRATCH_CSR, x0
    bne  t1, t0, fail_A1

    li t0, 0xFFFFFFFF
    csrrw x0, MSCRATCH_CSR, t0
    csrrw t1, MSCRATCH_CSR, x0
    bne  t1, t0, fail_A2

    li t0, 0xAAAAAAAA
    csrrw x0, MSCRATCH_CSR, t0
    csrrw t1, MSCRATCH_CSR, x0
    bne  t1, t0, fail_A3

    li t0, 0x55555555
    csrrw x0, MSCRATCH_CSR, t0
    csrrw t1, MSCRATCH_CSR, x0
    bne  t1, t0, fail_A4

/* --- A.2 Walking ones ------------------------------------------------------ */

    li t0, 1
A_walk_ones:
    csrrw x0, MSCRATCH_CSR, t0
    csrrw t1, MSCRATCH_CSR, x0
    bne  t1, t0, fail_A5
    slli t0, t0, 1
    bnez t0, A_walk_ones

/* --- A.3 Walking zeros ----------------------------------------------------- */

    li t2, 1
A_walk_zeros:
    not  t0, t2
    csrrw x0, MSCRATCH_CSR, t0
    csrrw t1, MSCRATCH_CSR, x0
    bne  t1, t0, fail_A6
    slli t2, t2, 1
    bnez t2, A_walk_zeros

/* --- A.4 Set / Clear bit-by-bit ------------------------------------------- */

    csrrw x0, MSCRATCH_CSR, x0
    li t3, 0

    li t0, 1; li t1, 0x10000000
A_set_loop:
    csrrs x0, MSCRATCH_CSR, t0
    or    t3, t3,           t0
    slli  t0, t0,           1
    bnez  t0, A_set_loop
    csrrs t0, MSCRATCH_CSR, x0
    bne   t0, t3          , fail_A7

    li    t0, 0xFFFFFFFF
    csrrw x0, MSCRATCH_CSR, t0
    li    t0, 1
A_clr_loop:
    csrrc x0, MSCRATCH_CSR, t0
    xor   t3, t3, t0
    slli  t0, t0, 1
    bnez  t0, A_clr_loop
    csrrs t0, MSCRATCH_CSR, x0
    bne   t0, t3          , fail_A8


/* ============================================================================
 * SECTION B : IMMEDIATE-OPERAND CSR INSTRUCTIONS
 * NOTE: uimm is 5-bit wide → bits [4:0] only
 * ============================================================================ */

/* --- B.1 Read / Write ------------------------------------------------------ */

    csrrwi x0, MSCRATCH_CSR, 0
    csrrw  t1, MSCRATCH_CSR, x0
    bnez   t1, fail_B1

    csrrwi x0, MSCRATCH_CSR, 0x1F
    csrrw  t1, MSCRATCH_CSR, x0
    li     t0, 0x1F
    bne    t1, t0, fail_B2

/* --- B.2 Alternating ------------------------------------------------------- */

    csrrwi x0, MSCRATCH_CSR, 0x15
    csrrw  t1, MSCRATCH_CSR, x0
    li     t0, 0x15
    bne    t1, t0, fail_B3

    csrrwi x0, MSCRATCH_CSR, 0x0A
    csrrw  t1, MSCRATCH_CSR, x0
    li     t0, 0x0A
    bne    t1, t0, fail_B4

/* --- B.3 Immediate set / clear (bit-by-bit) -------------------------------- */

    csrrwi x0, MSCRATCH_CSR, 0
    li t3, 0

    csrrsi x0, MSCRATCH_CSR, 0x01 ; ori t3, t3, 0x01
    csrrsi x0, MSCRATCH_CSR, 0x02 ; ori t3, t3, 0x02
    csrrsi x0, MSCRATCH_CSR, 0x04 ; ori t3, t3, 0x04
    csrrsi x0, MSCRATCH_CSR, 0x08 ; ori t3, t3, 0x08
    csrrsi x0, MSCRATCH_CSR, 0x10 ; ori t3, t3, 0x10

    csrrw  t1, MSCRATCH_CSR, x0
    bne    t1, t3, fail_B5

    csrrci x0, MSCRATCH_CSR, 0x01
    csrrci x0, MSCRATCH_CSR, 0x02
    csrrci x0, MSCRATCH_CSR, 0x04
    csrrci x0, MSCRATCH_CSR, 0x08
    csrrci x0, MSCRATCH_CSR, 0x10

    csrrw  t1, MSCRATCH_CSR, x0
    bnez   t1, fail_B6

/* --- Random Stress test for set/clear ---------------------------*/

    csrrw x0, MSCRATCH_CSR, x0
    li    t0, 0x15
    csrrs x0, MSCRATCH_CSR, t0
    csrrw t1, MSCRATCH_CSR, t0
    bne   t1, t0, fail_c1

    li    t0, 0x15
    csrrc x0, MSCRATCH_CSR, t0
    csrrw t1, MSCRATCH_CSR, t0
    bnez  t1, fail_c2

    csrrwi x0, MSCRATCH_CSR, 0
    csrrsi x0, MSCRATCH_CSR, 0x15
    csrrw  t1, MSCRATCH_CSR, x0
    li     t0, 0x15
    bne    t1, t0, fail_c3

    csrrci x0, MSCRATCH_CSR, 0x15
    csrrw  t1, MSCRATCH_CSR, x0
    bnez   t1, fail_c4


/* ============================================================================
 * PASS / FAIL
 * ============================================================================ */

pass:
    li t0, PRINT_PORT
    li t1, 'A' ; sw t1, 0(t0)
    li t1, 'L' ; sw t1, 0(t0)
    li t1, 'L' ; sw t1, 0(t0)
    li t1, ' ' ; sw t1, 0(t0)
    li t1, 'T' ; sw t1, 0(t0)
    li t1, 'E' ; sw t1, 0(t0)
    li t1, 'S' ; sw t1, 0(t0)
    li t1, 'T' ; sw t1, 0(t0)
    li t1, 'S' ; sw t1, 0(t0)
    li t1, ' ' ; sw t1, 0(t0)
    li t1, 'P' ; sw t1, 0(t0)
    li t1, 'A' ; sw t1, 0(t0)
    li t1, 'S' ; sw t1, 0(t0)
    li t1, 'S' ; sw t1, 0(t0)
    li t1, 'E' ; sw t1, 0(t0)
    li t1, 'D' ; sw t1, 0(t0)
    li t1, '\n'; sw t1, 0(t0)

    li t2, PASS_CODE
    li t3, STATUS_ADDR
    sw t2, 0(t3)
    wfi

fail:
    li t0, PRINT_PORT
    li t1, 'F'      ; sb t1, 0(t0)
    li t1, 'A'      ; sb t1, 0(t0)
    li t1, 'I'      ; sb t1, 0(t0)
    li t1, 'L'      ; sb t1, 0(t0)
    li t1, 'E'      ; sb t1, 0(t0)
    li t1, 'D'      ; sb t1, 0(t0)
    li t1, ' '      ; sb t1, 0(t0)
    li t1, 'A'      ; sb t1, 0(t0)
    li t1, 'T'      ; sb t1, 0(t0)
    li t1, ' '      ; sb t1, 0(t0)
    li t1, 'T'      ; sb t1, 0(t0)
    li t1, 'E'      ; sb t1, 0(t0)
    li t1, 'S'      ; sb t1, 0(t0)
    li t1, 'T'      ; sb t1, 0(t0)
    li t1, '-'      ; sb t1, 0(t0)
    li t1, 'I'      ; sb t1, 0(t0)
    li t1, 'D'      ; sb t1, 0(t0)
    li t1, ' '      ; sb t1, 0(t0)
    li t1, ':'      ; sb t1, 0(t0)
    li t1, ' '      ; sb t1, 0(t0)
    addi t1, s0, '0'
    sw   t1, 0(t0)
    li t1, '\n'; sw t1, 0(t0)
    li t1, 'F'      ; sb t1, 0(t0)
    li t1, 'o'      ; sb t1, 0(t0)
    li t1, 'r'      ; sb t1, 0(t0)
    li t1, ' '      ; sb t1, 0(t0)
    li t1, 'T'      ; sb t1, 0(t0)
    li t1, 'e'      ; sb t1, 0(t0)
    li t1, 's'      ; sb t1, 0(t0)
    li t1, 't'      ; sb t1, 0(t0)
    li t1, '-'      ; sb t1, 0(t0)
    li t1, 'I'      ; sb t1, 0(t0)
    li t1, 'D'      ; sb t1, 0(t0)
    li t1, ' '      ; sb t1, 0(t0)
    li t1, 'r'      ; sb t1, 0(t0)
    li t1, 'e'      ; sb t1, 0(t0)
    li t1, 'f'      ; sb t1, 0(t0)
    li t1, 'e'      ; sb t1, 0(t0)
    li t1, 'r'      ; sb t1, 0(t0)
    li t1, ' '      ; sb t1, 0(t0)
    li t1, 't'      ; sb t1, 0(t0)
    li t1, 'o'      ; sb t1, 0(t0)
    li t1, ' '      ; sb t1, 0(t0)
    li t1, 'm'      ; sb t1, 0(t0)
    li t1, 's'      ; sb t1, 0(t0)
    li t1, 'c'      ; sb t1, 0(t0)
    li t1, 'r'      ; sb t1, 0(t0)
    li t1, 'a'      ; sb t1, 0(t0)
    li t1, 't'      ; sb t1, 0(t0)
    li t1, 'c'      ; sb t1, 0(t0)
    li t1, 'h'      ; sb t1, 0(t0)
    li t1, '_'      ; sb t1, 0(t0)
    li t1, 'c'      ; sb t1, 0(t0)
    li t1, 's'      ; sb t1, 0(t0)
    li t1, 'r'      ; sb t1, 0(t0)
    li t1, ' '      ; sb t1, 0(t0)
    li t1, 'c'      ; sb t1, 0(t0)
    li t1, 'u'      ; sb t1, 0(t0)
    li t1, 's'      ; sb t1, 0(t0)
    li t1, 't'      ; sb t1, 0(t0)
    li t1, 'o'      ; sb t1, 0(t0)
    li t1, 'm'      ; sb t1, 0(t0)
    li t1, ' '      ; sb t1, 0(t0)
    li t1, 't'      ; sb t1, 0(t0)
    li t1, 'e'      ; sb t1, 0(t0)
    li t1, 's'      ; sb t1, 0(t0)
    li t1, 't'      ; sb t1, 0(t0)
    li t1, ' '      ; sb t1, 0(t0)
    li t1, 'p'      ; sb t1, 0(t0)
    li t1, 'r'      ; sb t1, 0(t0)
    li t1, 'o'      ; sb t1, 0(t0)
    li t1, 'g'      ; sb t1, 0(t0)
    li t1, 'r'      ; sb t1, 0(t0)
    li t1, 'a'      ; sb t1, 0(t0)
    li t1, 'm'      ; sb t1, 0(t0)
    li t1, '\n'     ; sb t1, 0(t0)

    li s0, FAIL_CODE
    li t2, STATUS_ADDR
    sw s0, 0(t2)
    wfi

/* --- Failure IDs ---------------------------------------------------------- */

fail_A1: li s0, 1;  j fail
fail_A2: li s0, 2;  j fail
fail_A3: li s0, 3;  j fail
fail_A4: li s0, 4;  j fail
fail_A5: li s0, 5;  j fail
fail_A6: li s0, 6;  j fail
fail_A7: li s0, 7;  j fail
fail_A8: li s0, 8;  j fail

fail_B1: li s0, 9;  j fail
fail_B2: li s0, 10; j fail
fail_B3: li s0, 11; j fail
fail_B4: li s0, 12; j fail
fail_B5: li s0, 13; j fail
fail_B6: li s0, 14; j fail

fail_c1: li s0, 15; j fail
fail_c2: li s0, 16; j fail
fail_c3: li s0, 17; j fail
fail_c4: li s0, 18; j fail
