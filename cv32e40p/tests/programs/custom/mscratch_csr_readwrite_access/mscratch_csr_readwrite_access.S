# Copyright (c) <2026> <Ammarah_wakeel>
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

###############################################################################
# Test: mscratch read/write access
#
# Purpose:
#   Verify that the mscratch CSR (0x340) is fully readable and writable
#   across all 32 bits on RV32 (CV32E40P).
#
# Method:
#   - Write known 32-bit patterns to mscratch
#   - Read them back
#   - Compare expected vs actual
#
# Result:
#   - PASS if all patterns match
#   - FAIL on first mismatch
###############################################################################

.globl _start
.globl main
.globl exit
.global debug
.section .text

#define MSCRATCH_CSR   0x340
#define TEST_PASS     0x12345678
#define TEST_FAIL     0x1
#define STATUS_ADDR   0x20000000


main:  # Label as main for entry point

    ###########################################################################
    # Pattern 1: all zeros
    ###########################################################################
    li      t0, 0x00000000
    csrw    MSCRATCH_CSR, t0
    csrr    t1, MSCRATCH_CSR
    bne     t0, t1, fail

    ###########################################################################
    # Pattern 2: all ones
    ###########################################################################
    li      t0, 0xFFFFFFFF
    csrw    MSCRATCH_CSR, t0
    csrr    t1, MSCRATCH_CSR
    bne     t0, t1, fail

    ###########################################################################
    # Pattern 3: alternating bits (1010...)
    ###########################################################################
    li      t0, 0xAAAAAAAA
    csrw    MSCRATCH_CSR, t0
    csrr    t1, MSCRATCH_CSR
    bne     t0, t1, fail

    ###########################################################################
    # Pattern 4: alternating bits (0101...)
    ###########################################################################
    li      t0, 0x55555555
    csrw    MSCRATCH_CSR, t0
    csrr    t1, MSCRATCH_CSR
    bne     t0, t1, fail

    ###########################################################################
    # Pattern 5: MSB only
    ###########################################################################
    li      t0, 0x80000000
    csrw    MSCRATCH_CSR, t0
    csrr    t1, MSCRATCH_CSR
    bne     t0, t1, fail

    ###########################################################################
    # Pattern 6: LSB only
    ###########################################################################
    li      t0, 0x00000001
    csrw    MSCRATCH_CSR, t0
    csrr    t1, MSCRATCH_CSR
    bne     t0, t1, fail

    ###########################################################################
    # All tests passed
    ###########################################################################
pass:
    li      t0, TEST_PASS
    li      t1, STATUS_ADDR
    sw      t0, 0(t1)
    j _exit

fail:
    li      t0, TEST_FAIL
    li      t1, STATUS_ADDR
    sw      t0, 0(t1)
    j _exit
    
end:
    j _exit
