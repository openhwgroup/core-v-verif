# RISC-V assembly test program to demonstrate write/read access to all 32 bits of the mscratch CSR (0x340).
# This program writes specific bit patterns to mscratch and reads them back to verify access.
# It uses a simple loop to check walking 1s across all 32 bits, and also tests all 0s and all 1s.
# If all tests pass, it writes 0 to the exit address (0x20000004); otherwise writes 1.
# Assume running in machine mode (m-mode) with appropriate privileges.
# The write to 0x20000004 signals the testbench to finish the simulation.

.section .text
.global _start

_start:
    # Test 1: Write 0x00000000 and read back
    li t0, 0x00000000
    csrw mscratch, t0
    csrr t1, mscratch
    bne t0, t1, fail

    # Test 2: Write 0xFFFFFFFF and read back
    li t0, 0xFFFFFFFF
    csrw mscratch, t0
    csrr t1, mscratch
    bne t0, t1, fail

    # Test 3: Write 0xAAAAAAAA (alternating bits) and read back
    li t0, 0xAAAAAAAA
    csrw mscratch, t0
    csrr t1, mscratch
    bne t0, t1, fail

    # Test 4: Write 0x55555555 (alternating bits inverted) and read back
    li t0, 0x55555555
    csrw mscratch, t0
    csrr t1, mscratch
    bne t0, t1, fail

    # Test 5-36: Walking 1s across all 32 bits
    li t2, 1          # Start with bit 0 set
    li t3, 0          # Counter for 32 bits
walk_loop:
    mv t0, t2         # Write current walking 1 value
    csrw mscratch, t0
    csrr t1, mscratch
    bne t0, t1, fail  # Check if read matches write

    slli t2, t2, 1    # Shift left to next bit
    addi t3, t3, 1
    li t4, 32
    blt t3, t4, walk_loop

    # If all tests pass, go to pass
    j pass

fail:
    li a0, 1          # Failure code
    j exit

pass:
    li a0, 0          # Success code

exit:
    lui t0, 0x20000   # Exit address base: 0x20000000
    sw a0, 4(t0)      # Write to 0x20000004
    j .               # Infinite loop to prevent further execution (optional, as TB will finish)
