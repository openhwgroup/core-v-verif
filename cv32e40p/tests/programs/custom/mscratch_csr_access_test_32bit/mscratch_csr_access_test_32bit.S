.section .text
.global main
main:
    # Test 1: Write 0x00000000 to mscratch
    li t0, 0x00000000
    csrw mscratch, t0
    csrr t1, mscratch
    bne t0, t1, fail

    # Test 2: Write 0xFFFFFFFF
    li t0, 0xFFFFFFFF
    csrw mscratch, t0
    csrr t1, mscratch
    bne t0, t1, fail

    # Test 3: Write 0xAAAAAAAA
    li t0, 0xAAAAAAAA
    csrw mscratch, t0
    csrr t1, mscratch
    bne t0, t1, fail

    # Test 4: Write 0x55555555
    li t0, 0x55555555
    csrw mscratch, t0
    csrr t1, mscratch
    bne t0, t1, fail

    # Test 5-36: Walking 1s across all 32 bits
    li t2, 1
    li t3, 0
walk_loop:
    mv t0, t2
    csrw mscratch, t0
    csrr t1, mscratch
    bne t0, t1, fail
    slli t2, t2, 1
    addi t3, t3, 1
    li t4, 32
    blt t3, t4, walk_loop

    j pass  # Jump to set a0=0 and exit

fail:
    li a0, 1
    j exit

pass:
    li a0, 0

exit:
    lui t0, 0x20000
    sw a0, 4(t0)
    j .  # Infinite loop