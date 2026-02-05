# Copyright (c) 2026 Sumeyya Aktas
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.include "user_define.h"

.equ TRAP_HANDLED, 0x70617373    # Translates to "PASS"

.section .text.start
.globl _start

.section .rodata
msg_pass: .string "\nCSR PASS\n"
msg_fail: .string "\nCSR FAIL Test: "
msg_trap_handled: .string "\nSuccessfully ran trap handler\n"

.section .text

_start:
    # All zeros and all ones
    li x29, '1'
    li x15, 0x00000000
    csrw 0x340, x15           
    csrr x11, 0x340           
    bne x11, x15, csr_fail
    
    li x15, 0xFFFFFFFF
    csrw 0x340, x15           
    csrr x11, 0x340           
    bne x11, x15, csr_fail

    # Bridging faults
    li x29, '2'
    li x15, 0x55555555        
    csrw 0x340, x15
    csrr x11, 0x340
    bne x11, x15, csr_fail
    
    li x15, 0xAAAAAAAA        
    csrw 0x340, x15
    csrr x11, 0x340
    bne x11, x15, csr_fail

    li x29, '3'
    li x15, 1
walking_ones:
    csrw 0x340, x15
    csrr x11, 0x340
    bne x11, x15, csr_fail
    slli x15, x15, 1          
    bnez x15, walking_ones    

    li x29, '4'
    li x16, 1
walking_zeros:
    not x15, x16              
    csrw 0x340, x15
    csrr x11, 0x340
    bne x11, x15, csr_fail
    slli x16, x16, 1          
    bnez x16, walking_zeros   

    # Forces all 32 latches to toggle simultaneously to test stability
    li x29, '5'
    li x15, 0x12345678        
    csrw 0x340, x15
    not x16, x15              
    csrw 0x340, x16           
    csrr x11, 0x340
    bne x11, x16, csr_fail

    # Atomic CSRRS / CSRRC behavior
    li x29, '6'

    li x15, 0x0
    csrw 0x340, x15
    
    # Atomic set (CSRRS) 
    li x15, 0xFF
    csrrs x11, 0x340, x15     
    bnez x11, csr_fail        
    
    # Atomic clear (CSRRC) 
    li x16, 0xF0
    csrrc x11, 0x340, x16     
    li x17, 0x0F
    csrr x12, 0x340           
    bne x12, x17, csr_fail

    # Testing mtvec and the trap mechanism
    # to ensure traps land at the correct handler
    li x29, '7'
    la x15, trap_handler
    csrw mtvec, x15
    li x31, 0                 
    ecall   

    # Print "PASS" here instead of printing it inside
    # trap_handler since it might overwrite 'ra' 
    la a0, msg_trap_handled
    jal ra, print_string                  

    li x15, TRAP_HANDLED
    bne x31, x15, csr_fail

    j csr_pass

.align 4
trap_handler:
    csrr x30, mcause
    li x31, 11
    bne x30, x31, csr_fail

    li x31, TRAP_HANDLED

    csrr x30, mepc
    addi x30, x30, 4
    csrw mepc, x30
    mret

csr_pass:
    la a0, msg_pass
    jal ra, print_string
    
    li x18, 123456789        
    li x17, 0x20000000        
    sw x18, 0(x17)
    wfi                       

csr_fail:
    la a0, msg_fail
    jal ra, print_string

    lui t0, print_port>>12
    sw x29, 0(t0)
    addi t1, zero, '\n'
    sw t1, 0(t0)

    li x18, 1                 
    li x17, 0x20000000        
    sw x18, 0(x17)
    wfi

print_string:
    lui t0, print_port>>12
1:
    lb t1, 0(a0)
    beqz t1, 2f
    sw t1, 0(t0)        
    addi a0, a0, 1
    j 1b
2:
    ret