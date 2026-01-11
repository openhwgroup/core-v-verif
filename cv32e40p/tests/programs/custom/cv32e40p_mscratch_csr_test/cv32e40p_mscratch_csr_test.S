# Copyright (c) 2026 OpenHW Group
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.include "user_define.h"

.section .text.start
.globl _start

.section .text

_start:
    j _start_main

_start_main:
    # All zeros and all ones patterns
    li x29, '1'
    li x15, 0x00000000
    csrw 0x340, x15           
    csrr x11, 0x340           
    bne x11, x15, csr_fail
    
    li x15, 0xFFFFFFFF
    csrw 0x340, x15           
    csrr x11, 0x340           
    bne x11, x15, csr_fail

    # Detects adjacent bit shorts (bridging faults)
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

    j test_done

test_done:
    lui a0, print_port>>12
    addi a1, zero, '\n'
    sw a1, 0(a0)
    addi a1, zero, 'C'
    sw a1, 0(a0)
    addi a1, zero, 'S'
    sw a1, 0(a0)
    addi a1, zero, 'R'
    sw a1, 0(a0)
    addi a1, zero, ' '
    sw a1, 0(a0)
    addi a1, zero, 'D'
    sw a1, 0(a0)
    addi a1, zero, 'O'
    sw a1, 0(a0)
    addi a1, zero, 'N'
    sw a1, 0(a0)
    addi a1, zero, 'E'
    sw a1, 0(a0)
    addi a1, zero, '\n'
    sw a1, 0(a0)

csr_pass:
    li x18, 123456789         
    li x17, 0x20000000       
    sw x18, 0(x17)
    wfi                      

csr_fail:
    lui a0, print_port>>12
    addi a1, zero, '\n'
    sw a1, 0(a0)
    addi a1, zero, 'C'
    sw a1, 0(a0)
    addi a1, zero, 'S'
    sw a1, 0(a0)
    addi a1, zero, 'R'
    sw a1, 0(a0)
    addi a1, zero, ' '
    sw a1, 0(a0)
    addi a1, zero, 'F'
    sw a1, 0(a0)
    addi a1, zero, 'A'
    sw a1, 0(a0)
    addi a1, zero, 'I'
    sw a1, 0(a0)
    addi a1, zero, 'L'
    sw a1, 0(a0)
    addi a1, zero, ' '
    sw a1, 0(a0)
    addi a1, zero, 'E'
    sw a1, 0(a0)
    addi a1, zero, ':'
    sw a1, 0(a0)
    sw x29, 0(a0)             
    addi a1, zero, '\n'
    sw a1, 0(a0)
    
    li x18, 1                 
    li x17, 0x20000000        
    sw x18, 0(x17)
    wfi                       