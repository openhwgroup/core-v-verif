// Copyright (c) 2026 abizerlokhandwalastd10@gmail.com
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.include "user_define.h"
.section .text.start
.globl _start
.section .text
.type _start, @function

_start:
    j _start_main

.globl _start_main
.section .text
_start_main:
    li x29, '1'               # Load error code
    
    li x15, 0xffffffff       
    csrrw x11, 832, x15       
    
    csrrs x11, 832, x0        
    li x15, 0xffffffff        
    bne x11, x15, csr_fail    # If mscratch != 0xFFFFFFFF, jump to fail 

    li x29, '2'               # Load error code

    li x15, 0x00000000        
    csrrw x11, 832, x15       
    
    csrrs x11, 832, x0        
    li x15, 0x00000000        
    bne x11, x15, csr_fail    # If mscratch != 0x0000000, jump to fail 

    li x29, '3'               # Load error code

    li x15, 0x55555555        # 0101... pattern
    csrw 832, x15
    csrr x11, 832
    bne x11, x15, csr_fail

    li x15, 0xAAAAAAAA        # 1010... pattern
    csrw 832, x15
    csrr x11, 832
    bne x11, x15, csr_fail

    li x29, '4'               # Load error code
    
    li x15, 1                 # Start with bit 0
walking_ones:
    csrw 832, x15             
    csrr x11, 832             
    bne x11, x15, csr_fail    
    slli x15, x15, 1          # Shift left by 1
    bnez x15, walking_ones    

    li x29, '5'               # Load error code

    li x16, 1
walking_zeros:
    not x15, x16              # Flip bits (e.g. 11110, 11101...)
    csrw 832, x15
    csrr x11, 832
    bne x11, x15, csr_fail
    slli x16, x16, 1
    bnez x16, walking_zeros
    
test_done:
    lui a0,print_port>>12 
    addi a1, zero, '\n'
    sw a1, 0(a0)
    addi a1, zero, 'C'
    sw a1, 0(a0)
    addi a1, zero, 'V'
    sw a1, 0(a0)
    addi a1, zero, '3'
    sw a1, 0(a0)
    addi a1, zero, '2'
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
    lui a0,print_port>>12 
    addi a1, zero, '\n'
    sw a1, 0(a0)
    addi a1, zero, 'C'
    sw a1, 0(a0)
    addi a1, zero, 'V'
    sw a1, 0(a0)
    addi a1, zero, '3'
    sw a1, 0(a0)
    addi a1, zero, '2'
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
    
    # PRINT THE ERROR CODE (1-5)
    sw x29, 0(a0)             # Print the test ID stored in x29
    
    addi a1, zero, '\n'
    sw a1, 0(a0)

    li x18, 1
    li x17, 0x20000000
    sw x18, 0(x17)
    wfi
