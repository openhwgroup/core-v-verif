#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x0
_start:
RVMODEL_BOOT

 	la x7, supervisor_code
 	li x28, 0x10000
 	add x7, x7, x28
 	
 	li x8, 0x0F
 	
 	csrw 0x3B0, x7
 	csrw 0x3A0, x8
        # Set the MPP field to supervisor mode (1)
        li x29, 0b11
        slli x29, x29, 11
        or x28, x28, x29

	# Write the modified MSTATUS value back to the CSR
        csrw 0x300, x28

	# Load address of supervisor code
	la x28, supervisor_code
	#set MEPC register to address of supervisor code
        csrw 0x341, x28

	csrr x31, 0x300
	
      	mret
# Supervisor code starts here
supervisor_code:
 	# CSR_SEPC
	li x12, 0xa5a5a5a5
	csrrw x6, 321, x12
	li x12, 0x00000000
	bne x12, x6, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x6, 321, x12
	li x12, 0xa5a5a5a4
	bne x12, x6, csr_fail
	li x12, 0x7a6c28e1
	csrrw x6, 321, x12
	li x12, 0x5a5a5a5a
	bne x12, x6, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x6, 321, x12
	li x12, 0x7a6c28e0
	bne x12, x6, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x6, 321, x12
	li x12, 0xffedade4
	bne x12, x6, csr_fail
	li x12, 0x1228d835
	csrrs x6, 321, x12
	li x12, 0xfffffffe
	bne x12, x6, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x6, 321, x12
	li x12, 0xfffffffe
	bne x12, x6, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x6, 321, x12
	li x12, 0x5a5a5a5a
	bne x12, x6, csr_fail
	li x12, 0x712201a4
	csrrc x6, 321, x12
	li x12, 0x00000000
	bne x12, x6, csr_fail
	csrrwi x6, 321, 0b00101
	li x12, 0x00000000
	bne x12, x6, csr_fail
	csrrwi x6, 321, 0b11010
	li x12, 0x00000004
	bne x12, x6, csr_fail
	csrrwi x6, 321, 0b00010
	li x12, 0x0000001a
	bne x12, x6, csr_fail
	csrrsi x6, 321, 0b00101
	li x12, 0x00000002
	bne x12, x6, csr_fail
	csrrsi x6, 321, 0b11010
	li x12, 0x00000006
	bne x12, x6, csr_fail
	csrrsi x6, 321, 0b01001
	li x12, 0x0000001e
	bne x12, x6, csr_fail
	csrrci x6, 321, 0b00101
	li x12, 0x0000001e
	bne x12, x6, csr_fail
	csrrci x6, 321, 0b11010
	li x12, 0x0000001a
	bne x12, x6, csr_fail
	csrrci x6, 321, 0b11110
	li x12, 0x00000000
	bne x12, x6, csr_fail
	csrr x6, 321
	li x12, 0x00000000
	bne x12, x6, csr_fail

csr_pass:
	li x1, 0
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, x30
	self_loop: j self_loop

csr_fail:
	li x1, 1
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, x30
	self_loop_2: j self_loop_2

RVMODEL_DATA_BEGIN
RVMODEL_DATA_END


