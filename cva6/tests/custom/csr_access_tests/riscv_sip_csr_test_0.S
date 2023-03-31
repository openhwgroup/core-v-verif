#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:

RVMODEL_BOOT

	## set start address range t0 x7
 	la x7, supervisor_code
 	li x28, 0x10000
 	add x7, x7, x28
 	# Enable R,W,X,TOR IN PMPCFG CSR t0 x8
 	li x8, 0x0F
	#set PMPADDR0 CSR with x7
 	csrw 0x3B0, x7
	# set PMPCFG0 CSR with x8
 	csrw 0x3A0, x8


	# Save the current mode in x28
        csrr x28, 0x300

        # Set the MPP field to supervisor mode (1)
        li x29, 0b1
        slli x29, x29, 11
        or x28, x28, x29

        # Write the modified MSTATUS value back to the CSR
        csrw 0x300, x28
	la x28, supervisor_code
        csrw 0x341, x28
	csrr x31, 0x300

	mret

        
# Supervisor code starts here
supervisor_code:
	# CSR_SIP
	li x4, 0xa5a5a5a5
	csrrw x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0x5a5a5a5a
	csrrw x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0x5fab96d2
	csrrw x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0xa5a5a5a5
	csrrs x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0x5a5a5a5a
	csrrs x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0x4e0941cd
	csrrs x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0xa5a5a5a5
	csrrc x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0x5a5a5a5a
	csrrc x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0x3d3e2982
	csrrc x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrwi x10, 324, 0b00101
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrwi x10, 324, 0b11010
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrwi x10, 324, 0b00011
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrsi x10, 324, 0b00101
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrsi x10, 324, 0b11010
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrsi x10, 324, 0b10101
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrci x10, 324, 0b00101
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrci x10, 324, 0b11010
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrci x10, 324, 0b01110
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrr x10, 324
	li x4, 0x00000000
	bne x4, x10, csr_fail
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
