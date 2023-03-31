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
        li x29, 0b11
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
	# CSR_SSCRATCH
	li x1, 0xa5a5a5a5
	csrrw x3, 320, x1
	li x1, 0x00000000
	bne x1, x3, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x3, 320, x1
	li x1, 0xa5a5a5a5
	bne x1, x3, csr_fail
	li x1, 0xf149b7e8
	csrrw x3, 320, x1
	li x1, 0x5a5a5a5a
	bne x1, x3, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x3, 320, x1
	li x1, 0xf149b7e8
	bne x1, x3, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x3, 320, x1
	li x1, 0xf5edb7ed
	bne x1, x3, csr_fail
	li x1, 0xbcc8c1c2
	csrrs x3, 320, x1
	li x1, 0xffffffff
	bne x1, x3, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x3, 320, x1
	li x1, 0xffffffff
	bne x1, x3, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x3, 320, x1
	li x1, 0x5a5a5a5a
	bne x1, x3, csr_fail
	li x1, 0x18fd947a
	csrrc x3, 320, x1
	li x1, 0x00000000
	bne x1, x3, csr_fail
	csrrwi x3, 320, 0b00101
	li x1, 0x00000000
	bne x1, x3, csr_fail
	csrrwi x3, 320, 0b11010
	li x1, 0x00000005
	bne x1, x3, csr_fail
	csrrwi x3, 320, 0b01010
	li x1, 0x0000001a
	bne x1, x3, csr_fail
	csrrsi x3, 320, 0b00101
	li x1, 0x0000000a
	bne x1, x3, csr_fail
	csrrsi x3, 320, 0b11010
	li x1, 0x0000000f
	bne x1, x3, csr_fail
	csrrsi x3, 320, 0b10100
	li x1, 0x0000001f
	bne x1, x3, csr_fail
	csrrci x3, 320, 0b00101
	li x1, 0x0000001f
	bne x1, x3, csr_fail
	csrrci x3, 320, 0b11010
	li x1, 0x0000001a
	bne x1, x3, csr_fail
	csrrci x3, 320, 0b00001
	li x1, 0x00000000
	bne x1, x3, csr_fail
	csrr x3, 320
	li x1, 0x00000000
	bne x1, x3, csr_fail



		# CSR_MIE
 	li x10, 0xa5a5a5a5
 	csrrw x13, 772, x10
 	li x10, 0x00000000
 	bne x10, x13, csr_fail
 	li x10, 0x5a5a5a5a
 	csrrw x13, 772, x10
 	li x10, 0x000000a0
 	bne x10, x13, csr_fail
 	li x10, 0xf8851108
 	csrrw x13, 772, x10
 	li x10, 0x00000a0a
 	bne x10, x13, csr_fail
 	li x10, 0xa5a5a5a5
 	csrrs x13, 772, x10
 	li x10, 0x00000008
 	bne x10, x13, csr_fail
 	li x10, 0x5a5a5a5a
 	csrrs x13, 772, x10
 	li x10, 0x000000a8
 	bne x10, x13, csr_fail
 	li x10, 0x11dcf0fa
 	csrrs x13, 772, x10
 	li x10, 0x00000aaa
 	bne x10, x13, csr_fail
 	li x10, 0xa5a5a5a5
 	csrrc x13, 772, x10
 	li x10, 0x00000aaa
 	bne x10, x13, csr_fail
 	li x10, 0x5a5a5a5a
 	csrrc x13, 772, x10
 	li x10, 0x00000a0a
 	bne x10, x13, csr_fail
 	li x10, 0x9216f083
 	csrrc x13, 772, x10
 	li x10, 0x00000000
 	bne x10, x13, csr_fail
 	csrrwi x13, 772, 0b00101
 	li x10, 0x00000000
 	bne x10, x13, csr_fail
 	csrrwi x13, 772, 0b11010
 	li x10, 0x00000000
 	bne x10, x13, csr_fail
 	csrrwi x13, 772, 0b10110
 	li x10, 0x0000000a
 	bne x10, x13, csr_fail
 	csrrsi x13, 772, 0b00101
 	li x10, 0x00000002
 	bne x10, x13, csr_fail
 	csrrsi x13, 772, 0b11010
 	li x10, 0x00000002
 	bne x10, x13, csr_fail
 	csrrsi x13, 772, 0b00110
 	li x10, 0x0000000a
 	bne x10, x13, csr_fail
 	csrrci x13, 772, 0b00101
 	li x10, 0x0000000a
 	bne x10, x13, csr_fail
 	csrrci x13, 772, 0b11010
 	li x10, 0x0000000a
 	bne x10, x13, csr_fail
 	csrrci x13, 772, 0b01011
 	li x10, 0x00000000
 	bne x10, x13, csr_fail
 	csrr x13, 772
 	li x10, 0x00000000
 	bne x10, x13, csr_fail

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


not_supervisor:
li x1, 1
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, x30
	self_loop_3: j self_loop_3

RVMODEL_DATA_BEGIN
RVMODEL_DATA_END
