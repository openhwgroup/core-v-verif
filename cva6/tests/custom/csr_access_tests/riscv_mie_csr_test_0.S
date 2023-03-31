#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
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

RVMODEL_DATA_BEGIN
RVMODEL_DATA_END
