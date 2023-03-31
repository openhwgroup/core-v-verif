#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:

RVMODEL_BOOT
	# CSR_MCOUNTEREN
	li x14, 0xa5a5a5a5
	csrrw x3, 774, x14
	li x14, 0x00000000
	bne x14, x3, csr_fail
	li x14, 0x5a5a5a5a
	csrrw x3, 774, x14
	li x14, 0xa5a5a5a5
	bne x14, x3, csr_fail
	li x14, 0xf1811b91
	csrrw x3, 774, x14
	li x14, 0x5a5a5a5a
	bne x14, x3, csr_fail
	li x14, 0xa5a5a5a5
	csrrs x3, 774, x14
	li x14, 0xf1811b91
	bne x14, x3, csr_fail
	li x14, 0x5a5a5a5a
	csrrs x3, 774, x14
	li x14, 0xf5a5bfb5
	bne x14, x3, csr_fail
	li x14, 0x33487fde
	csrrs x3, 774, x14
	li x14, 0xffffffff
	bne x14, x3, csr_fail
	li x14, 0xa5a5a5a5
	csrrc x3, 774, x14
	li x14, 0xffffffff
	bne x14, x3, csr_fail
	li x14, 0x5a5a5a5a
	csrrc x3, 774, x14
	li x14, 0x5a5a5a5a
	bne x14, x3, csr_fail
	li x14, 0xff06b67c
	csrrc x3, 774, x14
	li x14, 0x00000000
	bne x14, x3, csr_fail
	csrrwi x3, 774, 0b00101
	li x14, 0x00000000
	bne x14, x3, csr_fail
	csrrwi x3, 774, 0b11010
	li x14, 0x00000005
	bne x14, x3, csr_fail
	csrrwi x3, 774, 0b00010
	li x14, 0x0000001a
	bne x14, x3, csr_fail
	csrrsi x3, 774, 0b00101
	li x14, 0x00000002
	bne x14, x3, csr_fail
	csrrsi x3, 774, 0b11010
	li x14, 0x00000007
	bne x14, x3, csr_fail
	csrrsi x3, 774, 0b00011
	li x14, 0x0000001f
	bne x14, x3, csr_fail
	csrrci x3, 774, 0b00101
	li x14, 0x0000001f
	bne x14, x3, csr_fail
	csrrci x3, 774, 0b11010
	li x14, 0x0000001a
	bne x14, x3, csr_fail
	csrrci x3, 774, 0b00101
	li x14, 0x00000000
	bne x14, x3, csr_fail
	csrr x3, 774
	li x14, 0x00000000
	bne x14, x3, csr_fail
csr_pass:
	li x1, 0
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, t5
	self_loop: j self_loop

csr_fail:
	li x1, 1
	slli x1, x1, 1
	addi x1, x1, 1
	sw x1, tohost, t5
	self_loop_2: j self_loop_2

RVMODEL_DATA_BEGIN
RVMODEL_DATA_END
