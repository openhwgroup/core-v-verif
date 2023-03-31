#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
RVMODEL_BOOT
	# CSR_MCAUSE
	li x3, 0xa5a5a5a5
	csrrw x14, 834, x3
	li x3, 0x00000000
	bne x3, x14, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x14, 834, x3
	li x3, 0xa5a5a5a5
	bne x3, x14, csr_fail
	li x3, 0x77b01936
	csrrw x14, 834, x3
	li x3, 0x5a5a5a5a
	bne x3, x14, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x14, 834, x3
	li x3, 0x77b01936
	bne x3, x14, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x14, 834, x3
	li x3, 0xf7b5bdb7
	bne x3, x14, csr_fail
	li x3, 0xd2e9bfc7
	csrrs x14, 834, x3
	li x3, 0xffffffff
	bne x3, x14, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x14, 834, x3
	li x3, 0xffffffff
	bne x3, x14, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x14, 834, x3
	li x3, 0x5a5a5a5a
	bne x3, x14, csr_fail
	li x3, 0xdf872ab5
	csrrc x14, 834, x3
	li x3, 0x00000000
	bne x3, x14, csr_fail
	csrrwi x14, 834, 0b00101
	li x3, 0x00000000
	bne x3, x14, csr_fail
	csrrwi x14, 834, 0b11010
	li x3, 0x00000005
	bne x3, x14, csr_fail
	csrrwi x14, 834, 0b01101
	li x3, 0x0000001a
	bne x3, x14, csr_fail
	csrrsi x14, 834, 0b00101
	li x3, 0x0000000d
	bne x3, x14, csr_fail
	csrrsi x14, 834, 0b11010
	li x3, 0x0000000d
	bne x3, x14, csr_fail
	csrrsi x14, 834, 0b10100
	li x3, 0x0000001f
	bne x3, x14, csr_fail
	csrrci x14, 834, 0b00101
	li x3, 0x0000001f
	bne x3, x14, csr_fail
	csrrci x14, 834, 0b11010
	li x3, 0x0000001a
	bne x3, x14, csr_fail
	csrrci x14, 834, 0b00110
	li x3, 0x00000000
	bne x3, x14, csr_fail
	csrr x14, 834
	li x3, 0x00000000
	bne x3, x14, csr_fail
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
