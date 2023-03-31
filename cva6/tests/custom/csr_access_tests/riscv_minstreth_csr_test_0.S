#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:

RVMODEL_BOOT
	# CSR_MINSTRET_H
	li x8, 0xa5a5a5a5
	csrrw x7, 2946, x8
	li x8, 0x00000000
	bne x8, x7, csr_fail
	li x8, 0x5a5a5a5a
	csrrw x7, 2946, x8
	li x8, 0xa5a5a5a5
	bne x8, x7, csr_fail
	li x8, 0xe7630821
	csrrw x7, 2946, x8
	li x8, 0x5a5a5a5a
	bne x8, x7, csr_fail
	li x8, 0xa5a5a5a5
	csrrs x7, 2946, x8
	li x8, 0xe7630821
	bne x8, x7, csr_fail
	li x8, 0x5a5a5a5a
	csrrs x7, 2946, x8
	li x8, 0xe7e7ada5
	bne x8, x7, csr_fail
	li x8, 0xb569db45
	csrrs x7, 2946, x8
	li x8, 0xffffffff
	bne x8, x7, csr_fail
	li x8, 0xa5a5a5a5
	csrrc x7, 2946, x8
	li x8, 0xffffffff
	bne x8, x7, csr_fail
	li x8, 0x5a5a5a5a
	csrrc x7, 2946, x8
	li x8, 0x5a5a5a5a
	bne x8, x7, csr_fail
	li x8, 0x38a2b2e0
	csrrc x7, 2946, x8
	li x8, 0x00000000
	bne x8, x7, csr_fail
	csrrwi x7, 2946, 0b00101
	li x8, 0x00000000
	bne x8, x7, csr_fail
	csrrwi x7, 2946, 0b11010
	li x8, 0x00000005
	bne x8, x7, csr_fail
	csrrwi x7, 2946, 0b01100
	li x8, 0x0000001a
	bne x8, x7, csr_fail
	csrrsi x7, 2946, 0b00101
	li x8, 0x0000000c
	bne x8, x7, csr_fail
	csrrsi x7, 2946, 0b11010
	li x8, 0x0000000d
	bne x8, x7, csr_fail
	csrrsi x7, 2946, 0b00000
	li x8, 0x0000001f
	bne x8, x7, csr_fail
	csrrci x7, 2946, 0b00101
	li x8, 0x0000001f
	bne x8, x7, csr_fail
	csrrci x7, 2946, 0b11010
	li x8, 0x0000001a
	bne x8, x7, csr_fail
	csrrci x7, 2946, 0b11100
	li x8, 0x00000000
	bne x8, x7, csr_fail
	csrr x7, 2946
	li x8, 0x00000000
	bne x8, x7, csr_fail
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
