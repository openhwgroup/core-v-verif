#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:

	# CSR_MIP
	li x6, 0xa5a5a5a5
	csrrw x12, 836, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 836, x6
	li x6, 0x00000020
	bne x6, x12, csr_fail
	li x6, 0xffa1ae40
	csrrw x12, 836, x6
	li x6, 0x00000202
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 836, x6
	li x6, 0x00000200
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 836, x6
	li x6, 0x00000220
	bne x6, x12, csr_fail
	li x6, 0x17b2f37e
	csrrs x12, 836, x6
	li x6, 0x00000222
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 836, x6
	li x6, 0x00000222
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 836, x6
	li x6, 0x00000202
	bne x6, x12, csr_fail
	li x6, 0x797104c0
	csrrc x12, 836, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 836, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 836, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 836, 0b01000
	li x6, 0x00000002
	bne x6, x12, csr_fail
	csrrsi x12, 836, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 836, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 836, 0b00000
	li x6, 0x00000002
	bne x6, x12, csr_fail
	csrrci x12, 836, 0b00101
	li x6, 0x00000002
	bne x6, x12, csr_fail
	csrrci x12, 836, 0b11010
	li x6, 0x00000002
	bne x6, x12, csr_fail
	csrrci x12, 836, 0b01100
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrr x12, 836
	li x6, 0x00000000
	bne x6, x12, csr_fail
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
