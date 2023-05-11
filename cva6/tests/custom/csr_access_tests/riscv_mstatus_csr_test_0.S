#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
	# CSR_MSTATUS
	li x10, 0xa5a5a5a5
	csrrw x8, 768, x10
	li x10, 0x00000000
	bne x10, x8, csr_fail
	li x10, 0x5a5a5a5a
	csrrw x8, 768, x10
	li x10, 0x002421a1
	bne x10, x8, csr_fail
	li x10, 0xf87e4500
	csrrw x8, 768, x10
	li x10, 0x005a581a
	bne x10, x8, csr_fail
	li x10, 0xa5a5a5a5
	csrrs x8, 768, x10
	li x10, 0x007e4100
	bne x10, x8, csr_fail
	li x10, 0x5a5a5a5a
	csrrs x8, 768, x10
	li x10, 0x007e61a1
	bne x10, x8, csr_fail
	li x10, 0x14dad7b7
	csrrs x8, 768, x10
	li x10, 0x007e79bb
	bne x10, x8, csr_fail
	li x10, 0xa5a5a5a5
	csrrc x8, 768, x10
	li x10, 0x007e79bb
	bne x10, x8, csr_fail
	li x10, 0x5a5a5a5a
	csrrc x8, 768, x10
	li x10, 0x005a581a
	bne x10, x8, csr_fail
	li x10, 0xd4c9e763
	csrrc x8, 768, x10
	li x10, 0x00000000
	bne x10, x8, csr_fail
	csrrwi x8, 768, 0b00101
	li x10, 0x00000000
	bne x10, x8, csr_fail
	csrrwi x8, 768, 0b11010
	li x10, 0x00000001
	bne x10, x8, csr_fail
	csrrwi x8, 768, 0b11010
	li x10, 0x0000001a
	bne x10, x8, csr_fail
	csrrsi x8, 768, 0b00101
	li x10, 0x0000001a
	bne x10, x8, csr_fail
	csrrsi x8, 768, 0b11010
	li x10, 0x0000001b
	bne x10, x8, csr_fail
	csrrsi x8, 768, 0b00011
	li x10, 0x0000001b
	bne x10, x8, csr_fail
	csrrci x8, 768, 0b00101
	li x10, 0x0000001b
	bne x10, x8, csr_fail
	csrrci x8, 768, 0b11010
	li x10, 0x0000001a
	bne x10, x8, csr_fail
	csrrci x8, 768, 0b11100
	li x10, 0x00000000
	bne x10, x8, csr_fail
	csrr x8, 768
	li x10, 0x00000000
	bne x10, x8, csr_fail
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
