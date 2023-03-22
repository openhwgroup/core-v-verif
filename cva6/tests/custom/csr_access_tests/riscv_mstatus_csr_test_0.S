#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
	# CSR_MSTATUS
	li x12, 0xa5a5a5a5
	csrrw x10, 768, x12
	li x12, 0x00000000
	bne x12, x10, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x10, 768, x12
	li x12, 0x002421a0
	bne x12, x10, csr_fail
	li x12, 0xae5fb8b3
	csrrw x10, 768, x12
	li x12, 0x005a580a
	bne x12, x10, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x10, 768, x12
	li x12, 0x005e38a2
	bne x12, x10, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x10, 768, x12
	li x12, 0x007e39a2
	bne x12, x10, csr_fail
	li x12, 0x80df9787
	csrrs x10, 768, x12
	li x12, 0x007e79aa
	bne x12, x10, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x10, 768, x12
	li x12, 0x007e79aa
	bne x12, x10, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x10, 768, x12
	li x12, 0x005a580a
	bne x12, x10, csr_fail
	li x12, 0x3e464370
	csrrc x10, 768, x12
	li x12, 0x00000000
	bne x12, x10, csr_fail
	csrrwi x10, 768, 0b00101
	li x12, 0x00000000
	bne x12, x10, csr_fail
	csrrwi x10, 768, 0b11010
	li x12, 0x00000000
	bne x12, x10, csr_fail
	csrrwi x10, 768, 0b01100
	li x12, 0x0000000a
	bne x12, x10, csr_fail
	csrrsi x10, 768, 0b00101
	li x12, 0x00000008
	bne x12, x10, csr_fail
	csrrsi x10, 768, 0b11010
	li x12, 0x00000008
	bne x12, x10, csr_fail
	csrrsi x10, 768, 0b11100
	li x12, 0x0000000a
	bne x12, x10, csr_fail
	csrrci x10, 768, 0b00101
	li x12, 0x0000000a
	bne x12, x10, csr_fail
	csrrci x10, 768, 0b11010
	li x12, 0x0000000a
	bne x12, x10, csr_fail
	csrrci x10, 768, 0b00010
	li x12, 0x00000000
	bne x12, x10, csr_fail
	csrr x10, 768
	li x12, 0x00000000
	bne x12, x10, csr_fail
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
