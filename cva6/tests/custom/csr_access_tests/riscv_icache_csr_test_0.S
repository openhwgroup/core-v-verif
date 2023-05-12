#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
	# CSR_ICACHE
	li x5, 0xa5a5a5a5
	csrrw x1, 1792, x5
	li x5, 0x00000001
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrw x1, 1792, x5
	li x5, 0x00000001
	bne x5, x1, csr_fail
	li x5, 0x4261da52
	csrrw x1, 1792, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0xa5a5a5a5
	csrrs x1, 1792, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrs x1, 1792, x5
	li x5, 0x00000001
	bne x5, x1, csr_fail
	li x5, 0x1c9d8fe3
	csrrs x1, 1792, x5
	li x5, 0x00000001
	bne x5, x1, csr_fail
	li x5, 0xa5a5a5a5
	csrrc x1, 1792, x5
	li x5, 0x00000001
	bne x5, x1, csr_fail
	li x5, 0x5a5a5a5a
	csrrc x1, 1792, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	li x5, 0x546d5dd3
	csrrc x1, 1792, x5
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 1792, 0b00101
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrwi x1, 1792, 0b11010
	li x5, 0x00000001
	bne x5, x1, csr_fail
	csrrwi x1, 1792, 0b10001
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrsi x1, 1792, 0b00101
	li x5, 0x00000001
	bne x5, x1, csr_fail
	csrrsi x1, 1792, 0b11010
	li x5, 0x00000001
	bne x5, x1, csr_fail
	csrrsi x1, 1792, 0b11101
	li x5, 0x00000001
	bne x5, x1, csr_fail
	csrrci x1, 1792, 0b00101
	li x5, 0x00000001
	bne x5, x1, csr_fail
	csrrci x1, 1792, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrrci x1, 1792, 0b11010
	li x5, 0x00000000
	bne x5, x1, csr_fail
	csrr x1, 1792
	li x5, 0x00000000
	bne x5, x1, csr_fail
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
