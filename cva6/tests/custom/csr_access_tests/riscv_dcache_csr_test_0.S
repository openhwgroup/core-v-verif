#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
	# CSR_DCACHE
	li x2, 0xa5a5a5a5
	csrrw x14, 1793, x2
	li x2, 0x00000001
	bne x2, x14, csr_fail
	li x2, 0x5a5a5a5a
	csrrw x14, 1793, x2
	li x2, 0x00000001
	bne x2, x14, csr_fail
	li x2, 0xebf389ea
	csrrw x14, 1793, x2
	li x2, 0x00000000
	bne x2, x14, csr_fail
	li x2, 0xa5a5a5a5
	csrrs x14, 1793, x2
	li x2, 0x00000000
	bne x2, x14, csr_fail
	li x2, 0x5a5a5a5a
	csrrs x14, 1793, x2
	li x2, 0x00000001
	bne x2, x14, csr_fail
	li x2, 0x9c90798f
	csrrs x14, 1793, x2
	li x2, 0x00000001
	bne x2, x14, csr_fail
	li x2, 0xa5a5a5a5
	csrrc x14, 1793, x2
	li x2, 0x00000001
	bne x2, x14, csr_fail
	li x2, 0x5a5a5a5a
	csrrc x14, 1793, x2
	li x2, 0x00000000
	bne x2, x14, csr_fail
	li x2, 0x865ca818
	csrrc x14, 1793, x2
	li x2, 0x00000000
	bne x2, x14, csr_fail
	csrrwi x14, 1793, 0b00101
	li x2, 0x00000000
	bne x2, x14, csr_fail
	csrrwi x14, 1793, 0b11010
	li x2, 0x00000001
	bne x2, x14, csr_fail
	csrrwi x14, 1793, 0b11000
	li x2, 0x00000000
	bne x2, x14, csr_fail
	csrrsi x14, 1793, 0b00101
	li x2, 0x00000000
	bne x2, x14, csr_fail
	csrrsi x14, 1793, 0b11010
	li x2, 0x00000001
	bne x2, x14, csr_fail
	csrrsi x14, 1793, 0b00001
	li x2, 0x00000001
	bne x2, x14, csr_fail
	csrrci x14, 1793, 0b00101
	li x2, 0x00000001
	bne x2, x14, csr_fail
	csrrci x14, 1793, 0b11010
	li x2, 0x00000000
	bne x2, x14, csr_fail
	csrrci x14, 1793, 0b00000
	li x2, 0x00000000
	bne x2, x14, csr_fail
	csrr x14, 1793
	li x2, 0x00000000
	bne x2, x14, csr_fail
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
