#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
	# CSR_MEPC
	li x9, 0xa5a5a5a5
	csrrw x2, 833, x9
	li x9, 0x00000000
	bne x9, x2, csr_fail
	li x9, 0x5a5a5a5a
	csrrw x2, 833, x9
	li x9, 0xa5a5a5a4
	bne x9, x2, csr_fail
	li x9, 0xc782f024
	csrrw x2, 833, x9
	li x9, 0x5a5a5a5a
	bne x9, x2, csr_fail
	li x9, 0xa5a5a5a5
	csrrs x2, 833, x9
	li x9, 0xc782f024
	bne x9, x2, csr_fail
	li x9, 0x5a5a5a5a
	csrrs x2, 833, x9
	li x9, 0xe7a7f5a4
	bne x9, x2, csr_fail
	li x9, 0x81d6d9bb
	csrrs x2, 833, x9
	li x9, 0xfffffffe
	bne x9, x2, csr_fail
	li x9, 0xa5a5a5a5
	csrrc x2, 833, x9
	li x9, 0xfffffffe
	bne x9, x2, csr_fail
	li x9, 0x5a5a5a5a
	csrrc x2, 833, x9
	li x9, 0x5a5a5a5a
	bne x9, x2, csr_fail
	li x9, 0x52216f2e
	csrrc x2, 833, x9
	li x9, 0x00000000
	bne x9, x2, csr_fail
	csrrwi x2, 833, 0b00101
	li x9, 0x00000000
	bne x9, x2, csr_fail
	csrrwi x2, 833, 0b11010
	li x9, 0x00000004
	bne x9, x2, csr_fail
	csrrwi x2, 833, 0b11100
	li x9, 0x0000001a
	bne x9, x2, csr_fail
	csrrsi x2, 833, 0b00101
	li x9, 0x0000001c
	bne x9, x2, csr_fail
	csrrsi x2, 833, 0b11010
	li x9, 0x0000001c
	bne x9, x2, csr_fail
	csrrsi x2, 833, 0b11110
	li x9, 0x0000001e
	bne x9, x2, csr_fail
	csrrci x2, 833, 0b00101
	li x9, 0x0000001e
	bne x9, x2, csr_fail
	csrrci x2, 833, 0b11010
	li x9, 0x0000001a
	bne x9, x2, csr_fail
	csrrci x2, 833, 0b00111
	li x9, 0x00000000
	bne x9, x2, csr_fail
	csrr x2, 833
	li x9, 0x00000000
	bne x9, x2, csr_fail
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
