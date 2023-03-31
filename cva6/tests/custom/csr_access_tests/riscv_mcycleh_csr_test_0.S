#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:

RVMODEL_BOOT
	# CSR_MCYCLE_H
	li x8, 0xa5a5a5a5
	csrrw x5, 2944, x8
	li x8, 0x00000000
	bne x8, x5, csr_fail
	li x8, 0x5a5a5a5a
	csrrw x5, 2944, x8
	li x8, 0xa5a5a5a5
	bne x8, x5, csr_fail
	li x8, 0xde2c74d5
	csrrw x5, 2944, x8
	li x8, 0x5a5a5a5a
	bne x8, x5, csr_fail
	li x8, 0xa5a5a5a5
	csrrs x5, 2944, x8
	li x8, 0xde2c74d5
	bne x8, x5, csr_fail
	li x8, 0x5a5a5a5a
	csrrs x5, 2944, x8
	li x8, 0xffadf5f5
	bne x8, x5, csr_fail
	li x8, 0x6ba6b505
	csrrs x5, 2944, x8
	li x8, 0xffffffff
	bne x8, x5, csr_fail
	li x8, 0xa5a5a5a5
	csrrc x5, 2944, x8
	li x8, 0xffffffff
	bne x8, x5, csr_fail
	li x8, 0x5a5a5a5a
	csrrc x5, 2944, x8
	li x8, 0x5a5a5a5a
	bne x8, x5, csr_fail
	li x8, 0x816ed005
	csrrc x5, 2944, x8
	li x8, 0x00000000
	bne x8, x5, csr_fail
	csrrwi x5, 2944, 0b00101
	li x8, 0x00000000
	bne x8, x5, csr_fail
	csrrwi x5, 2944, 0b11010
	li x8, 0x00000005
	bne x8, x5, csr_fail
	csrrwi x5, 2944, 0b01111
	li x8, 0x0000001a
	bne x8, x5, csr_fail
	csrrsi x5, 2944, 0b00101
	li x8, 0x0000000f
	bne x8, x5, csr_fail
	csrrsi x5, 2944, 0b11010
	li x8, 0x0000000f
	bne x8, x5, csr_fail
	csrrsi x5, 2944, 0b01111
	li x8, 0x0000001f
	bne x8, x5, csr_fail
	csrrci x5, 2944, 0b00101
	li x8, 0x0000001f
	bne x8, x5, csr_fail
	csrrci x5, 2944, 0b11010
	li x8, 0x0000001a
	bne x8, x5, csr_fail
	csrrci x5, 2944, 0b01001
	li x8, 0x00000000
	bne x8, x5, csr_fail
	csrr x5, 2944
	li x8, 0x00000000
	bne x8, x5, csr_fail
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
