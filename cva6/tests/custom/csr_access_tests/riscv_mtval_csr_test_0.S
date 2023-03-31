#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
RVMODEL_BOOT
	# CSR_MTVAL
	li x1, 0xa5a5a5a5
	csrrw x5, 835, x1
	li x1, 0x00000000
	bne x1, x5, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x5, 835, x1
	li x1, 0xa5a5a5a5
	bne x1, x5, csr_fail
	li x1, 0x69c7015b
	csrrw x5, 835, x1
	li x1, 0x5a5a5a5a
	bne x1, x5, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x5, 835, x1
	li x1, 0x69c7015b
	bne x1, x5, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x5, 835, x1
	li x1, 0xede7a5ff
	bne x1, x5, csr_fail
	li x1, 0xbcf5a4ed
	csrrs x5, 835, x1
	li x1, 0xffffffff
	bne x1, x5, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x5, 835, x1
	li x1, 0xffffffff
	bne x1, x5, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x5, 835, x1
	li x1, 0x5a5a5a5a
	bne x1, x5, csr_fail
	li x1, 0x04e00ec7
	csrrc x5, 835, x1
	li x1, 0x00000000
	bne x1, x5, csr_fail
	csrrwi x5, 835, 0b00101
	li x1, 0x00000000
	bne x1, x5, csr_fail
	csrrwi x5, 835, 0b11010
	li x1, 0x00000005
	bne x1, x5, csr_fail
	csrrwi x5, 835, 0b11000
	li x1, 0x0000001a
	bne x1, x5, csr_fail
	csrrsi x5, 835, 0b00101
	li x1, 0x00000018
	bne x1, x5, csr_fail
	csrrsi x5, 835, 0b11010
	li x1, 0x0000001d
	bne x1, x5, csr_fail
	csrrsi x5, 835, 0b10000
	li x1, 0x0000001f
	bne x1, x5, csr_fail
	csrrci x5, 835, 0b00101
	li x1, 0x0000001f
	bne x1, x5, csr_fail
	csrrci x5, 835, 0b11010
	li x1, 0x0000001a
	bne x1, x5, csr_fail
	csrrci x5, 835, 0b00110
	li x1, 0x00000000
	bne x1, x5, csr_fail
	csrr x5, 835
	li x1, 0x00000000
	bne x1, x5, csr_fail
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
