#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
RVMODEL_BOOT
	
	# CSR_MTVEC
	li x13, 0xa5a5a5a5
	csrrw x1, 773, x13
	li x13, 0x00000000
	bne x13, x1, csr_fail
	li x13, 0x5a5a5a5a
	csrrw x1, 773, x13
	li x13, 0xa5a5a5a5
	bne x13, x1, csr_fail
	li x13, 0xbedf1386
	csrrw x1, 773, x13
	li x13, 0x5a5a5a58
	bne x13, x1, csr_fail
	li x13, 0xa5a5a5a5
	csrrs x1, 773, x13
	li x13, 0xbedf1384
	bne x13, x1, csr_fail
	li x13, 0x5a5a5a5a
	csrrs x1, 773, x13
	li x13, 0xbfffb7a5
	bne x13, x1, csr_fail
	li x13, 0x4cce12cc
	csrrs x1, 773, x13
	li x13, 0xfffffffd
	bne x13, x1, csr_fail
	li x13, 0xa5a5a5a5
	csrrc x1, 773, x13
	li x13, 0xfffffffd
	bne x13, x1, csr_fail
	li x13, 0x5a5a5a5a
	csrrc x1, 773, x13
	li x13, 0x5a5a5a58
	bne x13, x1, csr_fail
	li x13, 0xd040012b
	csrrc x1, 773, x13
	li x13, 0x00000000
	bne x13, x1, csr_fail
	csrrwi x1, 773, 0b00101
	li x13, 0x00000000
	bne x13, x1, csr_fail
	csrrwi x1, 773, 0b11010
	li x13, 0x00000005
	bne x13, x1, csr_fail
	csrrwi x1, 773, 0b01000
	li x13, 0x00000018
	bne x13, x1, csr_fail
	csrrsi x1, 773, 0b00101
	li x13, 0x00000008
	bne x13, x1, csr_fail
	csrrsi x1, 773, 0b11010
	li x13, 0x0000000d
	bne x13, x1, csr_fail
	csrrsi x1, 773, 0b10111
	li x13, 0x0000001d
	bne x13, x1, csr_fail
	csrrci x1, 773, 0b00101
	li x13, 0x0000001d
	bne x13, x1, csr_fail
	csrrci x1, 773, 0b11010
	li x13, 0x00000018
	bne x13, x1, csr_fail
	csrrci x1, 773, 0b01100
	li x13, 0x00000000
	bne x13, x1, csr_fail
	csrr x1, 773
	li x13, 0x00000000
	bne x13, x1, csr_fail
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
