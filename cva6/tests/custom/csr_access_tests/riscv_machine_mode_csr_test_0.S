#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
RVMODEL_BOOT

	# CSR_MCAUSE
	li x3, 0xa5a5a5a5
	csrrw x14, 834, x3
	li x3, 0x00000000
	bne x3, x14, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x14, 834, x3
	li x3, 0xa5a5a5a5
	bne x3, x14, csr_fail
	li x3, 0x77b01936
	csrrw x14, 834, x3
	li x3, 0x5a5a5a5a
	bne x3, x14, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x14, 834, x3
	li x3, 0x77b01936
	bne x3, x14, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x14, 834, x3
	li x3, 0xf7b5bdb7
	bne x3, x14, csr_fail
	li x3, 0xd2e9bfc7
	csrrs x14, 834, x3
	li x3, 0xffffffff
	bne x3, x14, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x14, 834, x3
	li x3, 0xffffffff
	bne x3, x14, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x14, 834, x3
	li x3, 0x5a5a5a5a
	bne x3, x14, csr_fail
	li x3, 0xdf872ab5
	csrrc x14, 834, x3
	li x3, 0x00000000
	bne x3, x14, csr_fail
	csrrwi x14, 834, 0b00101
	li x3, 0x00000000
	bne x3, x14, csr_fail
	csrrwi x14, 834, 0b11010
	li x3, 0x00000005
	bne x3, x14, csr_fail
	csrrwi x14, 834, 0b01101
	li x3, 0x0000001a
	bne x3, x14, csr_fail
	csrrsi x14, 834, 0b00101
	li x3, 0x0000000d
	bne x3, x14, csr_fail
	csrrsi x14, 834, 0b11010
	li x3, 0x0000000d
	bne x3, x14, csr_fail
	csrrsi x14, 834, 0b10100
	li x3, 0x0000001f
	bne x3, x14, csr_fail
	csrrci x14, 834, 0b00101
	li x3, 0x0000001f
	bne x3, x14, csr_fail
	csrrci x14, 834, 0b11010
	li x3, 0x0000001a
	bne x3, x14, csr_fail
	csrrci x14, 834, 0b00110
	li x3, 0x00000000
	bne x3, x14, csr_fail
	csrr x14, 834
	li x3, 0x00000000
	bne x3, x14, csr_fail

	# CSR_MCOUNTEREN
	li x14, 0xa5a5a5a5
	csrrw x3, 774, x14
	li x14, 0x00000000
	bne x14, x3, csr_fail
	li x14, 0x5a5a5a5a
	csrrw x3, 774, x14
	li x14, 0xa5a5a5a5
	bne x14, x3, csr_fail
	li x14, 0xf1811b91
	csrrw x3, 774, x14
	li x14, 0x5a5a5a5a
	bne x14, x3, csr_fail
	li x14, 0xa5a5a5a5
	csrrs x3, 774, x14
	li x14, 0xf1811b91
	bne x14, x3, csr_fail
	li x14, 0x5a5a5a5a
	csrrs x3, 774, x14
	li x14, 0xf5a5bfb5
	bne x14, x3, csr_fail
	li x14, 0x33487fde
	csrrs x3, 774, x14
	li x14, 0xffffffff
	bne x14, x3, csr_fail
	li x14, 0xa5a5a5a5
	csrrc x3, 774, x14
	li x14, 0xffffffff
	bne x14, x3, csr_fail
	li x14, 0x5a5a5a5a
	csrrc x3, 774, x14
	li x14, 0x5a5a5a5a
	bne x14, x3, csr_fail
	li x14, 0xff06b67c
	csrrc x3, 774, x14
	li x14, 0x00000000
	bne x14, x3, csr_fail
	csrrwi x3, 774, 0b00101
	li x14, 0x00000000
	bne x14, x3, csr_fail
	csrrwi x3, 774, 0b11010
	li x14, 0x00000005
	bne x14, x3, csr_fail
	csrrwi x3, 774, 0b00010
	li x14, 0x0000001a
	bne x14, x3, csr_fail
	csrrsi x3, 774, 0b00101
	li x14, 0x00000002
	bne x14, x3, csr_fail
	csrrsi x3, 774, 0b11010
	li x14, 0x00000007
	bne x14, x3, csr_fail
	csrrsi x3, 774, 0b00011
	li x14, 0x0000001f
	bne x14, x3, csr_fail
	csrrci x3, 774, 0b00101
	li x14, 0x0000001f
	bne x14, x3, csr_fail
	csrrci x3, 774, 0b11010
	li x14, 0x0000001a
	bne x14, x3, csr_fail
	csrrci x3, 774, 0b00101
	li x14, 0x00000000
	bne x14, x3, csr_fail
	csrr x3, 774
	li x14, 0x00000000
	bne x14, x3, csr_fail

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

	# CSR_MIE
	li x10, 0xa5a5a5a5
	csrrw x13, 772, x10
	li x10, 0x00000000
	bne x10, x13, csr_fail
	li x10, 0x5a5a5a5a
	csrrw x13, 772, x10
	li x10, 0x000000a0
	bne x10, x13, csr_fail
	li x10, 0xf8851108
	csrrw x13, 772, x10
	li x10, 0x00000a0a
	bne x10, x13, csr_fail
	li x10, 0xa5a5a5a5
	csrrs x13, 772, x10
	li x10, 0x00000008
	bne x10, x13, csr_fail
	li x10, 0x5a5a5a5a
	csrrs x13, 772, x10
	li x10, 0x000000a8
	bne x10, x13, csr_fail
	li x10, 0x11dcf0fa
	csrrs x13, 772, x10
	li x10, 0x00000aaa
	bne x10, x13, csr_fail
	li x10, 0xa5a5a5a5
	csrrc x13, 772, x10
	li x10, 0x00000aaa
	bne x10, x13, csr_fail
	li x10, 0x5a5a5a5a
	csrrc x13, 772, x10
	li x10, 0x00000a0a
	bne x10, x13, csr_fail
	li x10, 0x9216f083
	csrrc x13, 772, x10
	li x10, 0x00000000
	bne x10, x13, csr_fail
	csrrwi x13, 772, 0b00101
	li x10, 0x00000000
	bne x10, x13, csr_fail
	csrrwi x13, 772, 0b11010
	li x10, 0x00000000
	bne x10, x13, csr_fail
	csrrwi x13, 772, 0b10110
	li x10, 0x0000000a
	bne x10, x13, csr_fail
	csrrsi x13, 772, 0b00101
	li x10, 0x00000002
	bne x10, x13, csr_fail
	csrrsi x13, 772, 0b11010
	li x10, 0x00000002
	bne x10, x13, csr_fail
	csrrsi x13, 772, 0b00110
	li x10, 0x0000000a
	bne x10, x13, csr_fail
	csrrci x13, 772, 0b00101
	li x10, 0x0000000a
	bne x10, x13, csr_fail
	csrrci x13, 772, 0b11010
	li x10, 0x0000000a
	bne x10, x13, csr_fail
	csrrci x13, 772, 0b01011
	li x10, 0x00000000
	bne x10, x13, csr_fail
	csrr x13, 772
	li x10, 0x00000000
	bne x10, x13, csr_fail

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

	# CSR_MSCRATCH
	li x10, 0xa5a5a5a5
	csrrw x14, 0x340, x10
	li x10, 0x00000000
	bne x10, x14, csr_fail
	li x10, 0x5a5a5a5a
	csrrw x14, 0x340, x10
	li x10, 0xa5a5a5a5
	bne x10, x14, csr_fail
	li x10, 0x6c218674
	csrrw x14, 0x340, x10
	li x10, 0x5a5a5a5a
	bne x10, x14, csr_fail
	li x10, 0xa5a5a5a5
	csrrs x14, 0x340, x10
	li x10, 0x6c218674
	bne x10, x14, csr_fail
	li x10, 0x5a5a5a5a
	csrrs x14, 0x340, x10
	li x10, 0xeda5a7f5
	bne x10, x14, csr_fail
	li x10, 0xdd2d25a6
	csrrs x14, 0x340, x10
	li x10, 0xffffffff
	bne x10, x14, csr_fail
	li x10, 0xa5a5a5a5
	csrrc x14, 0x340, x10
	li x10, 0xffffffff
	bne x10, x14, csr_fail
	li x10, 0x5a5a5a5a
	csrrc x14, 0x340, x10
	li x10, 0x5a5a5a5a
	bne x10, x14, csr_fail
	li x10, 0x8959179c
	csrrc x14, 0x340, x10
	li x10, 0x00000000
	bne x10, x14, csr_fail
	csrrwi x14, 0x340, 0b00101
	li x10, 0x00000000
	bne x10, x14, csr_fail
	csrrwi x14, 0x340, 0b11010
	li x10, 0x00000005
	bne x10, x14, csr_fail
	csrrwi x14, 0x340, 0b01110
	li x10, 0x0000001a
	bne x10, x14, csr_fail
	csrrsi x14, 0x340, 0b00101
	li x10, 0x0000000e
	bne x10, x14, csr_fail
	csrrsi x14, 0x340, 0b11010
	li x10, 0x0000000f
	bne x10, x14, csr_fail
	csrrsi x14, 0x340, 0b00000
	li x10, 0x0000001f
	bne x10, x14, csr_fail
	csrrci x14, 0x340, 0b00101
	li x10, 0x0000001f
	bne x10, x14, csr_fail
	csrrci x14, 0x340, 0b11010
	li x10, 0x0000001a
	bne x10, x14, csr_fail
	csrrci x14, 0x340, 0b00100
	li x10, 0x00000000
	bne x10, x14, csr_fail
	csrr x14, 0x340
	li x10, 0x00000000
	bne x10, x14, csr_fail

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
