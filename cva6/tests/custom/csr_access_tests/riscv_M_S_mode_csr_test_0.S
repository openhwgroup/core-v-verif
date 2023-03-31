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

        ##supervisor_mode CSR tests
	
	# CSR_SCAUSE
	li x4, 0xa5a5a5a5
	csrrw x7, 322, x4
	li x4, 0x00000000
	bne x4, x7, csr_fail
	li x4, 0x5a5a5a5a
	csrrw x7, 322, x4
	li x4, 0xa5a5a5a5
	bne x4, x7, csr_fail
	li x4, 0x8b85f3c8
	csrrw x7, 322, x4
	li x4, 0x5a5a5a5a
	bne x4, x7, csr_fail
	li x4, 0xa5a5a5a5
	csrrs x7, 322, x4
	li x4, 0x8b85f3c8
	bne x4, x7, csr_fail
	li x4, 0x5a5a5a5a
	csrrs x7, 322, x4
	li x4, 0xafa5f7ed
	bne x4, x7, csr_fail
	li x4, 0x20fff1ae
	csrrs x7, 322, x4
	li x4, 0xffffffff
	bne x4, x7, csr_fail
	li x4, 0xa5a5a5a5
	csrrc x7, 322, x4
	li x4, 0xffffffff
	bne x4, x7, csr_fail
	li x4, 0x5a5a5a5a
	csrrc x7, 322, x4
	li x4, 0x5a5a5a5a
	bne x4, x7, csr_fail
	li x4, 0x1ee47ee4
	csrrc x7, 322, x4
	li x4, 0x00000000
	bne x4, x7, csr_fail
	csrrwi x7, 322, 0b00101
	li x4, 0x00000000
	bne x4, x7, csr_fail
	csrrwi x7, 322, 0b11010
	li x4, 0x00000005
	bne x4, x7, csr_fail
	csrrwi x7, 322, 0b11111
	li x4, 0x0000001a
	bne x4, x7, csr_fail
	csrrsi x7, 322, 0b00101
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	csrrsi x7, 322, 0b11010
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	csrrsi x7, 322, 0b00111
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	csrrci x7, 322, 0b00101
	li x4, 0x0000001f
	bne x4, x7, csr_fail
	csrrci x7, 322, 0b11010
	li x4, 0x0000001a
	bne x4, x7, csr_fail
	csrrci x7, 322, 0b10110
	li x4, 0x00000000
	bne x4, x7, csr_fail
	csrr x7, 322
	li x4, 0x00000000
	bne x4, x7, csr_fail

	# CSR_SCOUNTEREN
	li x14, 0xa5a5a5a5
	csrrw x2, 262, x14
	li x14, 0x00000000
	bne x14, x2, csr_fail
	li x14, 0x5a5a5a5a
	csrrw x2, 262, x14
	li x14, 0xa5a5a5a5
	bne x14, x2, csr_fail
	li x14, 0x525c02d9
	csrrw x2, 262, x14
	li x14, 0x5a5a5a5a
	bne x14, x2, csr_fail
	li x14, 0xa5a5a5a5
	csrrs x2, 262, x14
	li x14, 0x525c02d9
	bne x14, x2, csr_fail
	li x14, 0x5a5a5a5a
	csrrs x2, 262, x14
	li x14, 0xf7fda7fd
	bne x14, x2, csr_fail
	li x14, 0x552dbbde
	csrrs x2, 262, x14
	li x14, 0xffffffff
	bne x14, x2, csr_fail
	li x14, 0xa5a5a5a5
	csrrc x2, 262, x14
	li x14, 0xffffffff
	bne x14, x2, csr_fail
	li x14, 0x5a5a5a5a
	csrrc x2, 262, x14
	li x14, 0x5a5a5a5a
	bne x14, x2, csr_fail
	li x14, 0x98d9cd08
	csrrc x2, 262, x14
	li x14, 0x00000000
	bne x14, x2, csr_fail
	csrrwi x2, 262, 0b00101
	li x14, 0x00000000
	bne x14, x2, csr_fail
	csrrwi x2, 262, 0b11010
	li x14, 0x00000005
	bne x14, x2, csr_fail
	csrrwi x2, 262, 0b10101
	li x14, 0x0000001a
	bne x14, x2, csr_fail
	csrrsi x2, 262, 0b00101
	li x14, 0x00000015
	bne x14, x2, csr_fail
	csrrsi x2, 262, 0b11010
	li x14, 0x00000015
	bne x14, x2, csr_fail
	csrrsi x2, 262, 0b01101
	li x14, 0x0000001f
	bne x14, x2, csr_fail
	csrrci x2, 262, 0b00101
	li x14, 0x0000001f
	bne x14, x2, csr_fail
	csrrci x2, 262, 0b11010
	li x14, 0x0000001a
	bne x14, x2, csr_fail
	csrrci x2, 262, 0b11011
	li x14, 0x00000000
	bne x14, x2, csr_fail
	csrr x2, 262
	li x14, 0x00000000
	bne x14, x2, csr_fail	

	# CSR_SEPC
	li x12, 0xa5a5a5a5
	csrrw x6, 321, x12
	li x12, 0x00000000
	bne x12, x6, csr_fail
	li x12, 0x5a5a5a5a
	csrrw x6, 321, x12
	li x12, 0xa5a5a5a4
	bne x12, x6, csr_fail
	li x12, 0x7a6c28e1
	csrrw x6, 321, x12
	li x12, 0x5a5a5a5a
	bne x12, x6, csr_fail
	li x12, 0xa5a5a5a5
	csrrs x6, 321, x12
	li x12, 0x7a6c28e0
	bne x12, x6, csr_fail
	li x12, 0x5a5a5a5a
	csrrs x6, 321, x12
	li x12, 0xffedade4
	bne x12, x6, csr_fail
	li x12, 0x1228d835
	csrrs x6, 321, x12
	li x12, 0xfffffffe
	bne x12, x6, csr_fail
	li x12, 0xa5a5a5a5
	csrrc x6, 321, x12
	li x12, 0xfffffffe
	bne x12, x6, csr_fail
	li x12, 0x5a5a5a5a
	csrrc x6, 321, x12
	li x12, 0x5a5a5a5a
	bne x12, x6, csr_fail
	li x12, 0x712201a4
	csrrc x6, 321, x12
	li x12, 0x00000000
	bne x12, x6, csr_fail
	csrrwi x6, 321, 0b00101
	li x12, 0x00000000
	bne x12, x6, csr_fail
	csrrwi x6, 321, 0b11010
	li x12, 0x00000004
	bne x12, x6, csr_fail
	csrrwi x6, 321, 0b00010
	li x12, 0x0000001a
	bne x12, x6, csr_fail
	csrrsi x6, 321, 0b00101
	li x12, 0x00000002
	bne x12, x6, csr_fail
	csrrsi x6, 321, 0b11010
	li x12, 0x00000006
	bne x12, x6, csr_fail
	csrrsi x6, 321, 0b01001
	li x12, 0x0000001e
	bne x12, x6, csr_fail
	csrrci x6, 321, 0b00101
	li x12, 0x0000001e
	bne x12, x6, csr_fail
	csrrci x6, 321, 0b11010
	li x12, 0x0000001a
	bne x12, x6, csr_fail
	csrrci x6, 321, 0b11110
	li x12, 0x00000000
	bne x12, x6, csr_fail
	csrr x6, 321
	li x12, 0x00000000
	bne x12, x6, csr_fail

	# CSR_SIP
	li x4, 0xa5a5a5a5
	csrrw x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0x5a5a5a5a
	csrrw x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0x5fab96d2
	csrrw x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0xa5a5a5a5
	csrrs x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0x5a5a5a5a
	csrrs x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0x4e0941cd
	csrrs x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0xa5a5a5a5
	csrrc x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0x5a5a5a5a
	csrrc x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	li x4, 0x3d3e2982
	csrrc x10, 324, x4
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrwi x10, 324, 0b00101
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrwi x10, 324, 0b11010
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrwi x10, 324, 0b00011
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrsi x10, 324, 0b00101
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrsi x10, 324, 0b11010
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrsi x10, 324, 0b10101
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrci x10, 324, 0b00101
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrci x10, 324, 0b11010
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrrci x10, 324, 0b01110
	li x4, 0x00000000
	bne x4, x10, csr_fail
	csrr x10, 324
	li x4, 0x00000000
	bne x4, x10, csr_fail

	# CSR_SSCRATCH
	li x1, 0xa5a5a5a5
	csrrw x3, 320, x1
	li x1, 0x00000000
	bne x1, x3, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x3, 320, x1
	li x1, 0xa5a5a5a5
	bne x1, x3, csr_fail
	li x1, 0xf149b7e8
	csrrw x3, 320, x1
	li x1, 0x5a5a5a5a
	bne x1, x3, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x3, 320, x1
	li x1, 0xf149b7e8
	bne x1, x3, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x3, 320, x1
	li x1, 0xf5edb7ed
	bne x1, x3, csr_fail
	li x1, 0xbcc8c1c2
	csrrs x3, 320, x1
	li x1, 0xffffffff
	bne x1, x3, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x3, 320, x1
	li x1, 0xffffffff
	bne x1, x3, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x3, 320, x1
	li x1, 0x5a5a5a5a
	bne x1, x3, csr_fail
	li x1, 0x18fd947a
	csrrc x3, 320, x1
	li x1, 0x00000000
	bne x1, x3, csr_fail
	csrrwi x3, 320, 0b00101
	li x1, 0x00000000
	bne x1, x3, csr_fail
	csrrwi x3, 320, 0b11010
	li x1, 0x00000005
	bne x1, x3, csr_fail
	csrrwi x3, 320, 0b01010
	li x1, 0x0000001a
	bne x1, x3, csr_fail
	csrrsi x3, 320, 0b00101
	li x1, 0x0000000a
	bne x1, x3, csr_fail
	csrrsi x3, 320, 0b11010
	li x1, 0x0000000f
	bne x1, x3, csr_fail
	csrrsi x3, 320, 0b10100
	li x1, 0x0000001f
	bne x1, x3, csr_fail
	csrrci x3, 320, 0b00101
	li x1, 0x0000001f
	bne x1, x3, csr_fail
	csrrci x3, 320, 0b11010
	li x1, 0x0000001a
	bne x1, x3, csr_fail
	csrrci x3, 320, 0b00001
	li x1, 0x00000000
	bne x1, x3, csr_fail
	csrr x3, 320
	li x1, 0x00000000
	bne x1, x3, csr_fail

	# CSR_STVAL
	li x15, 0xa5a5a5a5
	csrrw x7, 323, x15
	li x15, 0x00000000
	bne x15, x7, csr_fail
	li x15, 0x5a5a5a5a
	csrrw x7, 323, x15
	li x15, 0xa5a5a5a5
	bne x15, x7, csr_fail
	li x15, 0x195a0d46
	csrrw x7, 323, x15
	li x15, 0x5a5a5a5a
	bne x15, x7, csr_fail
	li x15, 0xa5a5a5a5
	csrrs x7, 323, x15
	li x15, 0x195a0d46
	bne x15, x7, csr_fail
	li x15, 0x5a5a5a5a
	csrrs x7, 323, x15
	li x15, 0xbdffade7
	bne x15, x7, csr_fail
	li x15, 0xe82c2396
	csrrs x7, 323, x15
	li x15, 0xffffffff
	bne x15, x7, csr_fail
	li x15, 0xa5a5a5a5
	csrrc x7, 323, x15
	li x15, 0xffffffff
	bne x15, x7, csr_fail
	li x15, 0x5a5a5a5a
	csrrc x7, 323, x15
	li x15, 0x5a5a5a5a
	bne x15, x7, csr_fail
	li x15, 0x3fc5b750
	csrrc x7, 323, x15
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrrwi x7, 323, 0b00101
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrrwi x7, 323, 0b11010
	li x15, 0x00000005
	bne x15, x7, csr_fail
	csrrwi x7, 323, 0b00110
	li x15, 0x0000001a
	bne x15, x7, csr_fail
	csrrsi x7, 323, 0b00101
	li x15, 0x00000006
	bne x15, x7, csr_fail
	csrrsi x7, 323, 0b11010
	li x15, 0x00000007
	bne x15, x7, csr_fail
	csrrsi x7, 323, 0b00110
	li x15, 0x0000001f
	bne x15, x7, csr_fail
	csrrci x7, 323, 0b00101
	li x15, 0x0000001f
	bne x15, x7, csr_fail
	csrrci x7, 323, 0b11010
	li x15, 0x0000001a
	bne x15, x7, csr_fail
	csrrci x7, 323, 0b00010
	li x15, 0x00000000
	bne x15, x7, csr_fail
	csrr x7, 323
	li x15, 0x00000000
	bne x15, x7, csr_fail	

	# CSR_STVEC
	li x7, 0xa5a5a5a5
	csrrw x1, 261, x7
	li x7, 0x00000000
	bne x7, x1, csr_fail
	li x7, 0x5a5a5a5a
	csrrw x1, 261, x7
	li x7, 0xa5a5a5a5
	bne x7, x1, csr_fail
	li x7, 0xd2ec680e
	csrrw x1, 261, x7
	li x7, 0x5a5a5a58
	bne x7, x1, csr_fail
	li x7, 0xa5a5a5a5
	csrrs x1, 261, x7
	li x7, 0xd2ec680c
	bne x7, x1, csr_fail
	li x7, 0x5a5a5a5a
	csrrs x1, 261, x7
	li x7, 0xf7ededad
	bne x7, x1, csr_fail
	li x7, 0x14191a03
	csrrs x1, 261, x7
	li x7, 0xfffffffd
	bne x7, x1, csr_fail
	li x7, 0xa5a5a5a5
	csrrc x1, 261, x7
	li x7, 0xfffffffd
	bne x7, x1, csr_fail
	li x7, 0x5a5a5a5a
	csrrc x1, 261, x7
	li x7, 0x5a5a5a58
	bne x7, x1, csr_fail
	li x7, 0x9f73bde0
	csrrc x1, 261, x7
	li x7, 0x00000000
	bne x7, x1, csr_fail
	csrrwi x1, 261, 0b00101
	li x7, 0x00000000
	bne x7, x1, csr_fail
	csrrwi x1, 261, 0b11010
	li x7, 0x00000005
	bne x7, x1, csr_fail
	csrrwi x1, 261, 0b01011
	li x7, 0x00000018
	bne x7, x1, csr_fail
	csrrsi x1, 261, 0b00101
	li x7, 0x00000009
	bne x7, x1, csr_fail
	csrrsi x1, 261, 0b11010
	li x7, 0x0000000d
	bne x7, x1, csr_fail
	csrrsi x1, 261, 0b00111
	li x7, 0x0000001d
	bne x7, x1, csr_fail
	csrrci x1, 261, 0b00101
	li x7, 0x0000001d
	bne x7, x1, csr_fail
	csrrci x1, 261, 0b11010
	li x7, 0x00000018
	bne x7, x1, csr_fail
	csrrci x1, 261, 0b11010
	li x7, 0x00000000
	bne x7, x1, csr_fail
	csrr x1, 261
	li x7, 0x00000000
	bne x7, x1, csr_fail
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
