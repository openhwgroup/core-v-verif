.macro init
.endm
.section .text.init
.globl _start
.option norvc
_start:
	# mcycle
	# 	CSR marked volatile, skipping it.
	# mcycleh
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb80, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb80, x3
	li x3, 0xa5a5a5a5
	bne x3, x11, csr_fail
	li x3, 0xcc1390ec
	csrrw x11, 0xb80, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb80, x3
	li x3, 0xcc1390ec
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb80, x3
	li x3, 0xedb7b5ed
	bne x3, x11, csr_fail
	li x3, 0xde8f2e87
	csrrs x11, 0xb80, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb80, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb80, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xd7e57bff
	csrrc x11, 0xb80, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb80, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb80, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb80, 0b01110
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb80, 0b00101
	li x3, 0x0000000e
	bne x3, x11, csr_fail
	csrrsi x11, 0xb80, 0b11010
	li x3, 0x0000000f
	bne x3, x11, csr_fail
	csrrsi x11, 0xb80, 0b00111
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb80, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb80, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb80, 0b10001
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# minstret
	# 	CSR marked volatile, skipping it.
	# minstreth
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb82, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb82, x3
	li x3, 0xa5a5a5a5
	bne x3, x11, csr_fail
	li x3, 0x9af8ac8b
	csrrw x11, 0xb82, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb82, x3
	li x3, 0x9af8ac8b
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb82, x3
	li x3, 0xbffdadaf
	bne x3, x11, csr_fail
	li x3, 0x2bdac53d
	csrrs x11, 0xb82, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb82, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb82, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0x48d3446c
	csrrc x11, 0xb82, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb82, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb82, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb82, 0b10010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb82, 0b00101
	li x3, 0x00000012
	bne x3, x11, csr_fail
	csrrsi x11, 0xb82, 0b11010
	li x3, 0x00000017
	bne x3, x11, csr_fail
	csrrsi x11, 0xb82, 0b01011
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb82, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb82, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb82, 0b10011
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter3
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb03, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb03, x3
	li x3, 0xa5a5a5a5
	bne x3, x11, csr_fail
	li x3, 0x0e1cf6cf
	csrrw x11, 0xb03, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb03, x3
	li x3, 0x0e1cf6cf
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb03, x3
	li x3, 0xafbdf7ef
	bne x3, x11, csr_fail
	li x3, 0x822ddab4
	csrrs x11, 0xb03, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb03, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb03, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0x8ebd90c2
	csrrc x11, 0xb03, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb03, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb03, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb03, 0b10110
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb03, 0b00101
	li x3, 0x00000016
	bne x3, x11, csr_fail
	csrrsi x11, 0xb03, 0b11010
	li x3, 0x00000017
	bne x3, x11, csr_fail
	csrrsi x11, 0xb03, 0b00000
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb03, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb03, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb03, 0b11000
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter4
	# 	CSR marked SKIP_ME: Seeing a value in this counter at first read.
	# mhpmcounter5
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter6
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb06, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb06, x3
	li x3, 0xa5a5a5a5
	bne x3, x11, csr_fail
	li x3, 0xfdb4f2d7
	csrrw x11, 0xb06, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb06, x3
	li x3, 0xfdb4f2d7
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb06, x3
	li x3, 0xfdb5f7f7
	bne x3, x11, csr_fail
	li x3, 0xeb944ac3
	csrrs x11, 0xb06, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb06, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb06, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xdfc05310
	csrrc x11, 0xb06, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb06, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb06, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb06, 0b10111
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb06, 0b00101
	li x3, 0x00000017
	bne x3, x11, csr_fail
	csrrsi x11, 0xb06, 0b11010
	li x3, 0x00000017
	bne x3, x11, csr_fail
	csrrsi x11, 0xb06, 0b10111
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb06, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb06, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb06, 0b00110
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter7
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb07, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb07, x3
	li x3, 0xa5a5a5a5
	bne x3, x11, csr_fail
	li x3, 0x1afc6a02
	csrrw x11, 0xb07, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb07, x3
	li x3, 0x1afc6a02
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb07, x3
	li x3, 0xbffdefa7
	bne x3, x11, csr_fail
	li x3, 0x1a83dc4f
	csrrs x11, 0xb07, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb07, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb07, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xc66be830
	csrrc x11, 0xb07, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb07, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb07, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb07, 0b11001
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb07, 0b00101
	li x3, 0x00000019
	bne x3, x11, csr_fail
	csrrsi x11, 0xb07, 0b11010
	li x3, 0x0000001d
	bne x3, x11, csr_fail
	csrrsi x11, 0xb07, 0b11111
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb07, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb07, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb07, 0b11001
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter8
	# 	CSR marked SKIP_ME: Seeing a value in this counter at first read.
	# mhpmcounter9
	# 	CSR marked SKIP_ME: Seeing a value in this counter at first read.
	# mhpmcounter10
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb0a, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb0a, x3
	li x3, 0xa5a5a5a5
	bne x3, x11, csr_fail
	li x3, 0xe5b63f04
	csrrw x11, 0xb0a, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb0a, x3
	li x3, 0xe5b63f04
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb0a, x3
	li x3, 0xe5b7bfa5
	bne x3, x11, csr_fail
	li x3, 0x19d7177d
	csrrs x11, 0xb0a, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb0a, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb0a, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xc23d7c9f
	csrrc x11, 0xb0a, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb0a, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb0a, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb0a, 0b10100
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb0a, 0b00101
	li x3, 0x00000014
	bne x3, x11, csr_fail
	csrrsi x11, 0xb0a, 0b11010
	li x3, 0x00000015
	bne x3, x11, csr_fail
	csrrsi x11, 0xb0a, 0b00011
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb0a, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb0a, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb0a, 0b00110
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter11
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb0b, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb0b, x3
	li x3, 0xa5a5a5a5
	bne x3, x11, csr_fail
	li x3, 0xa7e18c8c
	csrrw x11, 0xb0b, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb0b, x3
	li x3, 0xa7e18c8c
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb0b, x3
	li x3, 0xa7e5adad
	bne x3, x11, csr_fail
	li x3, 0xb0008773
	csrrs x11, 0xb0b, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb0b, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb0b, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xe835e458
	csrrc x11, 0xb0b, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb0b, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb0b, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb0b, 0b10010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb0b, 0b00101
	li x3, 0x00000012
	bne x3, x11, csr_fail
	csrrsi x11, 0xb0b, 0b11010
	li x3, 0x00000017
	bne x3, x11, csr_fail
	csrrsi x11, 0xb0b, 0b01101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb0b, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb0b, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb0b, 0b11011
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter12
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb0c, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb0c, x3
	li x3, 0xa5a5a5a5
	bne x3, x11, csr_fail
	li x3, 0x3e1f37d5
	csrrw x11, 0xb0c, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb0c, x3
	li x3, 0x3e1f37d5
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb0c, x3
	li x3, 0xbfbfb7f5
	bne x3, x11, csr_fail
	li x3, 0x3a51e7e7
	csrrs x11, 0xb0c, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb0c, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb0c, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0x42ca270b
	csrrc x11, 0xb0c, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb0c, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb0c, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb0c, 0b00011
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb0c, 0b00101
	li x3, 0x00000003
	bne x3, x11, csr_fail
	csrrsi x11, 0xb0c, 0b11010
	li x3, 0x00000007
	bne x3, x11, csr_fail
	csrrsi x11, 0xb0c, 0b11001
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb0c, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb0c, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb0c, 0b01111
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter3h
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb83, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb83, x3
	li x3, 0x000000a5
	bne x3, x11, csr_fail
	li x3, 0x32c63f4f
	csrrw x11, 0xb83, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb83, x3
	li x3, 0x0000004f
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb83, x3
	li x3, 0x000000ef
	bne x3, x11, csr_fail
	li x3, 0xf0f08dbb
	csrrs x11, 0xb83, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb83, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb83, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0x90730850
	csrrc x11, 0xb83, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb83, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb83, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb83, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb83, 0b00101
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb83, 0b11010
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrsi x11, 0xb83, 0b10010
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb83, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb83, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb83, 0b01001
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter4h
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb84, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb84, x3
	li x3, 0x000000a5
	bne x3, x11, csr_fail
	li x3, 0xa1c60117
	csrrw x11, 0xb84, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb84, x3
	li x3, 0x00000017
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb84, x3
	li x3, 0x000000b7
	bne x3, x11, csr_fail
	li x3, 0x2817a0dc
	csrrs x11, 0xb84, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb84, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb84, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0x7f957645
	csrrc x11, 0xb84, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb84, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb84, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb84, 0b11001
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb84, 0b00101
	li x3, 0x00000019
	bne x3, x11, csr_fail
	csrrsi x11, 0xb84, 0b11010
	li x3, 0x0000001d
	bne x3, x11, csr_fail
	csrrsi x11, 0xb84, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb84, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb84, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb84, 0b00110
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter5h
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb85, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb85, x3
	li x3, 0x000000a5
	bne x3, x11, csr_fail
	li x3, 0x228ede1f
	csrrw x11, 0xb85, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb85, x3
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb85, x3
	li x3, 0x000000bf
	bne x3, x11, csr_fail
	li x3, 0xd74ff897
	csrrs x11, 0xb85, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb85, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb85, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0x18c1e0b0
	csrrc x11, 0xb85, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb85, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb85, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb85, 0b00000
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb85, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0xb85, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrsi x11, 0xb85, 0b00100
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb85, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb85, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb85, 0b10110
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter6h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter7h
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb87, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb87, x3
	li x3, 0x000000a5
	bne x3, x11, csr_fail
	li x3, 0x93816224
	csrrw x11, 0xb87, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb87, x3
	li x3, 0x00000024
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb87, x3
	li x3, 0x000000a5
	bne x3, x11, csr_fail
	li x3, 0xe1c22642
	csrrs x11, 0xb87, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb87, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb87, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0x53e711e8
	csrrc x11, 0xb87, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb87, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb87, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb87, 0b01100
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb87, 0b00101
	li x3, 0x0000000c
	bne x3, x11, csr_fail
	csrrsi x11, 0xb87, 0b11010
	li x3, 0x0000000d
	bne x3, x11, csr_fail
	csrrsi x11, 0xb87, 0b01111
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb87, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb87, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb87, 0b10001
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter8h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter9h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter10h
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb8a, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb8a, x3
	li x3, 0x000000a5
	bne x3, x11, csr_fail
	li x3, 0x260a61d7
	csrrw x11, 0xb8a, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb8a, x3
	li x3, 0x000000d7
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb8a, x3
	li x3, 0x000000f7
	bne x3, x11, csr_fail
	li x3, 0x79d48d16
	csrrs x11, 0xb8a, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb8a, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb8a, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0x03fe3152
	csrrc x11, 0xb8a, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb8a, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb8a, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb8a, 0b11001
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb8a, 0b00101
	li x3, 0x00000019
	bne x3, x11, csr_fail
	csrrsi x11, 0xb8a, 0b11010
	li x3, 0x0000001d
	bne x3, x11, csr_fail
	csrrsi x11, 0xb8a, 0b00111
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb8a, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb8a, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb8a, 0b11110
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter11h
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb8b, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb8b, x3
	li x3, 0x000000a5
	bne x3, x11, csr_fail
	li x3, 0x2614f1c5
	csrrw x11, 0xb8b, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb8b, x3
	li x3, 0x000000c5
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb8b, x3
	li x3, 0x000000e5
	bne x3, x11, csr_fail
	li x3, 0xe8e41ebc
	csrrs x11, 0xb8b, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb8b, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb8b, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0xbde7ab61
	csrrc x11, 0xb8b, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb8b, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb8b, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb8b, 0b10001
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb8b, 0b00101
	li x3, 0x00000011
	bne x3, x11, csr_fail
	csrrsi x11, 0xb8b, 0b11010
	li x3, 0x00000015
	bne x3, x11, csr_fail
	csrrsi x11, 0xb8b, 0b01101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb8b, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb8b, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb8b, 0b11110
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mhpmcounter12h
	li x3, 0xa5a5a5a5
	csrrw x11, 0xb8c, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0xb8c, x3
	li x3, 0x000000a5
	bne x3, x11, csr_fail
	li x3, 0xa83370bd
	csrrw x11, 0xb8c, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0xb8c, x3
	li x3, 0x000000bd
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0xb8c, x3
	li x3, 0x000000bd
	bne x3, x11, csr_fail
	li x3, 0x1508c3e9
	csrrs x11, 0xb8c, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0xb8c, x3
	li x3, 0x000000ff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0xb8c, x3
	li x3, 0x0000005a
	bne x3, x11, csr_fail
	li x3, 0x232476ee
	csrrc x11, 0xb8c, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb8c, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0xb8c, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0xb8c, 0b01010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb8c, 0b00101
	li x3, 0x0000000a
	bne x3, x11, csr_fail
	csrrsi x11, 0xb8c, 0b11010
	li x3, 0x0000000f
	bne x3, x11, csr_fail
	csrrsi x11, 0xb8c, 0b01001
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb8c, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0xb8c, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0xb8c, 0b01000
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mstatus
	# 	CSR marked SKIP_ME: Imperas model does not have U bit set to 1
	# misa
	li x3, 0xa5a5a5a5
	csrrw x11, 0x301, x3
	li x3, 0x40101104
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0x301, x3
	li x3, 0x40101104
	bne x3, x11, csr_fail
	li x3, 0x7a293c76
	csrrw x11, 0x301, x3
	li x3, 0x40101104
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0x301, x3
	li x3, 0x40101104
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0x301, x3
	li x3, 0x40101104
	bne x3, x11, csr_fail
	li x3, 0xdbd5175e
	csrrs x11, 0x301, x3
	li x3, 0x40101104
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0x301, x3
	li x3, 0x40101104
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0x301, x3
	li x3, 0x40101104
	bne x3, x11, csr_fail
	li x3, 0x326b72dd
	csrrc x11, 0x301, x3
	li x3, 0x40101104
	bne x3, x11, csr_fail
	csrrwi x11, 0x301, 0b00101
	li x3, 0x40101104
	bne x3, x11, csr_fail
	csrrwi x11, 0x301, 0b11010
	li x3, 0x40101104
	bne x3, x11, csr_fail
	csrrwi x11, 0x301, 0b01000
	li x3, 0x40101104
	bne x3, x11, csr_fail
	csrrsi x11, 0x301, 0b00101
	li x3, 0x40101104
	bne x3, x11, csr_fail
	csrrsi x11, 0x301, 0b11010
	li x3, 0x40101104
	bne x3, x11, csr_fail
	csrrsi x11, 0x301, 0b00111
	li x3, 0x40101104
	bne x3, x11, csr_fail
	csrrci x11, 0x301, 0b00101
	li x3, 0x40101104
	bne x3, x11, csr_fail
	csrrci x11, 0x301, 0b11010
	li x3, 0x40101104
	bne x3, x11, csr_fail
	csrrci x11, 0x301, 0b00111
	li x3, 0x40101104
	bne x3, x11, csr_fail
	# mie
	# 	CSR marked SKIP_ME: Imperas checker has bit 31 writeable
	# mtvec
	li x3, 0xa5a5a5a5
	csrrw x11, 0x305, x3
	li x3, 0x00000001
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0x305, x3
	li x3, 0xa5a5a501
	bne x3, x11, csr_fail
	li x3, 0x930724c2
	csrrw x11, 0x305, x3
	li x3, 0x5a5a5a01
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0x305, x3
	li x3, 0x93072401
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0x305, x3
	li x3, 0xb7a7a501
	bne x3, x11, csr_fail
	li x3, 0xf90aa8ef
	csrrs x11, 0x305, x3
	li x3, 0xffffff01
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0x305, x3
	li x3, 0xffffff01
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0x305, x3
	li x3, 0x5a5a5a01
	bne x3, x11, csr_fail
	li x3, 0x90aedecc
	csrrc x11, 0x305, x3
	li x3, 0x00000001
	bne x3, x11, csr_fail
	csrrwi x11, 0x305, 0b00101
	li x3, 0x00000001
	bne x3, x11, csr_fail
	csrrwi x11, 0x305, 0b11010
	li x3, 0x00000001
	bne x3, x11, csr_fail
	csrrwi x11, 0x305, 0b00011
	li x3, 0x00000001
	bne x3, x11, csr_fail
	csrrsi x11, 0x305, 0b00101
	li x3, 0x00000001
	bne x3, x11, csr_fail
	csrrsi x11, 0x305, 0b11010
	li x3, 0x00000001
	bne x3, x11, csr_fail
	csrrsi x11, 0x305, 0b11111
	li x3, 0x00000001
	bne x3, x11, csr_fail
	csrrci x11, 0x305, 0b00101
	li x3, 0x00000001
	bne x3, x11, csr_fail
	csrrci x11, 0x305, 0b11010
	li x3, 0x00000001
	bne x3, x11, csr_fail
	csrrci x11, 0x305, 0b00011
	li x3, 0x00000001
	bne x3, x11, csr_fail
	# mcountinhibit
	# 	CSR marked SKIP_ME: Imperas checker has this reading as 0's DUT has non zero values.
	# mhpmevent3
	# 	CSR marked SKIP_ME: Appears to be unimplemented in RTL.
	# mhpmevent4
	# 	CSR marked SKIP_ME: Appears to be unimplemented in RTL.
	# mhpmevent5
	# 	CSR marked SKIP_ME: Appears to be unimplemented in RTL.
	# mhpmevent6
	# 	CSR marked SKIP_ME: Appears to be unimplemented in RTL.
	# mhpmevent7
	# 	CSR marked SKIP_ME: Appears to be unimplemented in RTL.
	# mhpmevent8
	# 	CSR marked SKIP_ME: Appears to be unimplemented in RTL.
	# mhpmevent9
	# 	CSR marked SKIP_ME: Appears to be unimplemented in RTL.
	# mhpmevent10
	# 	CSR marked SKIP_ME: Appears to be unimplemented in RTL.
	# mhpmevent11
	# 	CSR marked SKIP_ME: Appears to be unimplemented in RTL.
	# mhpmevent12
	# 	CSR marked SKIP_ME: Appears to be unimplemented in RTL.
	# mscratch
	li x3, 0xa5a5a5a5
	csrrw x11, 0x340, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0x340, x3
	li x3, 0xa5a5a5a5
	bne x3, x11, csr_fail
	li x3, 0xcbdd587b
	csrrw x11, 0x340, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0x340, x3
	li x3, 0xcbdd587b
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0x340, x3
	li x3, 0xeffdfdff
	bne x3, x11, csr_fail
	li x3, 0x25dac351
	csrrs x11, 0x340, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0x340, x3
	li x3, 0xffffffff
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0x340, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0x5fdd9e06
	csrrc x11, 0x340, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x340, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x340, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0x340, 0b11110
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0x340, 0b00101
	li x3, 0x0000001e
	bne x3, x11, csr_fail
	csrrsi x11, 0x340, 0b11010
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrsi x11, 0x340, 0b11100
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0x340, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0x340, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0x340, 0b10011
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mepc
	li x3, 0xa5a5a5a5
	csrrw x11, 0x341, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0x341, x3
	li x3, 0xa5a5a5a4
	bne x3, x11, csr_fail
	li x3, 0xe87d0819
	csrrw x11, 0x341, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0x341, x3
	li x3, 0xe87d0818
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0x341, x3
	li x3, 0xedfdadbc
	bne x3, x11, csr_fail
	li x3, 0x36c05dac
	csrrs x11, 0x341, x3
	li x3, 0xfffffffe
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0x341, x3
	li x3, 0xfffffffe
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0x341, x3
	li x3, 0x5a5a5a5a
	bne x3, x11, csr_fail
	li x3, 0x0c7e53a9
	csrrc x11, 0x341, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x341, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x341, 0b11010
	li x3, 0x00000004
	bne x3, x11, csr_fail
	csrrwi x11, 0x341, 0b00111
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0x341, 0b00101
	li x3, 0x00000006
	bne x3, x11, csr_fail
	csrrsi x11, 0x341, 0b11010
	li x3, 0x00000006
	bne x3, x11, csr_fail
	csrrsi x11, 0x341, 0b00110
	li x3, 0x0000001e
	bne x3, x11, csr_fail
	csrrci x11, 0x341, 0b00101
	li x3, 0x0000001e
	bne x3, x11, csr_fail
	csrrci x11, 0x341, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0x341, 0b01111
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mcause
	li x3, 0xa5a5a5a5
	csrrw x11, 0x342, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0x342, x3
	li x3, 0x80000005
	bne x3, x11, csr_fail
	li x3, 0x73d36f19
	csrrw x11, 0x342, x3
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0x342, x3
	li x3, 0x00000019
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0x342, x3
	li x3, 0x8000001d
	bne x3, x11, csr_fail
	li x3, 0x64e505e4
	csrrs x11, 0x342, x3
	li x3, 0x8000001f
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0x342, x3
	li x3, 0x8000001f
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0x342, x3
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	li x3, 0x3a34df7b
	csrrc x11, 0x342, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x342, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x342, 0b11010
	li x3, 0x00000005
	bne x3, x11, csr_fail
	csrrwi x11, 0x342, 0b11000
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrsi x11, 0x342, 0b00101
	li x3, 0x00000018
	bne x3, x11, csr_fail
	csrrsi x11, 0x342, 0b11010
	li x3, 0x0000001d
	bne x3, x11, csr_fail
	csrrsi x11, 0x342, 0b11011
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0x342, 0b00101
	li x3, 0x0000001f
	bne x3, x11, csr_fail
	csrrci x11, 0x342, 0b11010
	li x3, 0x0000001a
	bne x3, x11, csr_fail
	csrrci x11, 0x342, 0b10000
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mtval
	# 	CSR marked SKIP_ME: Imperas does not have this CSR writeable
	# mip
	li x3, 0xa5a5a5a5
	csrrw x11, 0x344, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0x344, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x92534a43
	csrrw x11, 0x344, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0x344, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0x344, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xb0888e37
	csrrs x11, 0x344, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0x344, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0x344, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x15d52440
	csrrc x11, 0x344, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x344, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x344, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x344, 0b10110
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x344, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x344, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x344, 0b10010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x344, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x344, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x344, 0b11101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# tselect
	li x3, 0xa5a5a5a5
	csrrw x11, 0x7a0, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0x7a0, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xf40f0637
	csrrw x11, 0x7a0, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0x7a0, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0x7a0, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x74fc8410
	csrrs x11, 0x7a0, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0x7a0, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0x7a0, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x27ef9c4a
	csrrc x11, 0x7a0, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7a0, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7a0, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7a0, 0b01110
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7a0, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7a0, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7a0, 0b10101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7a0, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7a0, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7a0, 0b10001
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# tdata1
	# 	CSR marked SKIP_ME: DUT hardcodes U-mode to 1, Imperas has it as  0
	# tdata2
	li x3, 0xa5a5a5a5
	csrrw x11, 0x7a2, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0x7a2, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xf7703838
	csrrw x11, 0x7a2, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0x7a2, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0x7a2, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa18140f9
	csrrs x11, 0x7a2, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0x7a2, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0x7a2, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5e1c5141
	csrrc x11, 0x7a2, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7a2, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7a2, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7a2, 0b01110
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7a2, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7a2, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7a2, 0b11110
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7a2, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7a2, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7a2, 0b11000
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# tdata3
	li x3, 0xa5a5a5a5
	csrrw x11, 0x7a3, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0x7a3, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xebc4bda3
	csrrw x11, 0x7a3, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0x7a3, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0x7a3, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x8b9d479f
	csrrs x11, 0x7a3, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0x7a3, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0x7a3, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xfb206a26
	csrrc x11, 0x7a3, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7a3, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7a3, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7a3, 0b00000
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7a3, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7a3, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7a3, 0b00000
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7a3, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7a3, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7a3, 0b11001
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# mcontext
	li x3, 0xa5a5a5a5
	csrrw x11, 0x7a8, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0x7a8, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x606fe53a
	csrrw x11, 0x7a8, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0x7a8, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0x7a8, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x65830690
	csrrs x11, 0x7a8, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0x7a8, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0x7a8, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x38d658da
	csrrc x11, 0x7a8, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7a8, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7a8, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7a8, 0b01110
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7a8, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7a8, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7a8, 0b10000
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7a8, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7a8, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7a8, 0b11100
	li x3, 0x00000000
	bne x3, x11, csr_fail
	# scontext
	li x3, 0xa5a5a5a5
	csrrw x11, 0x7aa, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrw x11, 0x7aa, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xb09f2482
	csrrw x11, 0x7aa, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrs x11, 0x7aa, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrs x11, 0x7aa, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x799cc230
	csrrs x11, 0x7aa, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xa5a5a5a5
	csrrc x11, 0x7aa, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0x5a5a5a5a
	csrrc x11, 0x7aa, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	li x3, 0xe0b99d8d
	csrrc x11, 0x7aa, x3
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7aa, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7aa, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrwi x11, 0x7aa, 0b00011
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7aa, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7aa, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrsi x11, 0x7aa, 0b01000
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7aa, 0b00101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7aa, 0b11010
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrrci x11, 0x7aa, 0b01101
	li x3, 0x00000000
	bne x3, x11, csr_fail
	csrr x11, 1962
	li x3, 0x00000000
	bne x3, x11, csr_fail
csr_pass:
	li x1, 123456789
	li x2, 0x20000000
	sw x1, 0(x2)
	j csr_pass
csr_fail:
	li x1, 1
	li x2, 0x20000000
	sw x1, 0(x2)
	sw x3, 4(x2)
	sw x11, 8(x2)
	j csr_fail
