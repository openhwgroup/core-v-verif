#include "../../riscv-isa-sim/arch_test_target/spike/model_test.h"
.macro init
.endm
.section .text.init
.globl _start
.option norvc
.org 0x00
_start:
RVMODEL_BOOT

	## set start address range t0 x7
 	la x7, supervisor_code
 	li x28, 0x10000
 	add x7, x7, x28

 	# Enable R,W,X,TOR IN PMPCFG CSR t0 x8
 	li x8, 0x0F

	#set PMPADDR0 CSR with x7
 	csrw 0x3B0, x7

	# set PMPCFG0 CSR with x8
 	csrw 0x3A0, x8

 	# Save the current mode in x28
        csrr x28, 0x300

        # Set the MPP field to supervisor mode (1)
        li x29, 0b1
        slli x29, x29, 11
        or x28, x28, x29

       # Write the modified MSTATUS value back to the CSR
        csrw 0x300, x28
	la x28, supervisor_code
        csrw 0x341, x28
	csrr x31, 0x300

	mret
        
# Supervisor code starts here
supervisor_code:

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

		 		
