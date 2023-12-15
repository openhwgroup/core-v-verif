/* This is an auto-generated file not intended to be hand edited.
 * Changes should be made by editing the yaml file ../../../../env/corev-dv/cv32e20_csr_template.yaml
 * Then invoking gen_csr_test.py to regenerate this file.
 */
.macro init
.endm
.option norvc
.globl interrupt_csr_check
interrupt_csr_check:
	# mtvec
	li a1, 0x305
	li t0, 0x00000001
	csrrw t1, 0x305, t0
	li x12, 0xa5a5a5a5
	csrrw x13, 0x305, x12
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x305, x12
	li x12, 0xa5a5a501
	bne x12, x13, csr_mismatch
	li x12, 0x41190594
	csrrw x13, 0x305, x12
	li x12, 0x5a5a5a01
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x305, x12
	li x12, 0x41190501
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x305, x12
	li x12, 0xe5bda501
	bne x12, x13, csr_mismatch
	li x12, 0x72df50ab
	csrrs x13, 0x305, x12
	li x12, 0xffffff01
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x305, x12
	li x12, 0xffffff01
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x305, x12
	li x12, 0x5a5a5a01
	bne x12, x13, csr_mismatch
	li x12, 0x245d6b40
	csrrc x13, 0x305, x12
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x305, 0b00101
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x305, 0b11010
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x305, 0b00111
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x305, 0b00101
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x305, 0b11010
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x305, 0b11101
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrci x13, 0x305, 0b00101
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrci x13, 0x305, 0b11010
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrci x13, 0x305, 0b11011
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	li x12, 0x00000001
	csrw 0x305, x12
	csrrw t0, 0x305, t1
	# mepc
	li a1, 0x341
	li x12, 0xa5a5a5a5
	csrrw x13, 0x341, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x341, x12
	li x12, 0xa5a5a5a4
	bne x12, x13, csr_mismatch
	li x12, 0xfa62e211
	csrrw x13, 0x341, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x341, x12
	li x12, 0xfa62e210
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x341, x12
	li x12, 0xffe7e7b4
	bne x12, x13, csr_mismatch
	li x12, 0xa7600d9a
	csrrs x13, 0x341, x12
	li x12, 0xfffffffe
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x341, x12
	li x12, 0xfffffffe
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x341, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0x4b4e5174
	csrrc x13, 0x341, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x341, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x341, 0b11010
	li x12, 0x00000004
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x341, 0b11000
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x341, 0b00101
	li x12, 0x00000018
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x341, 0b11010
	li x12, 0x0000001c
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x341, 0b00000
	li x12, 0x0000001e
	bne x12, x13, csr_mismatch
	csrrci x13, 0x341, 0b00101
	li x12, 0x0000001e
	bne x12, x13, csr_mismatch
	csrrci x13, 0x341, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0x341, 0b01110
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x341, x12
	# mstatus
	li a1, 0x300
	li x12, 0xa5a5a5a5
	csrrw x13, 0x300, x12
	li x12, 0x00001800
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x300, x12
	li x12, 0x00200080
	bne x12, x13, csr_mismatch
	li x12, 0xdbc883dd
	csrrw x13, 0x300, x12
	li x12, 0x00021808
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x300, x12
	li x12, 0x00000088
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x300, x12
	li x12, 0x00200088
	bne x12, x13, csr_mismatch
	li x12, 0x0c6c0739
	csrrs x13, 0x300, x12
	li x12, 0x00221888
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x300, x12
	li x12, 0x00221888
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x300, x12
	li x12, 0x00021808
	bne x12, x13, csr_mismatch
	li x12, 0x4ac7a4fc
	csrrc x13, 0x300, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x300, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x300, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x300, 0b01111
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x300, 0b00101
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x300, 0b11010
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x300, 0b00111
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrci x13, 0x300, 0b00101
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrci x13, 0x300, 0b11010
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrci x13, 0x300, 0b01100
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00001800
	csrw 0x300, x12
	# mcause
	li a1, 0x342
	li x12, 0xa5a5a5a5
	csrrw x13, 0x342, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x342, x12
	li x12, 0x80000025
	bne x12, x13, csr_mismatch
	li x12, 0x67428a6f
	csrrw x13, 0x342, x12
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x342, x12
	li x12, 0x0000002f
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x342, x12
	li x12, 0x8000002f
	bne x12, x13, csr_mismatch
	li x12, 0xaecea695
	csrrs x13, 0x342, x12
	li x12, 0x8000003f
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x342, x12
	li x12, 0x8000003f
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x342, x12
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	li x12, 0x0a63871f
	csrrc x13, 0x342, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x342, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x342, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x342, 0b01101
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x342, 0b00101
	li x12, 0x0000000d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x342, 0b11010
	li x12, 0x0000000d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x342, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0x342, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0x342, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0x342, 0b00001
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x342, x12
	# mtval
	li a1, 0x343
	li x12, 0xa5a5a5a5
	csrrw x13, 0x343, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x343, x12
	li x12, 0xa5a5a5a5
	bne x12, x13, csr_mismatch
	li x12, 0x6a1faa6e
	csrrw x13, 0x343, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x343, x12
	li x12, 0x6a1faa6e
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x343, x12
	li x12, 0xefbfafef
	bne x12, x13, csr_mismatch
	li x12, 0x6b4a78e8
	csrrs x13, 0x343, x12
	li x12, 0xffffffff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x343, x12
	li x12, 0xffffffff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x343, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0x9845b92f
	csrrc x13, 0x343, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x343, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x343, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x343, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x343, 0b00101
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x343, 0b11010
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x343, 0b10000
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0x343, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0x343, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0x343, 0b01011
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x343, x12
	ret
.globl machine_mode_check
machine_mode_check:	la t1, glb_expect_illegal_insn
	# cycle
	li a1, 0xc00
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc00,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc00,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc00,0x0
	j csr_user_unauth
	csrrs x13, 0xc00,0x0
	li x12, 0x00000000
	csrrs x13, 0xc00,0x0
	li x12, 0x00000000
	csrrs x13, 0xc00,0x0
	li x12, 0x00000000
	csrrc x13, 0xc00,0x0
	li x12, 0x00000000
	csrrc x13, 0xc00,0x0
	li x12, 0x00000000
	csrrc x13, 0xc00,0x0
	li x12, 0x00000000
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc00, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc00, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc00, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xc00, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc00, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc00, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc00, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc00, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc00, 0b00000
	li x12, 0x00000000
	# instret
	li a1, 0xc02
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc02,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc02,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc02,0x0
	j csr_user_unauth
	csrrs x13, 0xc02,0x0
	li x12, 0x00000000
	csrrs x13, 0xc02,0x0
	li x12, 0x00000000
	csrrs x13, 0xc02,0x0
	li x12, 0x00000000
	csrrc x13, 0xc02,0x0
	li x12, 0x00000000
	csrrc x13, 0xc02,0x0
	li x12, 0x00000000
	csrrc x13, 0xc02,0x0
	li x12, 0x00000000
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc02, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc02, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc02, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xc02, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc02, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc02, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc02, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc02, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc02, 0b00000
	li x12, 0x00000000
	# cycleh
	li a1, 0xc80
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc80,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc80,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc80,0x0
	j csr_user_unauth
	csrrs x13, 0xc80,0x0
	li x12, 0x00000000
	csrrs x13, 0xc80,0x0
	li x12, 0x00000000
	csrrs x13, 0xc80,0x0
	li x12, 0x00000000
	csrrc x13, 0xc80,0x0
	li x12, 0x00000000
	csrrc x13, 0xc80,0x0
	li x12, 0x00000000
	csrrc x13, 0xc80,0x0
	li x12, 0x00000000
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc80, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc80, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc80, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xc80, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc80, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc80, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc80, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc80, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc80, 0b00000
	li x12, 0x00000000
	# instreth
	li a1, 0xc82
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc82,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc82,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc82,0x0
	j csr_user_unauth
	csrrs x13, 0xc82,0x0
	li x12, 0x00000000
	csrrs x13, 0xc82,0x0
	li x12, 0x00000000
	csrrs x13, 0xc82,0x0
	li x12, 0x00000000
	csrrc x13, 0xc82,0x0
	li x12, 0x00000000
	csrrc x13, 0xc82,0x0
	li x12, 0x00000000
	csrrc x13, 0xc82,0x0
	li x12, 0x00000000
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc82, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc82, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc82, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xc82, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc82, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc82, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc82, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc82, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc82, 0b00000
	li x12, 0x00000000
	# mcycle
	li a1, 0xb00
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb00, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb00, x12
	li x12, 0xa5a5a5a5
	li x12, 0xde5fbbb6
	csrrw x13, 0xb00, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb00, x12
	li x12, 0xde5fbbb6
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb00, x12
	li x12, 0xffffbfb7
	li x12, 0x251ce426
	csrrs x13, 0xb00, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb00, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb00, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa945780b
	csrrc x13, 0xb00, x12
	li x12, 0x00000000
	csrrwi x13, 0xb00, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb00, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb00, 0b11110
	li x12, 0x0000001a
	csrrsi x13, 0xb00, 0b00101
	li x12, 0x0000001e
	csrrsi x13, 0xb00, 0b11010
	li x12, 0x0000001f
	csrrsi x13, 0xb00, 0b10010
	li x12, 0x0000001f
	csrrci x13, 0xb00, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb00, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb00, 0b01011
	li x12, 0x00000000
	li x12, 0x00000000
	csrw 0xb00, x12
	# mcycleh
	li a1, 0xb80
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb80, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb80, x12
	li x12, 0xa5a5a5a5
	li x12, 0x9fc53e25
	csrrw x13, 0xb80, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb80, x12
	li x12, 0x9fc53e25
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb80, x12
	li x12, 0xbfe5bfa5
	li x12, 0xbfbc3e1e
	csrrs x13, 0xb80, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb80, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb80, x12
	li x12, 0x5a5a5a5a
	li x12, 0xe57d2373
	csrrc x13, 0xb80, x12
	li x12, 0x00000000
	csrrwi x13, 0xb80, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb80, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb80, 0b00100
	li x12, 0x0000001a
	csrrsi x13, 0xb80, 0b00101
	li x12, 0x00000004
	csrrsi x13, 0xb80, 0b11010
	li x12, 0x00000005
	csrrsi x13, 0xb80, 0b00111
	li x12, 0x0000001f
	csrrci x13, 0xb80, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb80, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb80, 0b11000
	li x12, 0x00000000
	li x12, 0x00000000
	csrw 0xb80, x12
	# minstret
	li a1, 0xb02
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb02, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb02, x12
	li x12, 0xa5a5a5a5
	li x12, 0x22749eec
	csrrw x13, 0xb02, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb02, x12
	li x12, 0x22749eec
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb02, x12
	li x12, 0xa7f5bfed
	li x12, 0xe3f7b36f
	csrrs x13, 0xb02, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb02, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb02, x12
	li x12, 0x5a5a5a5a
	li x12, 0x6e50ddb4
	csrrc x13, 0xb02, x12
	li x12, 0x00000000
	csrrwi x13, 0xb02, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb02, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb02, 0b01111
	li x12, 0x0000001a
	csrrsi x13, 0xb02, 0b00101
	li x12, 0x0000000f
	csrrsi x13, 0xb02, 0b11010
	li x12, 0x0000000f
	csrrsi x13, 0xb02, 0b11100
	li x12, 0x0000001f
	csrrci x13, 0xb02, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb02, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb02, 0b11101
	li x12, 0x00000000
	li x12, 0x00000000
	csrw 0xb02, x12
	# minstreth
	li a1, 0xb82
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb82, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb82, x12
	li x12, 0xa5a5a5a5
	li x12, 0xab01f08e
	csrrw x13, 0xb82, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb82, x12
	li x12, 0xab01f08e
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb82, x12
	li x12, 0xafa5f5af
	li x12, 0x3385bfad
	csrrs x13, 0xb82, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb82, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb82, x12
	li x12, 0x5a5a5a5a
	li x12, 0xfdd461d8
	csrrc x13, 0xb82, x12
	li x12, 0x00000000
	csrrwi x13, 0xb82, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb82, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb82, 0b01011
	li x12, 0x0000001a
	csrrsi x13, 0xb82, 0b00101
	li x12, 0x0000000b
	csrrsi x13, 0xb82, 0b11010
	li x12, 0x0000000f
	csrrsi x13, 0xb82, 0b01000
	li x12, 0x0000001f
	csrrci x13, 0xb82, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb82, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb82, 0b01001
	li x12, 0x00000000
	li x12, 0x00000000
	csrw 0xb82, x12
	# mhpmcounter3
	li a1, 0xb03
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb03, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb03, x12
	li x12, 0xa5a5a5a5
	li x12, 0xf51d6118
	csrrw x13, 0xb03, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb03, x12
	li x12, 0xf51d6118
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb03, x12
	li x12, 0xf5bde5bd
	li x12, 0x5ee7fa28
	csrrs x13, 0xb03, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb03, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb03, x12
	li x12, 0x5a5a5a5a
	li x12, 0xbb55e2bb
	csrrc x13, 0xb03, x12
	li x12, 0x00000000
	csrrwi x13, 0xb03, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb03, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb03, 0b10110
	li x12, 0x0000001a
	csrrsi x13, 0xb03, 0b00101
	li x12, 0x00000016
	csrrsi x13, 0xb03, 0b11010
	li x12, 0x00000017
	csrrsi x13, 0xb03, 0b00011
	li x12, 0x0000001f
	csrrci x13, 0xb03, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb03, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb03, 0b10110
	li x12, 0x00000000
	li x12, 0x00000000
	csrw 0xb03, x12
	# mhpmcounter4
	li a1, 0xb04
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb04, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb04, x12
	li x12, 0xa5a5a5a5
	li x12, 0x4b8d1909
	csrrw x13, 0xb04, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb04, x12
	li x12, 0x4b8d1909
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb04, x12
	li x12, 0xefadbdad
	li x12, 0x29361819
	csrrs x13, 0xb04, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb04, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb04, x12
	li x12, 0x5a5a5a5a
	li x12, 0x73f75630
	csrrc x13, 0xb04, x12
	li x12, 0x00000000
	csrrwi x13, 0xb04, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb04, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb04, 0b01110
	li x12, 0x0000001a
	csrrsi x13, 0xb04, 0b00101
	li x12, 0x0000000e
	csrrsi x13, 0xb04, 0b11010
	li x12, 0x0000000f
	csrrsi x13, 0xb04, 0b00110
	li x12, 0x0000001f
	csrrci x13, 0xb04, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb04, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb04, 0b11010
	li x12, 0x00000000
	li x12, 0x00000000
	csrw 0xb04, x12
	# mhpmcounter5
	li a1, 0xb05
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb05, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb05, x12
	li x12, 0xa5a5a5a5
	li x12, 0x74fd6466
	csrrw x13, 0xb05, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb05, x12
	li x12, 0x74fd6466
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb05, x12
	li x12, 0xf5fde5e7
	li x12, 0x1924ad21
	csrrs x13, 0xb05, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb05, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb05, x12
	li x12, 0x5a5a5a5a
	li x12, 0x8664dd1b
	csrrc x13, 0xb05, x12
	li x12, 0x00000000
	csrrwi x13, 0xb05, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb05, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb05, 0b00101
	li x12, 0x0000001a
	csrrsi x13, 0xb05, 0b00101
	li x12, 0x00000005
	csrrsi x13, 0xb05, 0b11010
	li x12, 0x00000005
	csrrsi x13, 0xb05, 0b01100
	li x12, 0x0000001f
	csrrci x13, 0xb05, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb05, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb05, 0b00001
	li x12, 0x00000000
	li x12, 0x00000000
	csrw 0xb05, x12
	# mhpmcounter6
	li a1, 0xb06
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb06, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb06, x12
	li x12, 0xa5a5a5a5
	li x12, 0x0506d836
	csrrw x13, 0xb06, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb06, x12
	li x12, 0x0506d836
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb06, x12
	li x12, 0xa5a7fdb7
	li x12, 0xc5dcd6e3
	csrrs x13, 0xb06, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb06, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb06, x12
	li x12, 0x5a5a5a5a
	li x12, 0x2384b118
	csrrc x13, 0xb06, x12
	li x12, 0x00000000
	csrrwi x13, 0xb06, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb06, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb06, 0b11010
	li x12, 0x0000001a
	csrrsi x13, 0xb06, 0b00101
	li x12, 0x0000001a
	csrrsi x13, 0xb06, 0b11010
	li x12, 0x0000001f
	csrrsi x13, 0xb06, 0b01100
	li x12, 0x0000001f
	csrrci x13, 0xb06, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb06, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb06, 0b01100
	li x12, 0x00000000
	li x12, 0x00000000
	csrw 0xb06, x12
	# mhpmcounter7
	li a1, 0xb07
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb07, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb07, x12
	li x12, 0xa5a5a5a5
	li x12, 0xb7f837d4
	csrrw x13, 0xb07, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb07, x12
	li x12, 0xb7f837d4
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb07, x12
	li x12, 0xb7fdb7f5
	li x12, 0x4c9ae724
	csrrs x13, 0xb07, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb07, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb07, x12
	li x12, 0x5a5a5a5a
	li x12, 0x6f4cd755
	csrrc x13, 0xb07, x12
	li x12, 0x00000000
	csrrwi x13, 0xb07, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb07, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb07, 0b00001
	li x12, 0x0000001a
	csrrsi x13, 0xb07, 0b00101
	li x12, 0x00000001
	csrrsi x13, 0xb07, 0b11010
	li x12, 0x00000005
	csrrsi x13, 0xb07, 0b11101
	li x12, 0x0000001f
	csrrci x13, 0xb07, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb07, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb07, 0b01111
	li x12, 0x00000000
	li x12, 0x00000000
	csrw 0xb07, x12
	# mhpmcounter8
	li a1, 0xb08
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb08, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb08, x12
	li x12, 0xa5a5a5a5
	li x12, 0x4a717444
	csrrw x13, 0xb08, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb08, x12
	li x12, 0x4a717444
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb08, x12
	li x12, 0xeff5f5e5
	li x12, 0xc08a9130
	csrrs x13, 0xb08, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb08, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb08, x12
	li x12, 0x5a5a5a5a
	li x12, 0xc685eb35
	csrrc x13, 0xb08, x12
	li x12, 0x00000000
	csrrwi x13, 0xb08, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb08, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb08, 0b01000
	li x12, 0x0000001a
	csrrsi x13, 0xb08, 0b00101
	li x12, 0x00000008
	csrrsi x13, 0xb08, 0b11010
	li x12, 0x0000000d
	csrrsi x13, 0xb08, 0b00111
	li x12, 0x0000001f
	csrrci x13, 0xb08, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb08, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb08, 0b00111
	li x12, 0x00000000
	li x12, 0x00000000
	csrw 0xb08, x12
	# mhpmcounter9
	li a1, 0xb09
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb09, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb09, x12
	li x12, 0xa5a5a5a5
	li x12, 0x6487b250
	csrrw x13, 0xb09, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb09, x12
	li x12, 0x6487b250
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb09, x12
	li x12, 0xe5a7b7f5
	li x12, 0xfede8f49
	csrrs x13, 0xb09, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb09, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb09, x12
	li x12, 0x5a5a5a5a
	li x12, 0xb09b822a
	csrrc x13, 0xb09, x12
	li x12, 0x00000000
	csrrwi x13, 0xb09, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb09, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb09, 0b00011
	li x12, 0x0000001a
	csrrsi x13, 0xb09, 0b00101
	li x12, 0x00000003
	csrrsi x13, 0xb09, 0b11010
	li x12, 0x00000007
	csrrsi x13, 0xb09, 0b01001
	li x12, 0x0000001f
	csrrci x13, 0xb09, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb09, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb09, 0b10101
	li x12, 0x00000000
	li x12, 0x00000000
	csrw 0xb09, x12
	# mhpmcounter10
	li a1, 0xb0a
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb0a, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb0a, x12
	li x12, 0xa5a5a5a5
	li x12, 0x961c24c4
	csrrw x13, 0xb0a, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb0a, x12
	li x12, 0x961c24c4
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb0a, x12
	li x12, 0xb7bda5e5
	li x12, 0x11e98bd6
	csrrs x13, 0xb0a, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb0a, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb0a, x12
	li x12, 0x5a5a5a5a
	li x12, 0xd82ec17b
	csrrc x13, 0xb0a, x12
	li x12, 0x00000000
	csrrwi x13, 0xb0a, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb0a, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb0a, 0b01101
	li x12, 0x0000001a
	csrrsi x13, 0xb0a, 0b00101
	li x12, 0x0000000d
	csrrsi x13, 0xb0a, 0b11010
	li x12, 0x0000000d
	csrrsi x13, 0xb0a, 0b10010
	li x12, 0x0000001f
	csrrci x13, 0xb0a, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb0a, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb0a, 0b10010
	li x12, 0x00000000
	li x12, 0x00000000
	csrw 0xb0a, x12
	# mhpmcounter11
	li a1, 0xb0b
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb0b, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb0b, x12
	li x12, 0xa5a5a5a5
	bne x12, x13, csr_mismatch
	li x12, 0xd1d461f0
	csrrw x13, 0xb0b, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb0b, x12
	li x12, 0xd1d461f0
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb0b, x12
	li x12, 0xf5f5e5f5
	bne x12, x13, csr_mismatch
	li x12, 0x372eef25
	csrrs x13, 0xb0b, x12
	li x12, 0xffffffff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb0b, x12
	li x12, 0xffffffff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb0b, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0xb0763b94
	csrrc x13, 0xb0b, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb0b, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb0b, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb0b, 0b00010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb0b, 0b00101
	li x12, 0x00000002
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb0b, 0b11010
	li x12, 0x00000007
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb0b, 0b10010
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb0b, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb0b, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb0b, 0b01110
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0xb0b, x12
	# mhpmcounter12
	li a1, 0xb0c
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb0c, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb0c, x12
	li x12, 0xa5a5a5a5
	bne x12, x13, csr_mismatch
	li x12, 0xd3cff628
	csrrw x13, 0xb0c, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb0c, x12
	li x12, 0xd3cff628
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb0c, x12
	li x12, 0xf7eff7ad
	bne x12, x13, csr_mismatch
	li x12, 0xa8180087
	csrrs x13, 0xb0c, x12
	li x12, 0xffffffff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb0c, x12
	li x12, 0xffffffff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb0c, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0xaf2a2d82
	csrrc x13, 0xb0c, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb0c, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb0c, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb0c, 0b11011
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb0c, 0b00101
	li x12, 0x0000001b
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb0c, 0b11010
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb0c, 0b00111
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb0c, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb0c, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb0c, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0xb0c, x12
	# mhpmcounter3h
	li a1, 0xb83
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb83, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb83, x12
	li x12, 0x000000a5
	bne x12, x13, csr_mismatch
	li x12, 0x41fc06d8
	csrrw x13, 0xb83, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb83, x12
	li x12, 0x000000d8
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb83, x12
	li x12, 0x000000fd
	bne x12, x13, csr_mismatch
	li x12, 0x1ab184bf
	csrrs x13, 0xb83, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb83, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb83, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0x9828c44f
	csrrc x13, 0xb83, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb83, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb83, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb83, 0b11001
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb83, 0b00101
	li x12, 0x00000019
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb83, 0b11010
	li x12, 0x0000001d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb83, 0b01011
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb83, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb83, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb83, 0b10001
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0xb83, x12
	# mhpmcounter4h
	li a1, 0xb84
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb84, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb84, x12
	li x12, 0x000000a5
	bne x12, x13, csr_mismatch
	li x12, 0xcabe6019
	csrrw x13, 0xb84, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb84, x12
	li x12, 0x00000019
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb84, x12
	li x12, 0x000000bd
	bne x12, x13, csr_mismatch
	li x12, 0x21b0e115
	csrrs x13, 0xb84, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb84, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb84, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0x614130ab
	csrrc x13, 0xb84, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb84, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb84, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb84, 0b11100
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb84, 0b00101
	li x12, 0x0000001c
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb84, 0b11010
	li x12, 0x0000001d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb84, 0b10011
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb84, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb84, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb84, 0b10111
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0xb84, x12
	# mhpmcounter5h
	li a1, 0xb85
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb85, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb85, x12
	li x12, 0x000000a5
	bne x12, x13, csr_mismatch
	li x12, 0x68291688
	csrrw x13, 0xb85, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb85, x12
	li x12, 0x00000088
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb85, x12
	li x12, 0x000000ad
	bne x12, x13, csr_mismatch
	li x12, 0xb7589302
	csrrs x13, 0xb85, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb85, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb85, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0x0592ab52
	csrrc x13, 0xb85, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb85, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb85, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb85, 0b01010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb85, 0b00101
	li x12, 0x0000000a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb85, 0b11010
	li x12, 0x0000000f
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb85, 0b01000
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb85, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb85, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb85, 0b11011
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0xb85, x12
	# mhpmcounter6h
	li a1, 0xb86
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb86, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb86, x12
	li x12, 0x000000a5
	bne x12, x13, csr_mismatch
	li x12, 0x38c76021
	csrrw x13, 0xb86, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb86, x12
	li x12, 0x00000021
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb86, x12
	li x12, 0x000000a5
	bne x12, x13, csr_mismatch
	li x12, 0xde561c82
	csrrs x13, 0xb86, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb86, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb86, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0x8cf3c6b1
	csrrc x13, 0xb86, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb86, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb86, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb86, 0b01000
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb86, 0b00101
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb86, 0b11010
	li x12, 0x0000000d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb86, 0b11010
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb86, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb86, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb86, 0b00011
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0xb86, x12
	# mhpmcounter7h
	li a1, 0xb87
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb87, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb87, x12
	li x12, 0x000000a5
	bne x12, x13, csr_mismatch
	li x12, 0x34c437d3
	csrrw x13, 0xb87, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb87, x12
	li x12, 0x000000d3
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb87, x12
	li x12, 0x000000f7
	bne x12, x13, csr_mismatch
	li x12, 0x3629c94b
	csrrs x13, 0xb87, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb87, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb87, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xaba3cbb6
	csrrc x13, 0xb87, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb87, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb87, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb87, 0b00011
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb87, 0b00101
	li x12, 0x00000003
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb87, 0b11010
	li x12, 0x00000007
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb87, 0b10111
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb87, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb87, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb87, 0b01010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0xb87, x12
	# mhpmcounter8h
	li a1, 0xb88
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb88, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb88, x12
	li x12, 0x000000a5
	bne x12, x13, csr_mismatch
	li x12, 0xf08c70df
	csrrw x13, 0xb88, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb88, x12
	li x12, 0x000000df
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb88, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0x85c5d973
	csrrs x13, 0xb88, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb88, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb88, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa42923e1
	csrrc x13, 0xb88, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb88, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb88, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb88, 0b10100
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb88, 0b00101
	li x12, 0x00000014
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb88, 0b11010
	li x12, 0x00000015
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb88, 0b00000
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb88, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb88, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb88, 0b11101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0xb88, x12
	# mhpmcounter9h
	li a1, 0xb89
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb89, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb89, x12
	li x12, 0x000000a5
	bne x12, x13, csr_mismatch
	li x12, 0xd09c6a38
	csrrw x13, 0xb89, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb89, x12
	li x12, 0x00000038
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb89, x12
	li x12, 0x000000bd
	bne x12, x13, csr_mismatch
	li x12, 0x27cc9adf
	csrrs x13, 0xb89, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb89, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb89, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xd35e05ef
	csrrc x13, 0xb89, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb89, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb89, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb89, 0b00001
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb89, 0b00101
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb89, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb89, 0b01010
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb89, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb89, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb89, 0b01111
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0xb89, x12
	# mhpmcounter10h
	li a1, 0xb8a
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb8a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb8a, x12
	li x12, 0x000000a5
	bne x12, x13, csr_mismatch
	li x12, 0xa0acbd57
	csrrw x13, 0xb8a, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb8a, x12
	li x12, 0x00000057
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb8a, x12
	li x12, 0x000000f7
	bne x12, x13, csr_mismatch
	li x12, 0x2f3a37e3
	csrrs x13, 0xb8a, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb8a, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb8a, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0x0b51d4b3
	csrrc x13, 0xb8a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8a, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8a, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8a, 0b11111
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8a, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8a, 0b11010
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8a, 0b01110
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8a, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8a, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8a, 0b01101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0xb8a, x12
	# mhpmcounter11h
	li a1, 0xb8b
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb8b, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb8b, x12
	li x12, 0x000000a5
	bne x12, x13, csr_mismatch
	li x12, 0xd886c9bc
	csrrw x13, 0xb8b, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb8b, x12
	li x12, 0x000000bc
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb8b, x12
	li x12, 0x000000bd
	bne x12, x13, csr_mismatch
	li x12, 0xaed331fe
	csrrs x13, 0xb8b, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb8b, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb8b, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xe5b57061
	csrrc x13, 0xb8b, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8b, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8b, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8b, 0b11110
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8b, 0b00101
	li x12, 0x0000001e
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8b, 0b11010
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8b, 0b01100
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8b, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8b, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8b, 0b00010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0xb8b, x12
	# mhpmcounter12h
	li a1, 0xb8c
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb8c, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb8c, x12
	li x12, 0x000000a5
	bne x12, x13, csr_mismatch
	li x12, 0xc4a535ef
	csrrw x13, 0xb8c, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb8c, x12
	li x12, 0x000000ef
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb8c, x12
	li x12, 0x000000ef
	bne x12, x13, csr_mismatch
	li x12, 0x6f811e4d
	csrrs x13, 0xb8c, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb8c, x12
	li x12, 0x000000ff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb8c, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xdae0e5ca
	csrrc x13, 0xb8c, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8c, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8c, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8c, 0b00000
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8c, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8c, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8c, 0b10000
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8c, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8c, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8c, 0b00001
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0xb8c, x12
	# misa
	li a1, 0x301
	li x12, 0xa5a5a5a5
	csrrw x13, 0x301, x12
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x301, x12
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	li x12, 0x20910965
	csrrw x13, 0x301, x12
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x301, x12
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x301, x12
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	li x12, 0x33b407a1
	csrrs x13, 0x301, x12
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x301, x12
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x301, x12
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	li x12, 0x5dc41c9c
	csrrc x13, 0x301, x12
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x301, 0b00101
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x301, 0b11010
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x301, 0b10110
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x301, 0b00101
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x301, 0b11010
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x301, 0b00000
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrci x13, 0x301, 0b00101
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrci x13, 0x301, 0b11010
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrci x13, 0x301, 0b00100
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	li x12, 0x40101104
	csrw 0x301, x12
	# mie
	li a1, 0x304
	li x12, 0xa5a5a5a5
	csrrw x13, 0x304, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x304, x12
	li x12, 0xa5a50080
	bne x12, x13, csr_mismatch
	li x12, 0xdc9e5841
	csrrw x13, 0x304, x12
	li x12, 0x5a5a0808
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x304, x12
	li x12, 0xdc9e0800
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x304, x12
	li x12, 0xfdbf0880
	bne x12, x13, csr_mismatch
	li x12, 0x936aff3f
	csrrs x13, 0x304, x12
	li x12, 0xffff0888
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x304, x12
	li x12, 0xffff0888
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x304, x12
	li x12, 0x5a5a0808
	bne x12, x13, csr_mismatch
	li x12, 0x67fe93ed
	csrrc x13, 0x304, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x304, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x304, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x304, 0b10110
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x304, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x304, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x304, 0b10011
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrci x13, 0x304, 0b00101
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrci x13, 0x304, 0b11010
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrci x13, 0x304, 0b10101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x304, x12
	# mcounteren
	li a1, 0x306
	li x12, 0xa5a5a5a5
	csrrw x13, 0x306, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x306, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x56ab8cd2
	csrrw x13, 0x306, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x306, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x306, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xd2bdb74b
	csrrs x13, 0x306, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x306, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x306, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5c6743
	csrrc x13, 0x306, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x306, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x306, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x306, 0b11011
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x306, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x306, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x306, 0b11011
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x306, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x306, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x306, 0b01111
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x306, x12
	# mstatush
	li a1, 0x310
	li x12, 0xa5a5a5a5
	csrrw x13, 0x310, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x310, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x3720d749
	csrrw x13, 0x310, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x310, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x310, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xc77b520c
	csrrs x13, 0x310, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x310, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x310, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xd3e45017
	csrrc x13, 0x310, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x310, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x310, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x310, 0b01010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x310, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x310, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x310, 0b01100
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x310, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x310, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x310, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x310, x12
	# menvcfg
	li a1, 0x30a
	li x12, 0xa5a5a5a5
	csrrw x13, 0x30a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x30a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x7a67edbf
	csrrw x13, 0x30a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x30a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x30a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x7e3330af
	csrrs x13, 0x30a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x30a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x30a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xc7d8d41c
	csrrc x13, 0x30a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x30a, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x30a, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x30a, 0b11100
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x30a, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x30a, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x30a, 0b10111
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x30a, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x30a, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x30a, 0b00100
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x30a, x12
	# menvcfgh
	li a1, 0x31a
	li x12, 0xa5a5a5a5
	csrrw x13, 0x31a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x31a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x0be4d254
	csrrw x13, 0x31a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x31a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x31a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x0e1ba81c
	csrrs x13, 0x31a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x31a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x31a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xd9c994ae
	csrrc x13, 0x31a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x31a, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x31a, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x31a, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x31a, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x31a, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x31a, 0b01110
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x31a, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x31a, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x31a, 0b01010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x31a, x12
	# mcountinhibit
	li a1, 0x320
	li x12, 0xa5a5a5a5
	csrrw x13, 0x320, x12
	li x12, 0xffffe00d
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x320, x12
	li x12, 0xffffe5a5
	bne x12, x13, csr_mismatch
	li x12, 0xa2f555ab
	csrrw x13, 0x320, x12
	li x12, 0xfffffa58
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x320, x12
	li x12, 0xfffff5a9
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x320, x12
	li x12, 0xfffff5ad
	bne x12, x13, csr_mismatch
	li x12, 0x98991203
	csrrs x13, 0x320, x12
	li x12, 0xfffffffd
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x320, x12
	li x12, 0xfffffffd
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x320, x12
	li x12, 0xfffffa58
	bne x12, x13, csr_mismatch
	li x12, 0xe92bbdfb
	csrrc x13, 0x320, x12
	li x12, 0xffffe000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x320, 0b00101
	li x12, 0xffffe000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x320, 0b11010
	li x12, 0xffffe005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x320, 0b00100
	li x12, 0xffffe018
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x320, 0b00101
	li x12, 0xffffe004
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x320, 0b11010
	li x12, 0xffffe005
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x320, 0b10001
	li x12, 0xffffe01d
	bne x12, x13, csr_mismatch
	csrrci x13, 0x320, 0b00101
	li x12, 0xffffe01d
	bne x12, x13, csr_mismatch
	csrrci x13, 0x320, 0b11010
	li x12, 0xffffe018
	bne x12, x13, csr_mismatch
	csrrci x13, 0x320, 0b01101
	li x12, 0xffffe000
	bne x12, x13, csr_mismatch
	li x12, 0xffffe00d
	csrw 0x320, x12
	# mhpmevent3
	li a1, 0x323
	li x12, 0xa5a5a5a5
	csrrw x13, 0x323, x12
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x323, x12
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	li x12, 0x34114ee7
	csrrw x13, 0x323, x12
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x323, x12
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x323, x12
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	li x12, 0xf867d77b
	csrrs x13, 0x323, x12
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x323, x12
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x323, x12
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	li x12, 0x6a04bb37
	csrrc x13, 0x323, x12
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x323, 0b00101
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x323, 0b11010
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x323, 0b01000
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x323, 0b00101
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x323, 0b11010
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x323, 0b00101
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrci x13, 0x323, 0b00101
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrci x13, 0x323, 0b11010
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	csrrci x13, 0x323, 0b11000
	li x12, 0x00000008
	bne x12, x13, csr_mismatch
	li x12, 0x00000008
	csrw 0x323, x12
	# mhpmevent4
	li a1, 0x324
	li x12, 0xa5a5a5a5
	csrrw x13, 0x324, x12
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x324, x12
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	li x12, 0x388ff6ee
	csrrw x13, 0x324, x12
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x324, x12
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x324, x12
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	li x12, 0x84acb85d
	csrrs x13, 0x324, x12
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x324, x12
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x324, x12
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	li x12, 0x06d77eb1
	csrrc x13, 0x324, x12
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x324, 0b00101
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x324, 0b11010
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x324, 0b00101
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x324, 0b00101
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x324, 0b11010
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x324, 0b11000
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	csrrci x13, 0x324, 0b00101
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	csrrci x13, 0x324, 0b11010
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	csrrci x13, 0x324, 0b00000
	li x12, 0x00000010
	bne x12, x13, csr_mismatch
	li x12, 0x00000010
	csrw 0x324, x12
	# mhpmevent5
	li a1, 0x325
	li x12, 0xa5a5a5a5
	csrrw x13, 0x325, x12
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x325, x12
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	li x12, 0x95e5fcb7
	csrrw x13, 0x325, x12
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x325, x12
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x325, x12
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	li x12, 0x588ef8b3
	csrrs x13, 0x325, x12
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x325, x12
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x325, x12
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	li x12, 0x266599a3
	csrrc x13, 0x325, x12
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x325, 0b00101
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x325, 0b11010
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x325, 0b01110
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x325, 0b00101
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x325, 0b11010
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x325, 0b10100
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	csrrci x13, 0x325, 0b00101
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	csrrci x13, 0x325, 0b11010
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	csrrci x13, 0x325, 0b11001
	li x12, 0x00000020
	bne x12, x13, csr_mismatch
	li x12, 0x00000020
	csrw 0x325, x12
	# mhpmevent6
	li a1, 0x326
	li x12, 0xa5a5a5a5
	csrrw x13, 0x326, x12
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x326, x12
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	li x12, 0xa85ea219
	csrrw x13, 0x326, x12
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x326, x12
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x326, x12
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	li x12, 0x08b226b6
	csrrs x13, 0x326, x12
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x326, x12
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x326, x12
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	li x12, 0x1c832c8a
	csrrc x13, 0x326, x12
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x326, 0b00101
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x326, 0b11010
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x326, 0b11011
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x326, 0b00101
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x326, 0b11010
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x326, 0b11000
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	csrrci x13, 0x326, 0b00101
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	csrrci x13, 0x326, 0b11010
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	csrrci x13, 0x326, 0b10101
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	li x12, 0x00000040
	csrw 0x326, x12
	# mhpmevent7
	li a1, 0x327
	li x12, 0xa5a5a5a5
	csrrw x13, 0x327, x12
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x327, x12
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	li x12, 0xba3b296e
	csrrw x13, 0x327, x12
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x327, x12
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x327, x12
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	li x12, 0x71b06a4c
	csrrs x13, 0x327, x12
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x327, x12
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x327, x12
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	li x12, 0xa07a2bd2
	csrrc x13, 0x327, x12
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x327, 0b00101
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x327, 0b11010
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x327, 0b01111
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x327, 0b00101
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x327, 0b11010
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x327, 0b01100
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	csrrci x13, 0x327, 0b00101
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	csrrci x13, 0x327, 0b11010
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	csrrci x13, 0x327, 0b11000
	li x12, 0x00000080
	bne x12, x13, csr_mismatch
	li x12, 0x00000080
	csrw 0x327, x12
	# mhpmevent8
	li a1, 0x328
	li x12, 0xa5a5a5a5
	csrrw x13, 0x328, x12
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x328, x12
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	li x12, 0xba40ae6d
	csrrw x13, 0x328, x12
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x328, x12
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x328, x12
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	li x12, 0x1bea6776
	csrrs x13, 0x328, x12
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x328, x12
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x328, x12
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	li x12, 0xd6663650
	csrrc x13, 0x328, x12
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x328, 0b00101
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x328, 0b11010
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x328, 0b01001
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x328, 0b00101
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x328, 0b11010
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x328, 0b11111
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	csrrci x13, 0x328, 0b00101
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	csrrci x13, 0x328, 0b11010
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	csrrci x13, 0x328, 0b11011
	li x12, 0x00000100
	bne x12, x13, csr_mismatch
	li x12, 0x00000100
	csrw 0x328, x12
	# mhpmevent9
	li a1, 0x329
	li x12, 0xa5a5a5a5
	csrrw x13, 0x329, x12
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x329, x12
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	li x12, 0xd7ef9068
	csrrw x13, 0x329, x12
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x329, x12
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x329, x12
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	li x12, 0xeffe6cad
	csrrs x13, 0x329, x12
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x329, x12
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x329, x12
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	li x12, 0xa7ce22b9
	csrrc x13, 0x329, x12
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x329, 0b00101
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x329, 0b11010
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x329, 0b11111
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x329, 0b00101
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x329, 0b11010
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x329, 0b11000
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	csrrci x13, 0x329, 0b00101
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	csrrci x13, 0x329, 0b11010
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	csrrci x13, 0x329, 0b10000
	li x12, 0x00000200
	bne x12, x13, csr_mismatch
	li x12, 0x00000200
	csrw 0x329, x12
	# mhpmevent10
	li a1, 0x32a
	li x12, 0xa5a5a5a5
	csrrw x13, 0x32a, x12
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x32a, x12
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	li x12, 0xd6f12ba0
	csrrw x13, 0x32a, x12
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x32a, x12
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x32a, x12
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	li x12, 0x30c8710e
	csrrs x13, 0x32a, x12
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x32a, x12
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x32a, x12
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	li x12, 0x8a208e32
	csrrc x13, 0x32a, x12
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x32a, 0b00101
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x32a, 0b11010
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x32a, 0b10100
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x32a, 0b00101
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x32a, 0b11010
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x32a, 0b11010
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	csrrci x13, 0x32a, 0b00101
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	csrrci x13, 0x32a, 0b11010
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	csrrci x13, 0x32a, 0b00001
	li x12, 0x00000400
	bne x12, x13, csr_mismatch
	li x12, 0x00000400
	csrw 0x32a, x12
	# mhpmevent11
	li a1, 0x32b
	li x12, 0xa5a5a5a5
	csrrw x13, 0x32b, x12
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x32b, x12
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	li x12, 0xd3f1ce0b
	csrrw x13, 0x32b, x12
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x32b, x12
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x32b, x12
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	li x12, 0x1a09d938
	csrrs x13, 0x32b, x12
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x32b, x12
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x32b, x12
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	li x12, 0x06b6a418
	csrrc x13, 0x32b, x12
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x32b, 0b00101
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x32b, 0b11010
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x32b, 0b01000
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x32b, 0b00101
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x32b, 0b11010
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x32b, 0b11111
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	csrrci x13, 0x32b, 0b00101
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	csrrci x13, 0x32b, 0b11010
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	csrrci x13, 0x32b, 0b10111
	li x12, 0x00000800
	bne x12, x13, csr_mismatch
	li x12, 0x00000800
	csrw 0x32b, x12
	# mhpmevent12
	li a1, 0x32c
	li x12, 0xa5a5a5a5
	csrrw x13, 0x32c, x12
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x32c, x12
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	li x12, 0xd6cbb6b0
	csrrw x13, 0x32c, x12
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x32c, x12
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x32c, x12
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	li x12, 0xb8c38469
	csrrs x13, 0x32c, x12
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x32c, x12
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x32c, x12
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	li x12, 0x00c620f3
	csrrc x13, 0x32c, x12
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x32c, 0b00101
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x32c, 0b11010
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x32c, 0b10000
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x32c, 0b00101
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x32c, 0b11010
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x32c, 0b01010
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x32c, 0b00101
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x32c, 0b11010
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x32c, 0b11001
	li x12, 0x00001000
	bne x12, x13, csr_mismatch
	li x12, 0x00001000
	csrw 0x32c, x12
	# mscratch
	li a1, 0x340
	li x12, 0xa5a5a5a5
	csrrw x13, 0x340, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x340, x12
	li x12, 0xa5a5a5a5
	bne x12, x13, csr_mismatch
	li x12, 0x8eb7b28c
	csrrw x13, 0x340, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x340, x12
	li x12, 0x8eb7b28c
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x340, x12
	li x12, 0xafb7b7ad
	bne x12, x13, csr_mismatch
	li x12, 0x044f7866
	csrrs x13, 0x340, x12
	li x12, 0xffffffff
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x340, x12
	li x12, 0xffffffff
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x340, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0xdc4969f3
	csrrc x13, 0x340, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x340, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x340, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x340, 0b01111
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x340, 0b00101
	li x12, 0x0000000f
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x340, 0b11010
	li x12, 0x0000000f
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x340, 0b11010
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0x340, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0x340, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0x340, 0b01010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x340, x12
	# mip
	li a1, 0x344
	li x12, 0xa5a5a5a5
	csrrw x13, 0x344, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x344, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x6a340bbe
	csrrw x13, 0x344, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x344, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x344, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xfcdcdaf0
	csrrs x13, 0x344, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x344, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x344, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x8295b701
	csrrc x13, 0x344, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x344, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x344, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x344, 0b01111
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x344, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x344, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x344, 0b00010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x344, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x344, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x344, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x344, x12
	# tselect
	li a1, 0x7a0
	li x12, 0xa5a5a5a5
	csrrw x13, 0x7a0, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x7a0, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x47f71794
	csrrw x13, 0x7a0, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x7a0, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x7a0, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xe2bb6162
	csrrs x13, 0x7a0, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x7a0, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x7a0, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x0f642276
	csrrc x13, 0x7a0, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a0, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a0, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a0, 0b10000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a0, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a0, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a0, 0b01010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a0, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a0, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a0, 0b10010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x7a0, x12
	# tdata1
	li a1, 0x7a1
	li x12, 0xa5a5a5a5
	csrrw x13, 0x7a1, x12
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x7a1, x12
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	li x12, 0xea8e3ad3
	csrrw x13, 0x7a1, x12
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x7a1, x12
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x7a1, x12
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	li x12, 0x8602bd6b
	csrrs x13, 0x7a1, x12
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x7a1, x12
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x7a1, x12
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	li x12, 0x9c12ca46
	csrrc x13, 0x7a1, x12
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a1, 0b00101
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a1, 0b11010
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a1, 0b11100
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a1, 0b00101
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a1, 0b11010
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a1, 0b11111
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a1, 0b00101
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a1, 0b11010
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a1, 0b10000
	li x12, 0x28001048
	bne x12, x13, csr_mismatch
	li x12, 0x28001048
	csrw 0x7a1, x12
	# tdata2
	li a1, 0x7a2
	li x12, 0xa5a5a5a5
	csrrw x13, 0x7a2, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x7a2, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x873376b8
	csrrw x13, 0x7a2, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x7a2, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x7a2, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xd6cf03d6
	csrrs x13, 0x7a2, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x7a2, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x7a2, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xf8f1b48a
	csrrc x13, 0x7a2, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a2, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a2, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a2, 0b01100
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a2, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a2, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a2, 0b00001
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a2, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a2, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a2, 0b11011
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x7a2, x12
	# tdata3
	li a1, 0x7a3
	li x12, 0xa5a5a5a5
	csrrw x13, 0x7a3, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x7a3, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xcab8183f
	csrrw x13, 0x7a3, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x7a3, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x7a3, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x2f663f45
	csrrs x13, 0x7a3, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x7a3, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x7a3, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x4bf011d5
	csrrc x13, 0x7a3, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a3, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a3, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a3, 0b01100
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a3, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a3, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a3, 0b00010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a3, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a3, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a3, 0b11011
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x7a3, x12
	# mcontext
	li a1, 0x7a8
	li x12, 0xa5a5a5a5
	csrrw x13, 0x7a8, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x7a8, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x7a081cde
	csrrw x13, 0x7a8, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x7a8, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x7a8, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x9074128f
	csrrs x13, 0x7a8, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x7a8, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x7a8, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xd7566cde
	csrrc x13, 0x7a8, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a8, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a8, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a8, 0b10100
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a8, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a8, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a8, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a8, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a8, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a8, 0b01111
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x7a8, x12
	# scontext
	li a1, 0x7aa
	li x12, 0xa5a5a5a5
	csrrw x13, 0x7aa, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x7aa, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x3f7b8a79
	csrrw x13, 0x7aa, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x7aa, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x7aa, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x86c581c1
	csrrs x13, 0x7aa, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x7aa, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x7aa, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xd17d9894
	csrrc x13, 0x7aa, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7aa, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7aa, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7aa, 0b01111
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7aa, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7aa, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7aa, 0b10010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7aa, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7aa, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7aa, 0b00100
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x7aa, x12
	# secureseed
	li a1, 0x7c1
	li x12, 0xa5a5a5a5
	csrrw x13, 0x7c1, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x7c1, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xc8091048
	csrrw x13, 0x7c1, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x7c1, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x7c1, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x46e191df
	csrrs x13, 0x7c1, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x7c1, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x7c1, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x7ec1fcde
	csrrc x13, 0x7c1, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7c1, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7c1, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7c1, 0b00011
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7c1, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7c1, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7c1, 0b11101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7c1, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7c1, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7c1, 0b00010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x00000000
	csrw 0x7c1, x12
	# mvendorid
	li a1, 0xf11
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf11,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf11,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf11,0x0
	j csr_user_unauth
	csrrs x13, 0xf11,0x0
	li x12, 0x00000602
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf11,0x0
	li x12, 0x00000602
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf11,0x0
	li x12, 0x00000602
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf11,0x0
	li x12, 0x00000602
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf11,0x0
	li x12, 0x00000602
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf11,0x0
	li x12, 0x00000602
	bne x12, x13, csr_mismatch
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf11, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf11, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf11, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xf11, 0b00000
	li x12, 0x00000602
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf11, 0b00000
	li x12, 0x00000602
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf11, 0b00000
	li x12, 0x00000602
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf11, 0b00000
	li x12, 0x00000602
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf11, 0b00000
	li x12, 0x00000602
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf11, 0b00000
	li x12, 0x00000602
	bne x12, x13, csr_mismatch
	# marchid
	li a1, 0xf12
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf12,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf12,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf12,0x0
	j csr_user_unauth
	csrrs x13, 0xf12,0x0
	li x12, 0x00000023
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf12,0x0
	li x12, 0x00000023
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf12,0x0
	li x12, 0x00000023
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf12,0x0
	li x12, 0x00000023
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf12,0x0
	li x12, 0x00000023
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf12,0x0
	li x12, 0x00000023
	bne x12, x13, csr_mismatch
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf12, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf12, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf12, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xf12, 0b00000
	li x12, 0x00000023
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf12, 0b00000
	li x12, 0x00000023
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf12, 0b00000
	li x12, 0x00000023
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf12, 0b00000
	li x12, 0x00000023
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf12, 0b00000
	li x12, 0x00000023
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf12, 0b00000
	li x12, 0x00000023
	bne x12, x13, csr_mismatch
	# mimpid
	li a1, 0xf13
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf13,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf13,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf13,0x0
	j csr_user_unauth
	csrrs x13, 0xf13,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf13,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf13,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf13,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf13,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf13,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf13, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf13, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf13, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xf13, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf13, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf13, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf13, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf13, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf13, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	# mhartid
	li a1, 0xf14
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf14,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf14,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf14,0x0
	j csr_user_unauth
	csrrs x13, 0xf14,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf14,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf14,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf14,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf14,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf14,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf14, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf14, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf14, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xf14, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf14, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf14, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf14, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf14, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf14, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	# mconfigptr
	li a1, 0xf15
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf15,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf15,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf15,0x0
	j csr_user_unauth
	csrrs x13, 0xf15,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf15,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf15,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf15,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf15,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf15,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf15, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf15, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf15, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xf15, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf15, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf15, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf15, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf15, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf15, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	ret
.globl csr_check_unimplemented
csr_check_unimplemented:
	la t1, glb_expect_illegal_insn
	addi sp, sp, -4
	sw ra, 0(sp)
	li a1, 0x0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x0
	jal ra, csr_bad_impl
	li a1, 0x1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1
	jal ra, csr_bad_impl
	li a1, 0x2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2
	jal ra, csr_bad_impl
	li a1, 0x3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3
	jal ra, csr_bad_impl
	li a1, 0x4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4
	jal ra, csr_bad_impl
	li a1, 0x5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5
	jal ra, csr_bad_impl
	li a1, 0x6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6
	jal ra, csr_bad_impl
	li a1, 0x7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7
	jal ra, csr_bad_impl
	li a1, 0x8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8
	jal ra, csr_bad_impl
	li a1, 0x9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9
	jal ra, csr_bad_impl
	li a1, 0xa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa
	jal ra, csr_bad_impl
	li a1, 0xb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb
	jal ra, csr_bad_impl
	li a1, 0xc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc
	jal ra, csr_bad_impl
	li a1, 0xd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd
	jal ra, csr_bad_impl
	li a1, 0xe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe
	jal ra, csr_bad_impl
	li a1, 0xf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf
	jal ra, csr_bad_impl
	li a1, 0x10
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x10
	jal ra, csr_bad_impl
	li a1, 0x11
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x11
	jal ra, csr_bad_impl
	li a1, 0x12
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x12
	jal ra, csr_bad_impl
	li a1, 0x13
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x13
	jal ra, csr_bad_impl
	li a1, 0x14
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x14
	jal ra, csr_bad_impl
	li a1, 0x15
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x15
	jal ra, csr_bad_impl
	li a1, 0x16
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x16
	jal ra, csr_bad_impl
	li a1, 0x17
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x17
	jal ra, csr_bad_impl
	li a1, 0x18
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x18
	jal ra, csr_bad_impl
	li a1, 0x19
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x19
	jal ra, csr_bad_impl
	li a1, 0x1a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1a
	jal ra, csr_bad_impl
	li a1, 0x1b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1b
	jal ra, csr_bad_impl
	li a1, 0x1c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1c
	jal ra, csr_bad_impl
	li a1, 0x1d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1d
	jal ra, csr_bad_impl
	li a1, 0x1e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1e
	jal ra, csr_bad_impl
	li a1, 0x1f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1f
	jal ra, csr_bad_impl
	li a1, 0x20
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x20
	jal ra, csr_bad_impl
	li a1, 0x21
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x21
	jal ra, csr_bad_impl
	li a1, 0x22
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x22
	jal ra, csr_bad_impl
	li a1, 0x23
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x23
	jal ra, csr_bad_impl
	li a1, 0x24
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x24
	jal ra, csr_bad_impl
	li a1, 0x25
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x25
	jal ra, csr_bad_impl
	li a1, 0x26
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x26
	jal ra, csr_bad_impl
	li a1, 0x27
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x27
	jal ra, csr_bad_impl
	li a1, 0x28
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x28
	jal ra, csr_bad_impl
	li a1, 0x29
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x29
	jal ra, csr_bad_impl
	li a1, 0x2a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2a
	jal ra, csr_bad_impl
	li a1, 0x2b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2b
	jal ra, csr_bad_impl
	li a1, 0x2c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2c
	jal ra, csr_bad_impl
	li a1, 0x2d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2d
	jal ra, csr_bad_impl
	li a1, 0x2e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2e
	jal ra, csr_bad_impl
	li a1, 0x2f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2f
	jal ra, csr_bad_impl
	li a1, 0x30
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x30
	jal ra, csr_bad_impl
	li a1, 0x31
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x31
	jal ra, csr_bad_impl
	li a1, 0x32
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x32
	jal ra, csr_bad_impl
	li a1, 0x33
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x33
	jal ra, csr_bad_impl
	li a1, 0x34
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x34
	jal ra, csr_bad_impl
	li a1, 0x35
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x35
	jal ra, csr_bad_impl
	li a1, 0x36
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x36
	jal ra, csr_bad_impl
	li a1, 0x37
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x37
	jal ra, csr_bad_impl
	li a1, 0x38
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x38
	jal ra, csr_bad_impl
	li a1, 0x39
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x39
	jal ra, csr_bad_impl
	li a1, 0x3a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3a
	jal ra, csr_bad_impl
	li a1, 0x3b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3b
	jal ra, csr_bad_impl
	li a1, 0x3c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3c
	jal ra, csr_bad_impl
	li a1, 0x3d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3d
	jal ra, csr_bad_impl
	li a1, 0x3e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3e
	jal ra, csr_bad_impl
	li a1, 0x3f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3f
	jal ra, csr_bad_impl
	li a1, 0x40
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x40
	jal ra, csr_bad_impl
	li a1, 0x41
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x41
	jal ra, csr_bad_impl
	li a1, 0x42
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x42
	jal ra, csr_bad_impl
	li a1, 0x43
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x43
	jal ra, csr_bad_impl
	li a1, 0x44
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x44
	jal ra, csr_bad_impl
	li a1, 0x45
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x45
	jal ra, csr_bad_impl
	li a1, 0x46
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x46
	jal ra, csr_bad_impl
	li a1, 0x47
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x47
	jal ra, csr_bad_impl
	li a1, 0x48
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x48
	jal ra, csr_bad_impl
	li a1, 0x49
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x49
	jal ra, csr_bad_impl
	li a1, 0x4a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4a
	jal ra, csr_bad_impl
	li a1, 0x4b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4b
	jal ra, csr_bad_impl
	li a1, 0x4c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4c
	jal ra, csr_bad_impl
	li a1, 0x4d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4d
	jal ra, csr_bad_impl
	li a1, 0x4e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4e
	jal ra, csr_bad_impl
	li a1, 0x4f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4f
	jal ra, csr_bad_impl
	li a1, 0x50
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x50
	jal ra, csr_bad_impl
	li a1, 0x51
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x51
	jal ra, csr_bad_impl
	li a1, 0x52
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x52
	jal ra, csr_bad_impl
	li a1, 0x53
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x53
	jal ra, csr_bad_impl
	li a1, 0x54
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x54
	jal ra, csr_bad_impl
	li a1, 0x55
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x55
	jal ra, csr_bad_impl
	li a1, 0x56
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x56
	jal ra, csr_bad_impl
	li a1, 0x57
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x57
	jal ra, csr_bad_impl
	li a1, 0x58
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x58
	jal ra, csr_bad_impl
	li a1, 0x59
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x59
	jal ra, csr_bad_impl
	li a1, 0x5a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5a
	jal ra, csr_bad_impl
	li a1, 0x5b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5b
	jal ra, csr_bad_impl
	li a1, 0x5c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5c
	jal ra, csr_bad_impl
	li a1, 0x5d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5d
	jal ra, csr_bad_impl
	li a1, 0x5e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5e
	jal ra, csr_bad_impl
	li a1, 0x5f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5f
	jal ra, csr_bad_impl
	li a1, 0x60
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x60
	jal ra, csr_bad_impl
	li a1, 0x61
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x61
	jal ra, csr_bad_impl
	li a1, 0x62
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x62
	jal ra, csr_bad_impl
	li a1, 0x63
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x63
	jal ra, csr_bad_impl
	li a1, 0x64
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x64
	jal ra, csr_bad_impl
	li a1, 0x65
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x65
	jal ra, csr_bad_impl
	li a1, 0x66
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x66
	jal ra, csr_bad_impl
	li a1, 0x67
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x67
	jal ra, csr_bad_impl
	li a1, 0x68
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x68
	jal ra, csr_bad_impl
	li a1, 0x69
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x69
	jal ra, csr_bad_impl
	li a1, 0x6a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6a
	jal ra, csr_bad_impl
	li a1, 0x6b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6b
	jal ra, csr_bad_impl
	li a1, 0x6c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6c
	jal ra, csr_bad_impl
	li a1, 0x6d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6d
	jal ra, csr_bad_impl
	li a1, 0x6e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6e
	jal ra, csr_bad_impl
	li a1, 0x6f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6f
	jal ra, csr_bad_impl
	li a1, 0x70
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x70
	jal ra, csr_bad_impl
	li a1, 0x71
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x71
	jal ra, csr_bad_impl
	li a1, 0x72
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x72
	jal ra, csr_bad_impl
	li a1, 0x73
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x73
	jal ra, csr_bad_impl
	li a1, 0x74
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x74
	jal ra, csr_bad_impl
	li a1, 0x75
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x75
	jal ra, csr_bad_impl
	li a1, 0x76
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x76
	jal ra, csr_bad_impl
	li a1, 0x77
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x77
	jal ra, csr_bad_impl
	li a1, 0x78
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x78
	jal ra, csr_bad_impl
	li a1, 0x79
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x79
	jal ra, csr_bad_impl
	li a1, 0x7a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7a
	jal ra, csr_bad_impl
	li a1, 0x7b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7b
	jal ra, csr_bad_impl
	li a1, 0x7c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7c
	jal ra, csr_bad_impl
	li a1, 0x7d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7d
	jal ra, csr_bad_impl
	li a1, 0x7e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7e
	jal ra, csr_bad_impl
	li a1, 0x7f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7f
	jal ra, csr_bad_impl
	li a1, 0x80
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x80
	jal ra, csr_bad_impl
	li a1, 0x81
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x81
	jal ra, csr_bad_impl
	li a1, 0x82
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x82
	jal ra, csr_bad_impl
	li a1, 0x83
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x83
	jal ra, csr_bad_impl
	li a1, 0x84
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x84
	jal ra, csr_bad_impl
	li a1, 0x85
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x85
	jal ra, csr_bad_impl
	li a1, 0x86
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x86
	jal ra, csr_bad_impl
	li a1, 0x87
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x87
	jal ra, csr_bad_impl
	li a1, 0x88
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x88
	jal ra, csr_bad_impl
	li a1, 0x89
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x89
	jal ra, csr_bad_impl
	li a1, 0x8a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8a
	jal ra, csr_bad_impl
	li a1, 0x8b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8b
	jal ra, csr_bad_impl
	li a1, 0x8c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8c
	jal ra, csr_bad_impl
	li a1, 0x8d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8d
	jal ra, csr_bad_impl
	li a1, 0x8e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8e
	jal ra, csr_bad_impl
	li a1, 0x8f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8f
	jal ra, csr_bad_impl
	li a1, 0x90
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x90
	jal ra, csr_bad_impl
	li a1, 0x91
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x91
	jal ra, csr_bad_impl
	li a1, 0x92
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x92
	jal ra, csr_bad_impl
	li a1, 0x93
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x93
	jal ra, csr_bad_impl
	li a1, 0x94
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x94
	jal ra, csr_bad_impl
	li a1, 0x95
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x95
	jal ra, csr_bad_impl
	li a1, 0x96
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x96
	jal ra, csr_bad_impl
	li a1, 0x97
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x97
	jal ra, csr_bad_impl
	li a1, 0x98
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x98
	jal ra, csr_bad_impl
	li a1, 0x99
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x99
	jal ra, csr_bad_impl
	li a1, 0x9a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9a
	jal ra, csr_bad_impl
	li a1, 0x9b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9b
	jal ra, csr_bad_impl
	li a1, 0x9c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9c
	jal ra, csr_bad_impl
	li a1, 0x9d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9d
	jal ra, csr_bad_impl
	li a1, 0x9e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9e
	jal ra, csr_bad_impl
	li a1, 0x9f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9f
	jal ra, csr_bad_impl
	li a1, 0xa0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa0
	jal ra, csr_bad_impl
	li a1, 0xa1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa1
	jal ra, csr_bad_impl
	li a1, 0xa2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa2
	jal ra, csr_bad_impl
	li a1, 0xa3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa3
	jal ra, csr_bad_impl
	li a1, 0xa4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa4
	jal ra, csr_bad_impl
	li a1, 0xa5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa5
	jal ra, csr_bad_impl
	li a1, 0xa6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa6
	jal ra, csr_bad_impl
	li a1, 0xa7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa7
	jal ra, csr_bad_impl
	li a1, 0xa8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa8
	jal ra, csr_bad_impl
	li a1, 0xa9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa9
	jal ra, csr_bad_impl
	li a1, 0xaa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaa
	jal ra, csr_bad_impl
	li a1, 0xab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xab
	jal ra, csr_bad_impl
	li a1, 0xac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xac
	jal ra, csr_bad_impl
	li a1, 0xad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xad
	jal ra, csr_bad_impl
	li a1, 0xae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xae
	jal ra, csr_bad_impl
	li a1, 0xaf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaf
	jal ra, csr_bad_impl
	li a1, 0xb0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb0
	jal ra, csr_bad_impl
	li a1, 0xb1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb1
	jal ra, csr_bad_impl
	li a1, 0xb2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb2
	jal ra, csr_bad_impl
	li a1, 0xb3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb3
	jal ra, csr_bad_impl
	li a1, 0xb4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb4
	jal ra, csr_bad_impl
	li a1, 0xb5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb5
	jal ra, csr_bad_impl
	li a1, 0xb6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb6
	jal ra, csr_bad_impl
	li a1, 0xb7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb7
	jal ra, csr_bad_impl
	li a1, 0xb8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb8
	jal ra, csr_bad_impl
	li a1, 0xb9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb9
	jal ra, csr_bad_impl
	li a1, 0xba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xba
	jal ra, csr_bad_impl
	li a1, 0xbb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbb
	jal ra, csr_bad_impl
	li a1, 0xbc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbc
	jal ra, csr_bad_impl
	li a1, 0xbd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbd
	jal ra, csr_bad_impl
	li a1, 0xbe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbe
	jal ra, csr_bad_impl
	li a1, 0xbf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbf
	jal ra, csr_bad_impl
	li a1, 0xc0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc0
	jal ra, csr_bad_impl
	li a1, 0xc1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc1
	jal ra, csr_bad_impl
	li a1, 0xc2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc2
	jal ra, csr_bad_impl
	li a1, 0xc3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc3
	jal ra, csr_bad_impl
	li a1, 0xc4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc4
	jal ra, csr_bad_impl
	li a1, 0xc5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc5
	jal ra, csr_bad_impl
	li a1, 0xc6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc6
	jal ra, csr_bad_impl
	li a1, 0xc7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc7
	jal ra, csr_bad_impl
	li a1, 0xc8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc8
	jal ra, csr_bad_impl
	li a1, 0xc9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc9
	jal ra, csr_bad_impl
	li a1, 0xca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xca
	jal ra, csr_bad_impl
	li a1, 0xcb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcb
	jal ra, csr_bad_impl
	li a1, 0xcc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcc
	jal ra, csr_bad_impl
	li a1, 0xcd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcd
	jal ra, csr_bad_impl
	li a1, 0xce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xce
	jal ra, csr_bad_impl
	li a1, 0xcf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcf
	jal ra, csr_bad_impl
	li a1, 0xd0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd0
	jal ra, csr_bad_impl
	li a1, 0xd1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd1
	jal ra, csr_bad_impl
	li a1, 0xd2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd2
	jal ra, csr_bad_impl
	li a1, 0xd3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd3
	jal ra, csr_bad_impl
	li a1, 0xd4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd4
	jal ra, csr_bad_impl
	li a1, 0xd5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd5
	jal ra, csr_bad_impl
	li a1, 0xd6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd6
	jal ra, csr_bad_impl
	li a1, 0xd7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd7
	jal ra, csr_bad_impl
	li a1, 0xd8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd8
	jal ra, csr_bad_impl
	li a1, 0xd9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd9
	jal ra, csr_bad_impl
	li a1, 0xda
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xda
	jal ra, csr_bad_impl
	li a1, 0xdb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdb
	jal ra, csr_bad_impl
	li a1, 0xdc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdc
	jal ra, csr_bad_impl
	li a1, 0xdd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdd
	jal ra, csr_bad_impl
	li a1, 0xde
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xde
	jal ra, csr_bad_impl
	li a1, 0xdf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdf
	jal ra, csr_bad_impl
	li a1, 0xe0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe0
	jal ra, csr_bad_impl
	li a1, 0xe1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe1
	jal ra, csr_bad_impl
	li a1, 0xe2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe2
	jal ra, csr_bad_impl
	li a1, 0xe3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe3
	jal ra, csr_bad_impl
	li a1, 0xe4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe4
	jal ra, csr_bad_impl
	li a1, 0xe5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe5
	jal ra, csr_bad_impl
	li a1, 0xe6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe6
	jal ra, csr_bad_impl
	li a1, 0xe7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe7
	jal ra, csr_bad_impl
	li a1, 0xe8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe8
	jal ra, csr_bad_impl
	li a1, 0xe9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe9
	jal ra, csr_bad_impl
	li a1, 0xea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xea
	jal ra, csr_bad_impl
	li a1, 0xeb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeb
	jal ra, csr_bad_impl
	li a1, 0xec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xec
	jal ra, csr_bad_impl
	li a1, 0xed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xed
	jal ra, csr_bad_impl
	li a1, 0xee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xee
	jal ra, csr_bad_impl
	li a1, 0xef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xef
	jal ra, csr_bad_impl
	li a1, 0xf0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf0
	jal ra, csr_bad_impl
	li a1, 0xf1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf1
	jal ra, csr_bad_impl
	li a1, 0xf2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf2
	jal ra, csr_bad_impl
	li a1, 0xf3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf3
	jal ra, csr_bad_impl
	li a1, 0xf4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf4
	jal ra, csr_bad_impl
	li a1, 0xf5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf5
	jal ra, csr_bad_impl
	li a1, 0xf6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf6
	jal ra, csr_bad_impl
	li a1, 0xf7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf7
	jal ra, csr_bad_impl
	li a1, 0xf8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf8
	jal ra, csr_bad_impl
	li a1, 0xf9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf9
	jal ra, csr_bad_impl
	li a1, 0xfa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfa
	jal ra, csr_bad_impl
	li a1, 0xfb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfb
	jal ra, csr_bad_impl
	li a1, 0xfc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfc
	jal ra, csr_bad_impl
	li a1, 0xfd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfd
	jal ra, csr_bad_impl
	li a1, 0xfe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfe
	jal ra, csr_bad_impl
	li a1, 0xff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xff
	jal ra, csr_bad_impl
	li a1, 0x100
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x100
	jal ra, csr_bad_impl
	li a1, 0x101
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x101
	jal ra, csr_bad_impl
	li a1, 0x102
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x102
	jal ra, csr_bad_impl
	li a1, 0x103
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x103
	jal ra, csr_bad_impl
	li a1, 0x104
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x104
	jal ra, csr_bad_impl
	li a1, 0x105
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x105
	jal ra, csr_bad_impl
	li a1, 0x106
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x106
	jal ra, csr_bad_impl
	li a1, 0x107
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x107
	jal ra, csr_bad_impl
	li a1, 0x108
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x108
	jal ra, csr_bad_impl
	li a1, 0x109
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x109
	jal ra, csr_bad_impl
	li a1, 0x10a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x10a
	jal ra, csr_bad_impl
	li a1, 0x10b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x10b
	jal ra, csr_bad_impl
	li a1, 0x10c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x10c
	jal ra, csr_bad_impl
	li a1, 0x10d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x10d
	jal ra, csr_bad_impl
	li a1, 0x10e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x10e
	jal ra, csr_bad_impl
	li a1, 0x10f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x10f
	jal ra, csr_bad_impl
	li a1, 0x110
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x110
	jal ra, csr_bad_impl
	li a1, 0x111
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x111
	jal ra, csr_bad_impl
	li a1, 0x112
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x112
	jal ra, csr_bad_impl
	li a1, 0x113
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x113
	jal ra, csr_bad_impl
	li a1, 0x114
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x114
	jal ra, csr_bad_impl
	li a1, 0x115
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x115
	jal ra, csr_bad_impl
	li a1, 0x116
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x116
	jal ra, csr_bad_impl
	li a1, 0x117
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x117
	jal ra, csr_bad_impl
	li a1, 0x118
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x118
	jal ra, csr_bad_impl
	li a1, 0x119
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x119
	jal ra, csr_bad_impl
	li a1, 0x11a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x11a
	jal ra, csr_bad_impl
	li a1, 0x11b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x11b
	jal ra, csr_bad_impl
	li a1, 0x11c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x11c
	jal ra, csr_bad_impl
	li a1, 0x11d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x11d
	jal ra, csr_bad_impl
	li a1, 0x11e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x11e
	jal ra, csr_bad_impl
	li a1, 0x11f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x11f
	jal ra, csr_bad_impl
	li a1, 0x120
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x120
	jal ra, csr_bad_impl
	li a1, 0x121
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x121
	jal ra, csr_bad_impl
	li a1, 0x122
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x122
	jal ra, csr_bad_impl
	li a1, 0x123
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x123
	jal ra, csr_bad_impl
	li a1, 0x124
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x124
	jal ra, csr_bad_impl
	li a1, 0x125
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x125
	jal ra, csr_bad_impl
	li a1, 0x126
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x126
	jal ra, csr_bad_impl
	li a1, 0x127
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x127
	jal ra, csr_bad_impl
	li a1, 0x128
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x128
	jal ra, csr_bad_impl
	li a1, 0x129
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x129
	jal ra, csr_bad_impl
	li a1, 0x12a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x12a
	jal ra, csr_bad_impl
	li a1, 0x12b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x12b
	jal ra, csr_bad_impl
	li a1, 0x12c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x12c
	jal ra, csr_bad_impl
	li a1, 0x12d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x12d
	jal ra, csr_bad_impl
	li a1, 0x12e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x12e
	jal ra, csr_bad_impl
	li a1, 0x12f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x12f
	jal ra, csr_bad_impl
	li a1, 0x130
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x130
	jal ra, csr_bad_impl
	li a1, 0x131
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x131
	jal ra, csr_bad_impl
	li a1, 0x132
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x132
	jal ra, csr_bad_impl
	li a1, 0x133
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x133
	jal ra, csr_bad_impl
	li a1, 0x134
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x134
	jal ra, csr_bad_impl
	li a1, 0x135
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x135
	jal ra, csr_bad_impl
	li a1, 0x136
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x136
	jal ra, csr_bad_impl
	li a1, 0x137
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x137
	jal ra, csr_bad_impl
	li a1, 0x138
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x138
	jal ra, csr_bad_impl
	li a1, 0x139
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x139
	jal ra, csr_bad_impl
	li a1, 0x13a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x13a
	jal ra, csr_bad_impl
	li a1, 0x13b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x13b
	jal ra, csr_bad_impl
	li a1, 0x13c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x13c
	jal ra, csr_bad_impl
	li a1, 0x13d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x13d
	jal ra, csr_bad_impl
	li a1, 0x13e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x13e
	jal ra, csr_bad_impl
	li a1, 0x13f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x13f
	jal ra, csr_bad_impl
	li a1, 0x140
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x140
	jal ra, csr_bad_impl
	li a1, 0x141
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x141
	jal ra, csr_bad_impl
	li a1, 0x142
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x142
	jal ra, csr_bad_impl
	li a1, 0x143
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x143
	jal ra, csr_bad_impl
	li a1, 0x144
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x144
	jal ra, csr_bad_impl
	li a1, 0x145
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x145
	jal ra, csr_bad_impl
	li a1, 0x146
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x146
	jal ra, csr_bad_impl
	li a1, 0x147
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x147
	jal ra, csr_bad_impl
	li a1, 0x148
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x148
	jal ra, csr_bad_impl
	li a1, 0x149
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x149
	jal ra, csr_bad_impl
	li a1, 0x14a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x14a
	jal ra, csr_bad_impl
	li a1, 0x14b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x14b
	jal ra, csr_bad_impl
	li a1, 0x14c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x14c
	jal ra, csr_bad_impl
	li a1, 0x14d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x14d
	jal ra, csr_bad_impl
	li a1, 0x14e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x14e
	jal ra, csr_bad_impl
	li a1, 0x14f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x14f
	jal ra, csr_bad_impl
	li a1, 0x150
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x150
	jal ra, csr_bad_impl
	li a1, 0x151
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x151
	jal ra, csr_bad_impl
	li a1, 0x152
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x152
	jal ra, csr_bad_impl
	li a1, 0x153
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x153
	jal ra, csr_bad_impl
	li a1, 0x154
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x154
	jal ra, csr_bad_impl
	li a1, 0x155
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x155
	jal ra, csr_bad_impl
	li a1, 0x156
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x156
	jal ra, csr_bad_impl
	li a1, 0x157
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x157
	jal ra, csr_bad_impl
	li a1, 0x158
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x158
	jal ra, csr_bad_impl
	li a1, 0x159
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x159
	jal ra, csr_bad_impl
	li a1, 0x15a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x15a
	jal ra, csr_bad_impl
	li a1, 0x15b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x15b
	jal ra, csr_bad_impl
	li a1, 0x15c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x15c
	jal ra, csr_bad_impl
	li a1, 0x15d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x15d
	jal ra, csr_bad_impl
	li a1, 0x15e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x15e
	jal ra, csr_bad_impl
	li a1, 0x15f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x15f
	jal ra, csr_bad_impl
	li a1, 0x160
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x160
	jal ra, csr_bad_impl
	li a1, 0x161
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x161
	jal ra, csr_bad_impl
	li a1, 0x162
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x162
	jal ra, csr_bad_impl
	li a1, 0x163
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x163
	jal ra, csr_bad_impl
	li a1, 0x164
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x164
	jal ra, csr_bad_impl
	li a1, 0x165
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x165
	jal ra, csr_bad_impl
	li a1, 0x166
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x166
	jal ra, csr_bad_impl
	li a1, 0x167
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x167
	jal ra, csr_bad_impl
	li a1, 0x168
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x168
	jal ra, csr_bad_impl
	li a1, 0x169
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x169
	jal ra, csr_bad_impl
	li a1, 0x16a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x16a
	jal ra, csr_bad_impl
	li a1, 0x16b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x16b
	jal ra, csr_bad_impl
	li a1, 0x16c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x16c
	jal ra, csr_bad_impl
	li a1, 0x16d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x16d
	jal ra, csr_bad_impl
	li a1, 0x16e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x16e
	jal ra, csr_bad_impl
	li a1, 0x16f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x16f
	jal ra, csr_bad_impl
	li a1, 0x170
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x170
	jal ra, csr_bad_impl
	li a1, 0x171
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x171
	jal ra, csr_bad_impl
	li a1, 0x172
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x172
	jal ra, csr_bad_impl
	li a1, 0x173
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x173
	jal ra, csr_bad_impl
	li a1, 0x174
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x174
	jal ra, csr_bad_impl
	li a1, 0x175
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x175
	jal ra, csr_bad_impl
	li a1, 0x176
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x176
	jal ra, csr_bad_impl
	li a1, 0x177
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x177
	jal ra, csr_bad_impl
	li a1, 0x178
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x178
	jal ra, csr_bad_impl
	li a1, 0x179
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x179
	jal ra, csr_bad_impl
	li a1, 0x17a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x17a
	jal ra, csr_bad_impl
	li a1, 0x17b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x17b
	jal ra, csr_bad_impl
	li a1, 0x17c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x17c
	jal ra, csr_bad_impl
	li a1, 0x17d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x17d
	jal ra, csr_bad_impl
	li a1, 0x17e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x17e
	jal ra, csr_bad_impl
	li a1, 0x17f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x17f
	jal ra, csr_bad_impl
	li a1, 0x180
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x180
	jal ra, csr_bad_impl
	li a1, 0x181
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x181
	jal ra, csr_bad_impl
	li a1, 0x182
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x182
	jal ra, csr_bad_impl
	li a1, 0x183
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x183
	jal ra, csr_bad_impl
	li a1, 0x184
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x184
	jal ra, csr_bad_impl
	li a1, 0x185
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x185
	jal ra, csr_bad_impl
	li a1, 0x186
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x186
	jal ra, csr_bad_impl
	li a1, 0x187
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x187
	jal ra, csr_bad_impl
	li a1, 0x188
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x188
	jal ra, csr_bad_impl
	li a1, 0x189
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x189
	jal ra, csr_bad_impl
	li a1, 0x18a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x18a
	jal ra, csr_bad_impl
	li a1, 0x18b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x18b
	jal ra, csr_bad_impl
	li a1, 0x18c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x18c
	jal ra, csr_bad_impl
	li a1, 0x18d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x18d
	jal ra, csr_bad_impl
	li a1, 0x18e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x18e
	jal ra, csr_bad_impl
	li a1, 0x18f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x18f
	jal ra, csr_bad_impl
	li a1, 0x190
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x190
	jal ra, csr_bad_impl
	li a1, 0x191
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x191
	jal ra, csr_bad_impl
	li a1, 0x192
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x192
	jal ra, csr_bad_impl
	li a1, 0x193
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x193
	jal ra, csr_bad_impl
	li a1, 0x194
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x194
	jal ra, csr_bad_impl
	li a1, 0x195
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x195
	jal ra, csr_bad_impl
	li a1, 0x196
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x196
	jal ra, csr_bad_impl
	li a1, 0x197
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x197
	jal ra, csr_bad_impl
	li a1, 0x198
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x198
	jal ra, csr_bad_impl
	li a1, 0x199
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x199
	jal ra, csr_bad_impl
	li a1, 0x19a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x19a
	jal ra, csr_bad_impl
	li a1, 0x19b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x19b
	jal ra, csr_bad_impl
	li a1, 0x19c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x19c
	jal ra, csr_bad_impl
	li a1, 0x19d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x19d
	jal ra, csr_bad_impl
	li a1, 0x19e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x19e
	jal ra, csr_bad_impl
	li a1, 0x19f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x19f
	jal ra, csr_bad_impl
	li a1, 0x1a0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1a0
	jal ra, csr_bad_impl
	li a1, 0x1a1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1a1
	jal ra, csr_bad_impl
	li a1, 0x1a2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1a2
	jal ra, csr_bad_impl
	li a1, 0x1a3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1a3
	jal ra, csr_bad_impl
	li a1, 0x1a4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1a4
	jal ra, csr_bad_impl
	li a1, 0x1a5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1a5
	jal ra, csr_bad_impl
	li a1, 0x1a6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1a6
	jal ra, csr_bad_impl
	li a1, 0x1a7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1a7
	jal ra, csr_bad_impl
	li a1, 0x1a8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1a8
	jal ra, csr_bad_impl
	li a1, 0x1a9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1a9
	jal ra, csr_bad_impl
	li a1, 0x1aa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1aa
	jal ra, csr_bad_impl
	li a1, 0x1ab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ab
	jal ra, csr_bad_impl
	li a1, 0x1ac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ac
	jal ra, csr_bad_impl
	li a1, 0x1ad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ad
	jal ra, csr_bad_impl
	li a1, 0x1ae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ae
	jal ra, csr_bad_impl
	li a1, 0x1af
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1af
	jal ra, csr_bad_impl
	li a1, 0x1b0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1b0
	jal ra, csr_bad_impl
	li a1, 0x1b1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1b1
	jal ra, csr_bad_impl
	li a1, 0x1b2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1b2
	jal ra, csr_bad_impl
	li a1, 0x1b3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1b3
	jal ra, csr_bad_impl
	li a1, 0x1b4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1b4
	jal ra, csr_bad_impl
	li a1, 0x1b5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1b5
	jal ra, csr_bad_impl
	li a1, 0x1b6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1b6
	jal ra, csr_bad_impl
	li a1, 0x1b7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1b7
	jal ra, csr_bad_impl
	li a1, 0x1b8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1b8
	jal ra, csr_bad_impl
	li a1, 0x1b9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1b9
	jal ra, csr_bad_impl
	li a1, 0x1ba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ba
	jal ra, csr_bad_impl
	li a1, 0x1bb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1bb
	jal ra, csr_bad_impl
	li a1, 0x1bc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1bc
	jal ra, csr_bad_impl
	li a1, 0x1bd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1bd
	jal ra, csr_bad_impl
	li a1, 0x1be
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1be
	jal ra, csr_bad_impl
	li a1, 0x1bf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1bf
	jal ra, csr_bad_impl
	li a1, 0x1c0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1c0
	jal ra, csr_bad_impl
	li a1, 0x1c1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1c1
	jal ra, csr_bad_impl
	li a1, 0x1c2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1c2
	jal ra, csr_bad_impl
	li a1, 0x1c3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1c3
	jal ra, csr_bad_impl
	li a1, 0x1c4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1c4
	jal ra, csr_bad_impl
	li a1, 0x1c5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1c5
	jal ra, csr_bad_impl
	li a1, 0x1c6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1c6
	jal ra, csr_bad_impl
	li a1, 0x1c7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1c7
	jal ra, csr_bad_impl
	li a1, 0x1c8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1c8
	jal ra, csr_bad_impl
	li a1, 0x1c9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1c9
	jal ra, csr_bad_impl
	li a1, 0x1ca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ca
	jal ra, csr_bad_impl
	li a1, 0x1cb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1cb
	jal ra, csr_bad_impl
	li a1, 0x1cc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1cc
	jal ra, csr_bad_impl
	li a1, 0x1cd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1cd
	jal ra, csr_bad_impl
	li a1, 0x1ce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ce
	jal ra, csr_bad_impl
	li a1, 0x1cf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1cf
	jal ra, csr_bad_impl
	li a1, 0x1d0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1d0
	jal ra, csr_bad_impl
	li a1, 0x1d1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1d1
	jal ra, csr_bad_impl
	li a1, 0x1d2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1d2
	jal ra, csr_bad_impl
	li a1, 0x1d3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1d3
	jal ra, csr_bad_impl
	li a1, 0x1d4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1d4
	jal ra, csr_bad_impl
	li a1, 0x1d5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1d5
	jal ra, csr_bad_impl
	li a1, 0x1d6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1d6
	jal ra, csr_bad_impl
	li a1, 0x1d7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1d7
	jal ra, csr_bad_impl
	li a1, 0x1d8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1d8
	jal ra, csr_bad_impl
	li a1, 0x1d9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1d9
	jal ra, csr_bad_impl
	li a1, 0x1da
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1da
	jal ra, csr_bad_impl
	li a1, 0x1db
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1db
	jal ra, csr_bad_impl
	li a1, 0x1dc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1dc
	jal ra, csr_bad_impl
	li a1, 0x1dd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1dd
	jal ra, csr_bad_impl
	li a1, 0x1de
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1de
	jal ra, csr_bad_impl
	li a1, 0x1df
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1df
	jal ra, csr_bad_impl
	li a1, 0x1e0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1e0
	jal ra, csr_bad_impl
	li a1, 0x1e1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1e1
	jal ra, csr_bad_impl
	li a1, 0x1e2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1e2
	jal ra, csr_bad_impl
	li a1, 0x1e3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1e3
	jal ra, csr_bad_impl
	li a1, 0x1e4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1e4
	jal ra, csr_bad_impl
	li a1, 0x1e5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1e5
	jal ra, csr_bad_impl
	li a1, 0x1e6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1e6
	jal ra, csr_bad_impl
	li a1, 0x1e7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1e7
	jal ra, csr_bad_impl
	li a1, 0x1e8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1e8
	jal ra, csr_bad_impl
	li a1, 0x1e9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1e9
	jal ra, csr_bad_impl
	li a1, 0x1ea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ea
	jal ra, csr_bad_impl
	li a1, 0x1eb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1eb
	jal ra, csr_bad_impl
	li a1, 0x1ec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ec
	jal ra, csr_bad_impl
	li a1, 0x1ed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ed
	jal ra, csr_bad_impl
	li a1, 0x1ee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ee
	jal ra, csr_bad_impl
	li a1, 0x1ef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ef
	jal ra, csr_bad_impl
	li a1, 0x1f0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1f0
	jal ra, csr_bad_impl
	li a1, 0x1f1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1f1
	jal ra, csr_bad_impl
	li a1, 0x1f2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1f2
	jal ra, csr_bad_impl
	li a1, 0x1f3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1f3
	jal ra, csr_bad_impl
	li a1, 0x1f4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1f4
	jal ra, csr_bad_impl
	li a1, 0x1f5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1f5
	jal ra, csr_bad_impl
	li a1, 0x1f6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1f6
	jal ra, csr_bad_impl
	li a1, 0x1f7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1f7
	jal ra, csr_bad_impl
	li a1, 0x1f8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1f8
	jal ra, csr_bad_impl
	li a1, 0x1f9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1f9
	jal ra, csr_bad_impl
	li a1, 0x1fa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1fa
	jal ra, csr_bad_impl
	li a1, 0x1fb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1fb
	jal ra, csr_bad_impl
	li a1, 0x1fc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1fc
	jal ra, csr_bad_impl
	li a1, 0x1fd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1fd
	jal ra, csr_bad_impl
	li a1, 0x1fe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1fe
	jal ra, csr_bad_impl
	li a1, 0x1ff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x1ff
	jal ra, csr_bad_impl
	li a1, 0x200
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x200
	jal ra, csr_bad_impl
	li a1, 0x201
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x201
	jal ra, csr_bad_impl
	li a1, 0x202
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x202
	jal ra, csr_bad_impl
	li a1, 0x203
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x203
	jal ra, csr_bad_impl
	li a1, 0x204
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x204
	jal ra, csr_bad_impl
	li a1, 0x205
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x205
	jal ra, csr_bad_impl
	li a1, 0x206
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x206
	jal ra, csr_bad_impl
	li a1, 0x207
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x207
	jal ra, csr_bad_impl
	li a1, 0x208
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x208
	jal ra, csr_bad_impl
	li a1, 0x209
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x209
	jal ra, csr_bad_impl
	li a1, 0x20a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x20a
	jal ra, csr_bad_impl
	li a1, 0x20b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x20b
	jal ra, csr_bad_impl
	li a1, 0x20c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x20c
	jal ra, csr_bad_impl
	li a1, 0x20d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x20d
	jal ra, csr_bad_impl
	li a1, 0x20e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x20e
	jal ra, csr_bad_impl
	li a1, 0x20f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x20f
	jal ra, csr_bad_impl
	li a1, 0x210
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x210
	jal ra, csr_bad_impl
	li a1, 0x211
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x211
	jal ra, csr_bad_impl
	li a1, 0x212
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x212
	jal ra, csr_bad_impl
	li a1, 0x213
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x213
	jal ra, csr_bad_impl
	li a1, 0x214
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x214
	jal ra, csr_bad_impl
	li a1, 0x215
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x215
	jal ra, csr_bad_impl
	li a1, 0x216
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x216
	jal ra, csr_bad_impl
	li a1, 0x217
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x217
	jal ra, csr_bad_impl
	li a1, 0x218
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x218
	jal ra, csr_bad_impl
	li a1, 0x219
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x219
	jal ra, csr_bad_impl
	li a1, 0x21a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x21a
	jal ra, csr_bad_impl
	li a1, 0x21b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x21b
	jal ra, csr_bad_impl
	li a1, 0x21c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x21c
	jal ra, csr_bad_impl
	li a1, 0x21d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x21d
	jal ra, csr_bad_impl
	li a1, 0x21e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x21e
	jal ra, csr_bad_impl
	li a1, 0x21f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x21f
	jal ra, csr_bad_impl
	li a1, 0x220
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x220
	jal ra, csr_bad_impl
	li a1, 0x221
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x221
	jal ra, csr_bad_impl
	li a1, 0x222
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x222
	jal ra, csr_bad_impl
	li a1, 0x223
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x223
	jal ra, csr_bad_impl
	li a1, 0x224
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x224
	jal ra, csr_bad_impl
	li a1, 0x225
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x225
	jal ra, csr_bad_impl
	li a1, 0x226
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x226
	jal ra, csr_bad_impl
	li a1, 0x227
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x227
	jal ra, csr_bad_impl
	li a1, 0x228
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x228
	jal ra, csr_bad_impl
	li a1, 0x229
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x229
	jal ra, csr_bad_impl
	li a1, 0x22a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x22a
	jal ra, csr_bad_impl
	li a1, 0x22b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x22b
	jal ra, csr_bad_impl
	li a1, 0x22c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x22c
	jal ra, csr_bad_impl
	li a1, 0x22d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x22d
	jal ra, csr_bad_impl
	li a1, 0x22e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x22e
	jal ra, csr_bad_impl
	li a1, 0x22f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x22f
	jal ra, csr_bad_impl
	li a1, 0x230
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x230
	jal ra, csr_bad_impl
	li a1, 0x231
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x231
	jal ra, csr_bad_impl
	li a1, 0x232
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x232
	jal ra, csr_bad_impl
	li a1, 0x233
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x233
	jal ra, csr_bad_impl
	li a1, 0x234
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x234
	jal ra, csr_bad_impl
	li a1, 0x235
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x235
	jal ra, csr_bad_impl
	li a1, 0x236
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x236
	jal ra, csr_bad_impl
	li a1, 0x237
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x237
	jal ra, csr_bad_impl
	li a1, 0x238
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x238
	jal ra, csr_bad_impl
	li a1, 0x239
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x239
	jal ra, csr_bad_impl
	li a1, 0x23a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x23a
	jal ra, csr_bad_impl
	li a1, 0x23b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x23b
	jal ra, csr_bad_impl
	li a1, 0x23c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x23c
	jal ra, csr_bad_impl
	li a1, 0x23d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x23d
	jal ra, csr_bad_impl
	li a1, 0x23e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x23e
	jal ra, csr_bad_impl
	li a1, 0x23f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x23f
	jal ra, csr_bad_impl
	li a1, 0x240
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x240
	jal ra, csr_bad_impl
	li a1, 0x241
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x241
	jal ra, csr_bad_impl
	li a1, 0x242
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x242
	jal ra, csr_bad_impl
	li a1, 0x243
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x243
	jal ra, csr_bad_impl
	li a1, 0x244
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x244
	jal ra, csr_bad_impl
	li a1, 0x245
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x245
	jal ra, csr_bad_impl
	li a1, 0x246
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x246
	jal ra, csr_bad_impl
	li a1, 0x247
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x247
	jal ra, csr_bad_impl
	li a1, 0x248
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x248
	jal ra, csr_bad_impl
	li a1, 0x249
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x249
	jal ra, csr_bad_impl
	li a1, 0x24a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x24a
	jal ra, csr_bad_impl
	li a1, 0x24b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x24b
	jal ra, csr_bad_impl
	li a1, 0x24c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x24c
	jal ra, csr_bad_impl
	li a1, 0x24d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x24d
	jal ra, csr_bad_impl
	li a1, 0x24e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x24e
	jal ra, csr_bad_impl
	li a1, 0x24f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x24f
	jal ra, csr_bad_impl
	li a1, 0x250
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x250
	jal ra, csr_bad_impl
	li a1, 0x251
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x251
	jal ra, csr_bad_impl
	li a1, 0x252
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x252
	jal ra, csr_bad_impl
	li a1, 0x253
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x253
	jal ra, csr_bad_impl
	li a1, 0x254
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x254
	jal ra, csr_bad_impl
	li a1, 0x255
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x255
	jal ra, csr_bad_impl
	li a1, 0x256
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x256
	jal ra, csr_bad_impl
	li a1, 0x257
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x257
	jal ra, csr_bad_impl
	li a1, 0x258
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x258
	jal ra, csr_bad_impl
	li a1, 0x259
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x259
	jal ra, csr_bad_impl
	li a1, 0x25a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x25a
	jal ra, csr_bad_impl
	li a1, 0x25b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x25b
	jal ra, csr_bad_impl
	li a1, 0x25c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x25c
	jal ra, csr_bad_impl
	li a1, 0x25d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x25d
	jal ra, csr_bad_impl
	li a1, 0x25e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x25e
	jal ra, csr_bad_impl
	li a1, 0x25f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x25f
	jal ra, csr_bad_impl
	li a1, 0x260
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x260
	jal ra, csr_bad_impl
	li a1, 0x261
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x261
	jal ra, csr_bad_impl
	li a1, 0x262
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x262
	jal ra, csr_bad_impl
	li a1, 0x263
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x263
	jal ra, csr_bad_impl
	li a1, 0x264
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x264
	jal ra, csr_bad_impl
	li a1, 0x265
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x265
	jal ra, csr_bad_impl
	li a1, 0x266
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x266
	jal ra, csr_bad_impl
	li a1, 0x267
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x267
	jal ra, csr_bad_impl
	li a1, 0x268
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x268
	jal ra, csr_bad_impl
	li a1, 0x269
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x269
	jal ra, csr_bad_impl
	li a1, 0x26a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x26a
	jal ra, csr_bad_impl
	li a1, 0x26b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x26b
	jal ra, csr_bad_impl
	li a1, 0x26c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x26c
	jal ra, csr_bad_impl
	li a1, 0x26d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x26d
	jal ra, csr_bad_impl
	li a1, 0x26e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x26e
	jal ra, csr_bad_impl
	li a1, 0x26f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x26f
	jal ra, csr_bad_impl
	li a1, 0x270
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x270
	jal ra, csr_bad_impl
	li a1, 0x271
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x271
	jal ra, csr_bad_impl
	li a1, 0x272
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x272
	jal ra, csr_bad_impl
	li a1, 0x273
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x273
	jal ra, csr_bad_impl
	li a1, 0x274
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x274
	jal ra, csr_bad_impl
	li a1, 0x275
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x275
	jal ra, csr_bad_impl
	li a1, 0x276
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x276
	jal ra, csr_bad_impl
	li a1, 0x277
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x277
	jal ra, csr_bad_impl
	li a1, 0x278
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x278
	jal ra, csr_bad_impl
	li a1, 0x279
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x279
	jal ra, csr_bad_impl
	li a1, 0x27a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x27a
	jal ra, csr_bad_impl
	li a1, 0x27b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x27b
	jal ra, csr_bad_impl
	li a1, 0x27c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x27c
	jal ra, csr_bad_impl
	li a1, 0x27d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x27d
	jal ra, csr_bad_impl
	li a1, 0x27e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x27e
	jal ra, csr_bad_impl
	li a1, 0x27f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x27f
	jal ra, csr_bad_impl
	li a1, 0x280
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x280
	jal ra, csr_bad_impl
	li a1, 0x281
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x281
	jal ra, csr_bad_impl
	li a1, 0x282
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x282
	jal ra, csr_bad_impl
	li a1, 0x283
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x283
	jal ra, csr_bad_impl
	li a1, 0x284
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x284
	jal ra, csr_bad_impl
	li a1, 0x285
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x285
	jal ra, csr_bad_impl
	li a1, 0x286
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x286
	jal ra, csr_bad_impl
	li a1, 0x287
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x287
	jal ra, csr_bad_impl
	li a1, 0x288
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x288
	jal ra, csr_bad_impl
	li a1, 0x289
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x289
	jal ra, csr_bad_impl
	li a1, 0x28a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x28a
	jal ra, csr_bad_impl
	li a1, 0x28b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x28b
	jal ra, csr_bad_impl
	li a1, 0x28c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x28c
	jal ra, csr_bad_impl
	li a1, 0x28d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x28d
	jal ra, csr_bad_impl
	li a1, 0x28e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x28e
	jal ra, csr_bad_impl
	li a1, 0x28f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x28f
	jal ra, csr_bad_impl
	li a1, 0x290
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x290
	jal ra, csr_bad_impl
	li a1, 0x291
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x291
	jal ra, csr_bad_impl
	li a1, 0x292
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x292
	jal ra, csr_bad_impl
	li a1, 0x293
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x293
	jal ra, csr_bad_impl
	li a1, 0x294
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x294
	jal ra, csr_bad_impl
	li a1, 0x295
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x295
	jal ra, csr_bad_impl
	li a1, 0x296
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x296
	jal ra, csr_bad_impl
	li a1, 0x297
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x297
	jal ra, csr_bad_impl
	li a1, 0x298
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x298
	jal ra, csr_bad_impl
	li a1, 0x299
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x299
	jal ra, csr_bad_impl
	li a1, 0x29a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x29a
	jal ra, csr_bad_impl
	li a1, 0x29b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x29b
	jal ra, csr_bad_impl
	li a1, 0x29c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x29c
	jal ra, csr_bad_impl
	li a1, 0x29d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x29d
	jal ra, csr_bad_impl
	li a1, 0x29e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x29e
	jal ra, csr_bad_impl
	li a1, 0x29f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x29f
	jal ra, csr_bad_impl
	li a1, 0x2a0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2a0
	jal ra, csr_bad_impl
	li a1, 0x2a1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2a1
	jal ra, csr_bad_impl
	li a1, 0x2a2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2a2
	jal ra, csr_bad_impl
	li a1, 0x2a3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2a3
	jal ra, csr_bad_impl
	li a1, 0x2a4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2a4
	jal ra, csr_bad_impl
	li a1, 0x2a5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2a5
	jal ra, csr_bad_impl
	li a1, 0x2a6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2a6
	jal ra, csr_bad_impl
	li a1, 0x2a7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2a7
	jal ra, csr_bad_impl
	li a1, 0x2a8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2a8
	jal ra, csr_bad_impl
	li a1, 0x2a9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2a9
	jal ra, csr_bad_impl
	li a1, 0x2aa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2aa
	jal ra, csr_bad_impl
	li a1, 0x2ab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ab
	jal ra, csr_bad_impl
	li a1, 0x2ac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ac
	jal ra, csr_bad_impl
	li a1, 0x2ad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ad
	jal ra, csr_bad_impl
	li a1, 0x2ae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ae
	jal ra, csr_bad_impl
	li a1, 0x2af
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2af
	jal ra, csr_bad_impl
	li a1, 0x2b0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2b0
	jal ra, csr_bad_impl
	li a1, 0x2b1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2b1
	jal ra, csr_bad_impl
	li a1, 0x2b2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2b2
	jal ra, csr_bad_impl
	li a1, 0x2b3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2b3
	jal ra, csr_bad_impl
	li a1, 0x2b4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2b4
	jal ra, csr_bad_impl
	li a1, 0x2b5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2b5
	jal ra, csr_bad_impl
	li a1, 0x2b6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2b6
	jal ra, csr_bad_impl
	li a1, 0x2b7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2b7
	jal ra, csr_bad_impl
	li a1, 0x2b8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2b8
	jal ra, csr_bad_impl
	li a1, 0x2b9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2b9
	jal ra, csr_bad_impl
	li a1, 0x2ba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ba
	jal ra, csr_bad_impl
	li a1, 0x2bb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2bb
	jal ra, csr_bad_impl
	li a1, 0x2bc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2bc
	jal ra, csr_bad_impl
	li a1, 0x2bd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2bd
	jal ra, csr_bad_impl
	li a1, 0x2be
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2be
	jal ra, csr_bad_impl
	li a1, 0x2bf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2bf
	jal ra, csr_bad_impl
	li a1, 0x2c0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2c0
	jal ra, csr_bad_impl
	li a1, 0x2c1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2c1
	jal ra, csr_bad_impl
	li a1, 0x2c2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2c2
	jal ra, csr_bad_impl
	li a1, 0x2c3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2c3
	jal ra, csr_bad_impl
	li a1, 0x2c4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2c4
	jal ra, csr_bad_impl
	li a1, 0x2c5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2c5
	jal ra, csr_bad_impl
	li a1, 0x2c6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2c6
	jal ra, csr_bad_impl
	li a1, 0x2c7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2c7
	jal ra, csr_bad_impl
	li a1, 0x2c8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2c8
	jal ra, csr_bad_impl
	li a1, 0x2c9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2c9
	jal ra, csr_bad_impl
	li a1, 0x2ca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ca
	jal ra, csr_bad_impl
	li a1, 0x2cb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2cb
	jal ra, csr_bad_impl
	li a1, 0x2cc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2cc
	jal ra, csr_bad_impl
	li a1, 0x2cd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2cd
	jal ra, csr_bad_impl
	li a1, 0x2ce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ce
	jal ra, csr_bad_impl
	li a1, 0x2cf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2cf
	jal ra, csr_bad_impl
	li a1, 0x2d0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2d0
	jal ra, csr_bad_impl
	li a1, 0x2d1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2d1
	jal ra, csr_bad_impl
	li a1, 0x2d2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2d2
	jal ra, csr_bad_impl
	li a1, 0x2d3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2d3
	jal ra, csr_bad_impl
	li a1, 0x2d4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2d4
	jal ra, csr_bad_impl
	li a1, 0x2d5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2d5
	jal ra, csr_bad_impl
	li a1, 0x2d6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2d6
	jal ra, csr_bad_impl
	li a1, 0x2d7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2d7
	jal ra, csr_bad_impl
	li a1, 0x2d8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2d8
	jal ra, csr_bad_impl
	li a1, 0x2d9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2d9
	jal ra, csr_bad_impl
	li a1, 0x2da
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2da
	jal ra, csr_bad_impl
	li a1, 0x2db
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2db
	jal ra, csr_bad_impl
	li a1, 0x2dc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2dc
	jal ra, csr_bad_impl
	li a1, 0x2dd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2dd
	jal ra, csr_bad_impl
	li a1, 0x2de
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2de
	jal ra, csr_bad_impl
	li a1, 0x2df
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2df
	jal ra, csr_bad_impl
	li a1, 0x2e0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2e0
	jal ra, csr_bad_impl
	li a1, 0x2e1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2e1
	jal ra, csr_bad_impl
	li a1, 0x2e2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2e2
	jal ra, csr_bad_impl
	li a1, 0x2e3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2e3
	jal ra, csr_bad_impl
	li a1, 0x2e4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2e4
	jal ra, csr_bad_impl
	li a1, 0x2e5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2e5
	jal ra, csr_bad_impl
	li a1, 0x2e6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2e6
	jal ra, csr_bad_impl
	li a1, 0x2e7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2e7
	jal ra, csr_bad_impl
	li a1, 0x2e8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2e8
	jal ra, csr_bad_impl
	li a1, 0x2e9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2e9
	jal ra, csr_bad_impl
	li a1, 0x2ea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ea
	jal ra, csr_bad_impl
	li a1, 0x2eb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2eb
	jal ra, csr_bad_impl
	li a1, 0x2ec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ec
	jal ra, csr_bad_impl
	li a1, 0x2ed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ed
	jal ra, csr_bad_impl
	li a1, 0x2ee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ee
	jal ra, csr_bad_impl
	li a1, 0x2ef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ef
	jal ra, csr_bad_impl
	li a1, 0x2f0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2f0
	jal ra, csr_bad_impl
	li a1, 0x2f1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2f1
	jal ra, csr_bad_impl
	li a1, 0x2f2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2f2
	jal ra, csr_bad_impl
	li a1, 0x2f3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2f3
	jal ra, csr_bad_impl
	li a1, 0x2f4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2f4
	jal ra, csr_bad_impl
	li a1, 0x2f5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2f5
	jal ra, csr_bad_impl
	li a1, 0x2f6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2f6
	jal ra, csr_bad_impl
	li a1, 0x2f7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2f7
	jal ra, csr_bad_impl
	li a1, 0x2f8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2f8
	jal ra, csr_bad_impl
	li a1, 0x2f9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2f9
	jal ra, csr_bad_impl
	li a1, 0x2fa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2fa
	jal ra, csr_bad_impl
	li a1, 0x2fb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2fb
	jal ra, csr_bad_impl
	li a1, 0x2fc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2fc
	jal ra, csr_bad_impl
	li a1, 0x2fd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2fd
	jal ra, csr_bad_impl
	li a1, 0x2fe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2fe
	jal ra, csr_bad_impl
	li a1, 0x2ff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x2ff
	jal ra, csr_bad_impl
	li a1, 0x302
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x302
	jal ra, csr_bad_impl
	li a1, 0x303
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x303
	jal ra, csr_bad_impl
	li a1, 0x307
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x307
	jal ra, csr_bad_impl
	li a1, 0x308
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x308
	jal ra, csr_bad_impl
	li a1, 0x309
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x309
	jal ra, csr_bad_impl
	li a1, 0x30b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x30b
	jal ra, csr_bad_impl
	li a1, 0x30c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x30c
	jal ra, csr_bad_impl
	li a1, 0x30d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x30d
	jal ra, csr_bad_impl
	li a1, 0x30e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x30e
	jal ra, csr_bad_impl
	li a1, 0x30f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x30f
	jal ra, csr_bad_impl
	li a1, 0x311
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x311
	jal ra, csr_bad_impl
	li a1, 0x312
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x312
	jal ra, csr_bad_impl
	li a1, 0x313
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x313
	jal ra, csr_bad_impl
	li a1, 0x314
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x314
	jal ra, csr_bad_impl
	li a1, 0x315
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x315
	jal ra, csr_bad_impl
	li a1, 0x316
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x316
	jal ra, csr_bad_impl
	li a1, 0x317
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x317
	jal ra, csr_bad_impl
	li a1, 0x318
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x318
	jal ra, csr_bad_impl
	li a1, 0x319
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x319
	jal ra, csr_bad_impl
	li a1, 0x31b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x31b
	jal ra, csr_bad_impl
	li a1, 0x31c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x31c
	jal ra, csr_bad_impl
	li a1, 0x31d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x31d
	jal ra, csr_bad_impl
	li a1, 0x31e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x31e
	jal ra, csr_bad_impl
	li a1, 0x31f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x31f
	jal ra, csr_bad_impl
	li a1, 0x321
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x321
	jal ra, csr_bad_impl
	li a1, 0x322
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x322
	jal ra, csr_bad_impl
	li a1, 0x32d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x32d
	jal ra, csr_bad_impl
	li a1, 0x32e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x32e
	jal ra, csr_bad_impl
	li a1, 0x32f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x32f
	jal ra, csr_bad_impl
	li a1, 0x330
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x330
	jal ra, csr_bad_impl
	li a1, 0x331
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x331
	jal ra, csr_bad_impl
	li a1, 0x332
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x332
	jal ra, csr_bad_impl
	li a1, 0x333
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x333
	jal ra, csr_bad_impl
	li a1, 0x334
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x334
	jal ra, csr_bad_impl
	li a1, 0x335
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x335
	jal ra, csr_bad_impl
	li a1, 0x336
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x336
	jal ra, csr_bad_impl
	li a1, 0x337
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x337
	jal ra, csr_bad_impl
	li a1, 0x338
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x338
	jal ra, csr_bad_impl
	li a1, 0x339
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x339
	jal ra, csr_bad_impl
	li a1, 0x33a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x33a
	jal ra, csr_bad_impl
	li a1, 0x33b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x33b
	jal ra, csr_bad_impl
	li a1, 0x33c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x33c
	jal ra, csr_bad_impl
	li a1, 0x33d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x33d
	jal ra, csr_bad_impl
	li a1, 0x33e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x33e
	jal ra, csr_bad_impl
	li a1, 0x33f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x33f
	jal ra, csr_bad_impl
	li a1, 0x345
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x345
	jal ra, csr_bad_impl
	li a1, 0x346
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x346
	jal ra, csr_bad_impl
	li a1, 0x347
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x347
	jal ra, csr_bad_impl
	li a1, 0x348
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x348
	jal ra, csr_bad_impl
	li a1, 0x349
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x349
	jal ra, csr_bad_impl
	li a1, 0x34a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x34a
	jal ra, csr_bad_impl
	li a1, 0x34b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x34b
	jal ra, csr_bad_impl
	li a1, 0x34c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x34c
	jal ra, csr_bad_impl
	li a1, 0x34d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x34d
	jal ra, csr_bad_impl
	li a1, 0x34e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x34e
	jal ra, csr_bad_impl
	li a1, 0x34f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x34f
	jal ra, csr_bad_impl
	li a1, 0x350
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x350
	jal ra, csr_bad_impl
	li a1, 0x351
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x351
	jal ra, csr_bad_impl
	li a1, 0x352
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x352
	jal ra, csr_bad_impl
	li a1, 0x353
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x353
	jal ra, csr_bad_impl
	li a1, 0x354
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x354
	jal ra, csr_bad_impl
	li a1, 0x355
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x355
	jal ra, csr_bad_impl
	li a1, 0x356
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x356
	jal ra, csr_bad_impl
	li a1, 0x357
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x357
	jal ra, csr_bad_impl
	li a1, 0x358
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x358
	jal ra, csr_bad_impl
	li a1, 0x359
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x359
	jal ra, csr_bad_impl
	li a1, 0x35a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x35a
	jal ra, csr_bad_impl
	li a1, 0x35b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x35b
	jal ra, csr_bad_impl
	li a1, 0x35c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x35c
	jal ra, csr_bad_impl
	li a1, 0x35d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x35d
	jal ra, csr_bad_impl
	li a1, 0x35e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x35e
	jal ra, csr_bad_impl
	li a1, 0x35f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x35f
	jal ra, csr_bad_impl
	li a1, 0x360
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x360
	jal ra, csr_bad_impl
	li a1, 0x361
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x361
	jal ra, csr_bad_impl
	li a1, 0x362
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x362
	jal ra, csr_bad_impl
	li a1, 0x363
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x363
	jal ra, csr_bad_impl
	li a1, 0x364
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x364
	jal ra, csr_bad_impl
	li a1, 0x365
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x365
	jal ra, csr_bad_impl
	li a1, 0x366
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x366
	jal ra, csr_bad_impl
	li a1, 0x367
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x367
	jal ra, csr_bad_impl
	li a1, 0x368
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x368
	jal ra, csr_bad_impl
	li a1, 0x369
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x369
	jal ra, csr_bad_impl
	li a1, 0x36a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x36a
	jal ra, csr_bad_impl
	li a1, 0x36b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x36b
	jal ra, csr_bad_impl
	li a1, 0x36c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x36c
	jal ra, csr_bad_impl
	li a1, 0x36d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x36d
	jal ra, csr_bad_impl
	li a1, 0x36e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x36e
	jal ra, csr_bad_impl
	li a1, 0x36f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x36f
	jal ra, csr_bad_impl
	li a1, 0x370
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x370
	jal ra, csr_bad_impl
	li a1, 0x371
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x371
	jal ra, csr_bad_impl
	li a1, 0x372
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x372
	jal ra, csr_bad_impl
	li a1, 0x373
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x373
	jal ra, csr_bad_impl
	li a1, 0x374
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x374
	jal ra, csr_bad_impl
	li a1, 0x375
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x375
	jal ra, csr_bad_impl
	li a1, 0x376
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x376
	jal ra, csr_bad_impl
	li a1, 0x377
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x377
	jal ra, csr_bad_impl
	li a1, 0x378
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x378
	jal ra, csr_bad_impl
	li a1, 0x379
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x379
	jal ra, csr_bad_impl
	li a1, 0x37a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x37a
	jal ra, csr_bad_impl
	li a1, 0x37b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x37b
	jal ra, csr_bad_impl
	li a1, 0x37c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x37c
	jal ra, csr_bad_impl
	li a1, 0x37d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x37d
	jal ra, csr_bad_impl
	li a1, 0x37e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x37e
	jal ra, csr_bad_impl
	li a1, 0x37f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x37f
	jal ra, csr_bad_impl
	li a1, 0x380
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x380
	jal ra, csr_bad_impl
	li a1, 0x381
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x381
	jal ra, csr_bad_impl
	li a1, 0x382
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x382
	jal ra, csr_bad_impl
	li a1, 0x383
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x383
	jal ra, csr_bad_impl
	li a1, 0x384
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x384
	jal ra, csr_bad_impl
	li a1, 0x385
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x385
	jal ra, csr_bad_impl
	li a1, 0x386
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x386
	jal ra, csr_bad_impl
	li a1, 0x387
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x387
	jal ra, csr_bad_impl
	li a1, 0x388
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x388
	jal ra, csr_bad_impl
	li a1, 0x389
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x389
	jal ra, csr_bad_impl
	li a1, 0x38a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x38a
	jal ra, csr_bad_impl
	li a1, 0x38b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x38b
	jal ra, csr_bad_impl
	li a1, 0x38c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x38c
	jal ra, csr_bad_impl
	li a1, 0x38d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x38d
	jal ra, csr_bad_impl
	li a1, 0x38e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x38e
	jal ra, csr_bad_impl
	li a1, 0x38f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x38f
	jal ra, csr_bad_impl
	li a1, 0x390
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x390
	jal ra, csr_bad_impl
	li a1, 0x391
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x391
	jal ra, csr_bad_impl
	li a1, 0x392
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x392
	jal ra, csr_bad_impl
	li a1, 0x393
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x393
	jal ra, csr_bad_impl
	li a1, 0x394
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x394
	jal ra, csr_bad_impl
	li a1, 0x395
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x395
	jal ra, csr_bad_impl
	li a1, 0x396
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x396
	jal ra, csr_bad_impl
	li a1, 0x397
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x397
	jal ra, csr_bad_impl
	li a1, 0x398
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x398
	jal ra, csr_bad_impl
	li a1, 0x399
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x399
	jal ra, csr_bad_impl
	li a1, 0x39a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x39a
	jal ra, csr_bad_impl
	li a1, 0x39b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x39b
	jal ra, csr_bad_impl
	li a1, 0x39c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x39c
	jal ra, csr_bad_impl
	li a1, 0x39d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x39d
	jal ra, csr_bad_impl
	li a1, 0x39e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x39e
	jal ra, csr_bad_impl
	li a1, 0x39f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x39f
	jal ra, csr_bad_impl
	li a1, 0x3a0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3a0
	jal ra, csr_bad_impl
	li a1, 0x3a1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3a1
	jal ra, csr_bad_impl
	li a1, 0x3a2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3a2
	jal ra, csr_bad_impl
	li a1, 0x3a3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3a3
	jal ra, csr_bad_impl
	li a1, 0x3a4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3a4
	jal ra, csr_bad_impl
	li a1, 0x3a5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3a5
	jal ra, csr_bad_impl
	li a1, 0x3a6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3a6
	jal ra, csr_bad_impl
	li a1, 0x3a7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3a7
	jal ra, csr_bad_impl
	li a1, 0x3a8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3a8
	jal ra, csr_bad_impl
	li a1, 0x3a9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3a9
	jal ra, csr_bad_impl
	li a1, 0x3aa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3aa
	jal ra, csr_bad_impl
	li a1, 0x3ab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ab
	jal ra, csr_bad_impl
	li a1, 0x3ac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ac
	jal ra, csr_bad_impl
	li a1, 0x3ad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ad
	jal ra, csr_bad_impl
	li a1, 0x3ae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ae
	jal ra, csr_bad_impl
	li a1, 0x3af
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3af
	jal ra, csr_bad_impl
	li a1, 0x3b0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3b0
	jal ra, csr_bad_impl
	li a1, 0x3b1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3b1
	jal ra, csr_bad_impl
	li a1, 0x3b2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3b2
	jal ra, csr_bad_impl
	li a1, 0x3b3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3b3
	jal ra, csr_bad_impl
	li a1, 0x3b4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3b4
	jal ra, csr_bad_impl
	li a1, 0x3b5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3b5
	jal ra, csr_bad_impl
	li a1, 0x3b6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3b6
	jal ra, csr_bad_impl
	li a1, 0x3b7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3b7
	jal ra, csr_bad_impl
	li a1, 0x3b8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3b8
	jal ra, csr_bad_impl
	li a1, 0x3b9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3b9
	jal ra, csr_bad_impl
	li a1, 0x3ba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ba
	jal ra, csr_bad_impl
	li a1, 0x3bb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3bb
	jal ra, csr_bad_impl
	li a1, 0x3bc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3bc
	jal ra, csr_bad_impl
	li a1, 0x3bd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3bd
	jal ra, csr_bad_impl
	li a1, 0x3be
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3be
	jal ra, csr_bad_impl
	li a1, 0x3bf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3bf
	jal ra, csr_bad_impl
	li a1, 0x3c0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3c0
	jal ra, csr_bad_impl
	li a1, 0x3c1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3c1
	jal ra, csr_bad_impl
	li a1, 0x3c2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3c2
	jal ra, csr_bad_impl
	li a1, 0x3c3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3c3
	jal ra, csr_bad_impl
	li a1, 0x3c4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3c4
	jal ra, csr_bad_impl
	li a1, 0x3c5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3c5
	jal ra, csr_bad_impl
	li a1, 0x3c6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3c6
	jal ra, csr_bad_impl
	li a1, 0x3c7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3c7
	jal ra, csr_bad_impl
	li a1, 0x3c8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3c8
	jal ra, csr_bad_impl
	li a1, 0x3c9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3c9
	jal ra, csr_bad_impl
	li a1, 0x3ca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ca
	jal ra, csr_bad_impl
	li a1, 0x3cb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3cb
	jal ra, csr_bad_impl
	li a1, 0x3cc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3cc
	jal ra, csr_bad_impl
	li a1, 0x3cd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3cd
	jal ra, csr_bad_impl
	li a1, 0x3ce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ce
	jal ra, csr_bad_impl
	li a1, 0x3cf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3cf
	jal ra, csr_bad_impl
	li a1, 0x3d0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3d0
	jal ra, csr_bad_impl
	li a1, 0x3d1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3d1
	jal ra, csr_bad_impl
	li a1, 0x3d2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3d2
	jal ra, csr_bad_impl
	li a1, 0x3d3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3d3
	jal ra, csr_bad_impl
	li a1, 0x3d4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3d4
	jal ra, csr_bad_impl
	li a1, 0x3d5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3d5
	jal ra, csr_bad_impl
	li a1, 0x3d6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3d6
	jal ra, csr_bad_impl
	li a1, 0x3d7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3d7
	jal ra, csr_bad_impl
	li a1, 0x3d8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3d8
	jal ra, csr_bad_impl
	li a1, 0x3d9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3d9
	jal ra, csr_bad_impl
	li a1, 0x3da
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3da
	jal ra, csr_bad_impl
	li a1, 0x3db
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3db
	jal ra, csr_bad_impl
	li a1, 0x3dc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3dc
	jal ra, csr_bad_impl
	li a1, 0x3dd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3dd
	jal ra, csr_bad_impl
	li a1, 0x3de
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3de
	jal ra, csr_bad_impl
	li a1, 0x3df
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3df
	jal ra, csr_bad_impl
	li a1, 0x3e0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3e0
	jal ra, csr_bad_impl
	li a1, 0x3e1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3e1
	jal ra, csr_bad_impl
	li a1, 0x3e2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3e2
	jal ra, csr_bad_impl
	li a1, 0x3e3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3e3
	jal ra, csr_bad_impl
	li a1, 0x3e4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3e4
	jal ra, csr_bad_impl
	li a1, 0x3e5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3e5
	jal ra, csr_bad_impl
	li a1, 0x3e6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3e6
	jal ra, csr_bad_impl
	li a1, 0x3e7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3e7
	jal ra, csr_bad_impl
	li a1, 0x3e8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3e8
	jal ra, csr_bad_impl
	li a1, 0x3e9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3e9
	jal ra, csr_bad_impl
	li a1, 0x3ea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ea
	jal ra, csr_bad_impl
	li a1, 0x3eb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3eb
	jal ra, csr_bad_impl
	li a1, 0x3ec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ec
	jal ra, csr_bad_impl
	li a1, 0x3ed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ed
	jal ra, csr_bad_impl
	li a1, 0x3ee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ee
	jal ra, csr_bad_impl
	li a1, 0x3ef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ef
	jal ra, csr_bad_impl
	li a1, 0x3f0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3f0
	jal ra, csr_bad_impl
	li a1, 0x3f1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3f1
	jal ra, csr_bad_impl
	li a1, 0x3f2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3f2
	jal ra, csr_bad_impl
	li a1, 0x3f3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3f3
	jal ra, csr_bad_impl
	li a1, 0x3f4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3f4
	jal ra, csr_bad_impl
	li a1, 0x3f5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3f5
	jal ra, csr_bad_impl
	li a1, 0x3f6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3f6
	jal ra, csr_bad_impl
	li a1, 0x3f7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3f7
	jal ra, csr_bad_impl
	li a1, 0x3f8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3f8
	jal ra, csr_bad_impl
	li a1, 0x3f9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3f9
	jal ra, csr_bad_impl
	li a1, 0x3fa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3fa
	jal ra, csr_bad_impl
	li a1, 0x3fb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3fb
	jal ra, csr_bad_impl
	li a1, 0x3fc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3fc
	jal ra, csr_bad_impl
	li a1, 0x3fd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3fd
	jal ra, csr_bad_impl
	li a1, 0x3fe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3fe
	jal ra, csr_bad_impl
	li a1, 0x3ff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x3ff
	jal ra, csr_bad_impl
	li a1, 0x400
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x400
	jal ra, csr_bad_impl
	li a1, 0x401
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x401
	jal ra, csr_bad_impl
	li a1, 0x402
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x402
	jal ra, csr_bad_impl
	li a1, 0x403
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x403
	jal ra, csr_bad_impl
	li a1, 0x404
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x404
	jal ra, csr_bad_impl
	li a1, 0x405
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x405
	jal ra, csr_bad_impl
	li a1, 0x406
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x406
	jal ra, csr_bad_impl
	li a1, 0x407
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x407
	jal ra, csr_bad_impl
	li a1, 0x408
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x408
	jal ra, csr_bad_impl
	li a1, 0x409
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x409
	jal ra, csr_bad_impl
	li a1, 0x40a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x40a
	jal ra, csr_bad_impl
	li a1, 0x40b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x40b
	jal ra, csr_bad_impl
	li a1, 0x40c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x40c
	jal ra, csr_bad_impl
	li a1, 0x40d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x40d
	jal ra, csr_bad_impl
	li a1, 0x40e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x40e
	jal ra, csr_bad_impl
	li a1, 0x40f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x40f
	jal ra, csr_bad_impl
	li a1, 0x410
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x410
	jal ra, csr_bad_impl
	li a1, 0x411
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x411
	jal ra, csr_bad_impl
	li a1, 0x412
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x412
	jal ra, csr_bad_impl
	li a1, 0x413
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x413
	jal ra, csr_bad_impl
	li a1, 0x414
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x414
	jal ra, csr_bad_impl
	li a1, 0x415
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x415
	jal ra, csr_bad_impl
	li a1, 0x416
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x416
	jal ra, csr_bad_impl
	li a1, 0x417
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x417
	jal ra, csr_bad_impl
	li a1, 0x418
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x418
	jal ra, csr_bad_impl
	li a1, 0x419
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x419
	jal ra, csr_bad_impl
	li a1, 0x41a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x41a
	jal ra, csr_bad_impl
	li a1, 0x41b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x41b
	jal ra, csr_bad_impl
	li a1, 0x41c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x41c
	jal ra, csr_bad_impl
	li a1, 0x41d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x41d
	jal ra, csr_bad_impl
	li a1, 0x41e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x41e
	jal ra, csr_bad_impl
	li a1, 0x41f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x41f
	jal ra, csr_bad_impl
	li a1, 0x420
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x420
	jal ra, csr_bad_impl
	li a1, 0x421
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x421
	jal ra, csr_bad_impl
	li a1, 0x422
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x422
	jal ra, csr_bad_impl
	li a1, 0x423
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x423
	jal ra, csr_bad_impl
	li a1, 0x424
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x424
	jal ra, csr_bad_impl
	li a1, 0x425
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x425
	jal ra, csr_bad_impl
	li a1, 0x426
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x426
	jal ra, csr_bad_impl
	li a1, 0x427
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x427
	jal ra, csr_bad_impl
	li a1, 0x428
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x428
	jal ra, csr_bad_impl
	li a1, 0x429
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x429
	jal ra, csr_bad_impl
	li a1, 0x42a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x42a
	jal ra, csr_bad_impl
	li a1, 0x42b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x42b
	jal ra, csr_bad_impl
	li a1, 0x42c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x42c
	jal ra, csr_bad_impl
	li a1, 0x42d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x42d
	jal ra, csr_bad_impl
	li a1, 0x42e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x42e
	jal ra, csr_bad_impl
	li a1, 0x42f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x42f
	jal ra, csr_bad_impl
	li a1, 0x430
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x430
	jal ra, csr_bad_impl
	li a1, 0x431
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x431
	jal ra, csr_bad_impl
	li a1, 0x432
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x432
	jal ra, csr_bad_impl
	li a1, 0x433
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x433
	jal ra, csr_bad_impl
	li a1, 0x434
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x434
	jal ra, csr_bad_impl
	li a1, 0x435
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x435
	jal ra, csr_bad_impl
	li a1, 0x436
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x436
	jal ra, csr_bad_impl
	li a1, 0x437
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x437
	jal ra, csr_bad_impl
	li a1, 0x438
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x438
	jal ra, csr_bad_impl
	li a1, 0x439
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x439
	jal ra, csr_bad_impl
	li a1, 0x43a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x43a
	jal ra, csr_bad_impl
	li a1, 0x43b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x43b
	jal ra, csr_bad_impl
	li a1, 0x43c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x43c
	jal ra, csr_bad_impl
	li a1, 0x43d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x43d
	jal ra, csr_bad_impl
	li a1, 0x43e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x43e
	jal ra, csr_bad_impl
	li a1, 0x43f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x43f
	jal ra, csr_bad_impl
	li a1, 0x440
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x440
	jal ra, csr_bad_impl
	li a1, 0x441
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x441
	jal ra, csr_bad_impl
	li a1, 0x442
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x442
	jal ra, csr_bad_impl
	li a1, 0x443
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x443
	jal ra, csr_bad_impl
	li a1, 0x444
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x444
	jal ra, csr_bad_impl
	li a1, 0x445
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x445
	jal ra, csr_bad_impl
	li a1, 0x446
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x446
	jal ra, csr_bad_impl
	li a1, 0x447
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x447
	jal ra, csr_bad_impl
	li a1, 0x448
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x448
	jal ra, csr_bad_impl
	li a1, 0x449
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x449
	jal ra, csr_bad_impl
	li a1, 0x44a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x44a
	jal ra, csr_bad_impl
	li a1, 0x44b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x44b
	jal ra, csr_bad_impl
	li a1, 0x44c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x44c
	jal ra, csr_bad_impl
	li a1, 0x44d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x44d
	jal ra, csr_bad_impl
	li a1, 0x44e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x44e
	jal ra, csr_bad_impl
	li a1, 0x44f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x44f
	jal ra, csr_bad_impl
	li a1, 0x450
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x450
	jal ra, csr_bad_impl
	li a1, 0x451
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x451
	jal ra, csr_bad_impl
	li a1, 0x452
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x452
	jal ra, csr_bad_impl
	li a1, 0x453
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x453
	jal ra, csr_bad_impl
	li a1, 0x454
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x454
	jal ra, csr_bad_impl
	li a1, 0x455
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x455
	jal ra, csr_bad_impl
	li a1, 0x456
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x456
	jal ra, csr_bad_impl
	li a1, 0x457
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x457
	jal ra, csr_bad_impl
	li a1, 0x458
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x458
	jal ra, csr_bad_impl
	li a1, 0x459
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x459
	jal ra, csr_bad_impl
	li a1, 0x45a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x45a
	jal ra, csr_bad_impl
	li a1, 0x45b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x45b
	jal ra, csr_bad_impl
	li a1, 0x45c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x45c
	jal ra, csr_bad_impl
	li a1, 0x45d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x45d
	jal ra, csr_bad_impl
	li a1, 0x45e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x45e
	jal ra, csr_bad_impl
	li a1, 0x45f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x45f
	jal ra, csr_bad_impl
	li a1, 0x460
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x460
	jal ra, csr_bad_impl
	li a1, 0x461
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x461
	jal ra, csr_bad_impl
	li a1, 0x462
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x462
	jal ra, csr_bad_impl
	li a1, 0x463
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x463
	jal ra, csr_bad_impl
	li a1, 0x464
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x464
	jal ra, csr_bad_impl
	li a1, 0x465
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x465
	jal ra, csr_bad_impl
	li a1, 0x466
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x466
	jal ra, csr_bad_impl
	li a1, 0x467
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x467
	jal ra, csr_bad_impl
	li a1, 0x468
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x468
	jal ra, csr_bad_impl
	li a1, 0x469
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x469
	jal ra, csr_bad_impl
	li a1, 0x46a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x46a
	jal ra, csr_bad_impl
	li a1, 0x46b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x46b
	jal ra, csr_bad_impl
	li a1, 0x46c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x46c
	jal ra, csr_bad_impl
	li a1, 0x46d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x46d
	jal ra, csr_bad_impl
	li a1, 0x46e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x46e
	jal ra, csr_bad_impl
	li a1, 0x46f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x46f
	jal ra, csr_bad_impl
	li a1, 0x470
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x470
	jal ra, csr_bad_impl
	li a1, 0x471
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x471
	jal ra, csr_bad_impl
	li a1, 0x472
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x472
	jal ra, csr_bad_impl
	li a1, 0x473
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x473
	jal ra, csr_bad_impl
	li a1, 0x474
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x474
	jal ra, csr_bad_impl
	li a1, 0x475
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x475
	jal ra, csr_bad_impl
	li a1, 0x476
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x476
	jal ra, csr_bad_impl
	li a1, 0x477
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x477
	jal ra, csr_bad_impl
	li a1, 0x478
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x478
	jal ra, csr_bad_impl
	li a1, 0x479
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x479
	jal ra, csr_bad_impl
	li a1, 0x47a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x47a
	jal ra, csr_bad_impl
	li a1, 0x47b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x47b
	jal ra, csr_bad_impl
	li a1, 0x47c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x47c
	jal ra, csr_bad_impl
	li a1, 0x47d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x47d
	jal ra, csr_bad_impl
	li a1, 0x47e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x47e
	jal ra, csr_bad_impl
	li a1, 0x47f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x47f
	jal ra, csr_bad_impl
	li a1, 0x480
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x480
	jal ra, csr_bad_impl
	li a1, 0x481
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x481
	jal ra, csr_bad_impl
	li a1, 0x482
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x482
	jal ra, csr_bad_impl
	li a1, 0x483
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x483
	jal ra, csr_bad_impl
	li a1, 0x484
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x484
	jal ra, csr_bad_impl
	li a1, 0x485
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x485
	jal ra, csr_bad_impl
	li a1, 0x486
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x486
	jal ra, csr_bad_impl
	li a1, 0x487
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x487
	jal ra, csr_bad_impl
	li a1, 0x488
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x488
	jal ra, csr_bad_impl
	li a1, 0x489
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x489
	jal ra, csr_bad_impl
	li a1, 0x48a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x48a
	jal ra, csr_bad_impl
	li a1, 0x48b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x48b
	jal ra, csr_bad_impl
	li a1, 0x48c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x48c
	jal ra, csr_bad_impl
	li a1, 0x48d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x48d
	jal ra, csr_bad_impl
	li a1, 0x48e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x48e
	jal ra, csr_bad_impl
	li a1, 0x48f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x48f
	jal ra, csr_bad_impl
	li a1, 0x490
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x490
	jal ra, csr_bad_impl
	li a1, 0x491
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x491
	jal ra, csr_bad_impl
	li a1, 0x492
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x492
	jal ra, csr_bad_impl
	li a1, 0x493
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x493
	jal ra, csr_bad_impl
	li a1, 0x494
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x494
	jal ra, csr_bad_impl
	li a1, 0x495
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x495
	jal ra, csr_bad_impl
	li a1, 0x496
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x496
	jal ra, csr_bad_impl
	li a1, 0x497
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x497
	jal ra, csr_bad_impl
	li a1, 0x498
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x498
	jal ra, csr_bad_impl
	li a1, 0x499
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x499
	jal ra, csr_bad_impl
	li a1, 0x49a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x49a
	jal ra, csr_bad_impl
	li a1, 0x49b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x49b
	jal ra, csr_bad_impl
	li a1, 0x49c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x49c
	jal ra, csr_bad_impl
	li a1, 0x49d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x49d
	jal ra, csr_bad_impl
	li a1, 0x49e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x49e
	jal ra, csr_bad_impl
	li a1, 0x49f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x49f
	jal ra, csr_bad_impl
	li a1, 0x4a0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4a0
	jal ra, csr_bad_impl
	li a1, 0x4a1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4a1
	jal ra, csr_bad_impl
	li a1, 0x4a2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4a2
	jal ra, csr_bad_impl
	li a1, 0x4a3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4a3
	jal ra, csr_bad_impl
	li a1, 0x4a4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4a4
	jal ra, csr_bad_impl
	li a1, 0x4a5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4a5
	jal ra, csr_bad_impl
	li a1, 0x4a6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4a6
	jal ra, csr_bad_impl
	li a1, 0x4a7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4a7
	jal ra, csr_bad_impl
	li a1, 0x4a8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4a8
	jal ra, csr_bad_impl
	li a1, 0x4a9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4a9
	jal ra, csr_bad_impl
	li a1, 0x4aa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4aa
	jal ra, csr_bad_impl
	li a1, 0x4ab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ab
	jal ra, csr_bad_impl
	li a1, 0x4ac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ac
	jal ra, csr_bad_impl
	li a1, 0x4ad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ad
	jal ra, csr_bad_impl
	li a1, 0x4ae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ae
	jal ra, csr_bad_impl
	li a1, 0x4af
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4af
	jal ra, csr_bad_impl
	li a1, 0x4b0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4b0
	jal ra, csr_bad_impl
	li a1, 0x4b1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4b1
	jal ra, csr_bad_impl
	li a1, 0x4b2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4b2
	jal ra, csr_bad_impl
	li a1, 0x4b3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4b3
	jal ra, csr_bad_impl
	li a1, 0x4b4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4b4
	jal ra, csr_bad_impl
	li a1, 0x4b5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4b5
	jal ra, csr_bad_impl
	li a1, 0x4b6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4b6
	jal ra, csr_bad_impl
	li a1, 0x4b7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4b7
	jal ra, csr_bad_impl
	li a1, 0x4b8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4b8
	jal ra, csr_bad_impl
	li a1, 0x4b9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4b9
	jal ra, csr_bad_impl
	li a1, 0x4ba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ba
	jal ra, csr_bad_impl
	li a1, 0x4bb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4bb
	jal ra, csr_bad_impl
	li a1, 0x4bc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4bc
	jal ra, csr_bad_impl
	li a1, 0x4bd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4bd
	jal ra, csr_bad_impl
	li a1, 0x4be
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4be
	jal ra, csr_bad_impl
	li a1, 0x4bf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4bf
	jal ra, csr_bad_impl
	li a1, 0x4c0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4c0
	jal ra, csr_bad_impl
	li a1, 0x4c1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4c1
	jal ra, csr_bad_impl
	li a1, 0x4c2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4c2
	jal ra, csr_bad_impl
	li a1, 0x4c3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4c3
	jal ra, csr_bad_impl
	li a1, 0x4c4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4c4
	jal ra, csr_bad_impl
	li a1, 0x4c5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4c5
	jal ra, csr_bad_impl
	li a1, 0x4c6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4c6
	jal ra, csr_bad_impl
	li a1, 0x4c7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4c7
	jal ra, csr_bad_impl
	li a1, 0x4c8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4c8
	jal ra, csr_bad_impl
	li a1, 0x4c9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4c9
	jal ra, csr_bad_impl
	li a1, 0x4ca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ca
	jal ra, csr_bad_impl
	li a1, 0x4cb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4cb
	jal ra, csr_bad_impl
	li a1, 0x4cc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4cc
	jal ra, csr_bad_impl
	li a1, 0x4cd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4cd
	jal ra, csr_bad_impl
	li a1, 0x4ce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ce
	jal ra, csr_bad_impl
	li a1, 0x4cf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4cf
	jal ra, csr_bad_impl
	li a1, 0x4d0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4d0
	jal ra, csr_bad_impl
	li a1, 0x4d1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4d1
	jal ra, csr_bad_impl
	li a1, 0x4d2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4d2
	jal ra, csr_bad_impl
	li a1, 0x4d3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4d3
	jal ra, csr_bad_impl
	li a1, 0x4d4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4d4
	jal ra, csr_bad_impl
	li a1, 0x4d5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4d5
	jal ra, csr_bad_impl
	li a1, 0x4d6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4d6
	jal ra, csr_bad_impl
	li a1, 0x4d7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4d7
	jal ra, csr_bad_impl
	li a1, 0x4d8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4d8
	jal ra, csr_bad_impl
	li a1, 0x4d9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4d9
	jal ra, csr_bad_impl
	li a1, 0x4da
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4da
	jal ra, csr_bad_impl
	li a1, 0x4db
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4db
	jal ra, csr_bad_impl
	li a1, 0x4dc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4dc
	jal ra, csr_bad_impl
	li a1, 0x4dd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4dd
	jal ra, csr_bad_impl
	li a1, 0x4de
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4de
	jal ra, csr_bad_impl
	li a1, 0x4df
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4df
	jal ra, csr_bad_impl
	li a1, 0x4e0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4e0
	jal ra, csr_bad_impl
	li a1, 0x4e1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4e1
	jal ra, csr_bad_impl
	li a1, 0x4e2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4e2
	jal ra, csr_bad_impl
	li a1, 0x4e3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4e3
	jal ra, csr_bad_impl
	li a1, 0x4e4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4e4
	jal ra, csr_bad_impl
	li a1, 0x4e5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4e5
	jal ra, csr_bad_impl
	li a1, 0x4e6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4e6
	jal ra, csr_bad_impl
	li a1, 0x4e7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4e7
	jal ra, csr_bad_impl
	li a1, 0x4e8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4e8
	jal ra, csr_bad_impl
	li a1, 0x4e9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4e9
	jal ra, csr_bad_impl
	li a1, 0x4ea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ea
	jal ra, csr_bad_impl
	li a1, 0x4eb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4eb
	jal ra, csr_bad_impl
	li a1, 0x4ec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ec
	jal ra, csr_bad_impl
	li a1, 0x4ed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ed
	jal ra, csr_bad_impl
	li a1, 0x4ee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ee
	jal ra, csr_bad_impl
	li a1, 0x4ef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ef
	jal ra, csr_bad_impl
	li a1, 0x4f0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4f0
	jal ra, csr_bad_impl
	li a1, 0x4f1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4f1
	jal ra, csr_bad_impl
	li a1, 0x4f2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4f2
	jal ra, csr_bad_impl
	li a1, 0x4f3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4f3
	jal ra, csr_bad_impl
	li a1, 0x4f4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4f4
	jal ra, csr_bad_impl
	li a1, 0x4f5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4f5
	jal ra, csr_bad_impl
	li a1, 0x4f6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4f6
	jal ra, csr_bad_impl
	li a1, 0x4f7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4f7
	jal ra, csr_bad_impl
	li a1, 0x4f8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4f8
	jal ra, csr_bad_impl
	li a1, 0x4f9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4f9
	jal ra, csr_bad_impl
	li a1, 0x4fa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4fa
	jal ra, csr_bad_impl
	li a1, 0x4fb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4fb
	jal ra, csr_bad_impl
	li a1, 0x4fc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4fc
	jal ra, csr_bad_impl
	li a1, 0x4fd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4fd
	jal ra, csr_bad_impl
	li a1, 0x4fe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4fe
	jal ra, csr_bad_impl
	li a1, 0x4ff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x4ff
	jal ra, csr_bad_impl
	li a1, 0x500
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x500
	jal ra, csr_bad_impl
	li a1, 0x501
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x501
	jal ra, csr_bad_impl
	li a1, 0x502
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x502
	jal ra, csr_bad_impl
	li a1, 0x503
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x503
	jal ra, csr_bad_impl
	li a1, 0x504
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x504
	jal ra, csr_bad_impl
	li a1, 0x505
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x505
	jal ra, csr_bad_impl
	li a1, 0x506
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x506
	jal ra, csr_bad_impl
	li a1, 0x507
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x507
	jal ra, csr_bad_impl
	li a1, 0x508
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x508
	jal ra, csr_bad_impl
	li a1, 0x509
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x509
	jal ra, csr_bad_impl
	li a1, 0x50a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x50a
	jal ra, csr_bad_impl
	li a1, 0x50b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x50b
	jal ra, csr_bad_impl
	li a1, 0x50c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x50c
	jal ra, csr_bad_impl
	li a1, 0x50d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x50d
	jal ra, csr_bad_impl
	li a1, 0x50e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x50e
	jal ra, csr_bad_impl
	li a1, 0x50f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x50f
	jal ra, csr_bad_impl
	li a1, 0x510
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x510
	jal ra, csr_bad_impl
	li a1, 0x511
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x511
	jal ra, csr_bad_impl
	li a1, 0x512
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x512
	jal ra, csr_bad_impl
	li a1, 0x513
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x513
	jal ra, csr_bad_impl
	li a1, 0x514
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x514
	jal ra, csr_bad_impl
	li a1, 0x515
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x515
	jal ra, csr_bad_impl
	li a1, 0x516
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x516
	jal ra, csr_bad_impl
	li a1, 0x517
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x517
	jal ra, csr_bad_impl
	li a1, 0x518
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x518
	jal ra, csr_bad_impl
	li a1, 0x519
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x519
	jal ra, csr_bad_impl
	li a1, 0x51a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x51a
	jal ra, csr_bad_impl
	li a1, 0x51b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x51b
	jal ra, csr_bad_impl
	li a1, 0x51c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x51c
	jal ra, csr_bad_impl
	li a1, 0x51d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x51d
	jal ra, csr_bad_impl
	li a1, 0x51e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x51e
	jal ra, csr_bad_impl
	li a1, 0x51f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x51f
	jal ra, csr_bad_impl
	li a1, 0x520
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x520
	jal ra, csr_bad_impl
	li a1, 0x521
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x521
	jal ra, csr_bad_impl
	li a1, 0x522
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x522
	jal ra, csr_bad_impl
	li a1, 0x523
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x523
	jal ra, csr_bad_impl
	li a1, 0x524
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x524
	jal ra, csr_bad_impl
	li a1, 0x525
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x525
	jal ra, csr_bad_impl
	li a1, 0x526
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x526
	jal ra, csr_bad_impl
	li a1, 0x527
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x527
	jal ra, csr_bad_impl
	li a1, 0x528
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x528
	jal ra, csr_bad_impl
	li a1, 0x529
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x529
	jal ra, csr_bad_impl
	li a1, 0x52a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x52a
	jal ra, csr_bad_impl
	li a1, 0x52b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x52b
	jal ra, csr_bad_impl
	li a1, 0x52c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x52c
	jal ra, csr_bad_impl
	li a1, 0x52d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x52d
	jal ra, csr_bad_impl
	li a1, 0x52e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x52e
	jal ra, csr_bad_impl
	li a1, 0x52f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x52f
	jal ra, csr_bad_impl
	li a1, 0x530
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x530
	jal ra, csr_bad_impl
	li a1, 0x531
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x531
	jal ra, csr_bad_impl
	li a1, 0x532
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x532
	jal ra, csr_bad_impl
	li a1, 0x533
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x533
	jal ra, csr_bad_impl
	li a1, 0x534
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x534
	jal ra, csr_bad_impl
	li a1, 0x535
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x535
	jal ra, csr_bad_impl
	li a1, 0x536
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x536
	jal ra, csr_bad_impl
	li a1, 0x537
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x537
	jal ra, csr_bad_impl
	li a1, 0x538
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x538
	jal ra, csr_bad_impl
	li a1, 0x539
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x539
	jal ra, csr_bad_impl
	li a1, 0x53a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x53a
	jal ra, csr_bad_impl
	li a1, 0x53b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x53b
	jal ra, csr_bad_impl
	li a1, 0x53c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x53c
	jal ra, csr_bad_impl
	li a1, 0x53d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x53d
	jal ra, csr_bad_impl
	li a1, 0x53e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x53e
	jal ra, csr_bad_impl
	li a1, 0x53f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x53f
	jal ra, csr_bad_impl
	li a1, 0x540
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x540
	jal ra, csr_bad_impl
	li a1, 0x541
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x541
	jal ra, csr_bad_impl
	li a1, 0x542
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x542
	jal ra, csr_bad_impl
	li a1, 0x543
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x543
	jal ra, csr_bad_impl
	li a1, 0x544
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x544
	jal ra, csr_bad_impl
	li a1, 0x545
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x545
	jal ra, csr_bad_impl
	li a1, 0x546
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x546
	jal ra, csr_bad_impl
	li a1, 0x547
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x547
	jal ra, csr_bad_impl
	li a1, 0x548
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x548
	jal ra, csr_bad_impl
	li a1, 0x549
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x549
	jal ra, csr_bad_impl
	li a1, 0x54a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x54a
	jal ra, csr_bad_impl
	li a1, 0x54b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x54b
	jal ra, csr_bad_impl
	li a1, 0x54c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x54c
	jal ra, csr_bad_impl
	li a1, 0x54d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x54d
	jal ra, csr_bad_impl
	li a1, 0x54e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x54e
	jal ra, csr_bad_impl
	li a1, 0x54f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x54f
	jal ra, csr_bad_impl
	li a1, 0x550
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x550
	jal ra, csr_bad_impl
	li a1, 0x551
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x551
	jal ra, csr_bad_impl
	li a1, 0x552
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x552
	jal ra, csr_bad_impl
	li a1, 0x553
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x553
	jal ra, csr_bad_impl
	li a1, 0x554
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x554
	jal ra, csr_bad_impl
	li a1, 0x555
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x555
	jal ra, csr_bad_impl
	li a1, 0x556
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x556
	jal ra, csr_bad_impl
	li a1, 0x557
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x557
	jal ra, csr_bad_impl
	li a1, 0x558
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x558
	jal ra, csr_bad_impl
	li a1, 0x559
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x559
	jal ra, csr_bad_impl
	li a1, 0x55a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x55a
	jal ra, csr_bad_impl
	li a1, 0x55b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x55b
	jal ra, csr_bad_impl
	li a1, 0x55c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x55c
	jal ra, csr_bad_impl
	li a1, 0x55d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x55d
	jal ra, csr_bad_impl
	li a1, 0x55e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x55e
	jal ra, csr_bad_impl
	li a1, 0x55f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x55f
	jal ra, csr_bad_impl
	li a1, 0x560
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x560
	jal ra, csr_bad_impl
	li a1, 0x561
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x561
	jal ra, csr_bad_impl
	li a1, 0x562
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x562
	jal ra, csr_bad_impl
	li a1, 0x563
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x563
	jal ra, csr_bad_impl
	li a1, 0x564
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x564
	jal ra, csr_bad_impl
	li a1, 0x565
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x565
	jal ra, csr_bad_impl
	li a1, 0x566
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x566
	jal ra, csr_bad_impl
	li a1, 0x567
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x567
	jal ra, csr_bad_impl
	li a1, 0x568
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x568
	jal ra, csr_bad_impl
	li a1, 0x569
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x569
	jal ra, csr_bad_impl
	li a1, 0x56a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x56a
	jal ra, csr_bad_impl
	li a1, 0x56b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x56b
	jal ra, csr_bad_impl
	li a1, 0x56c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x56c
	jal ra, csr_bad_impl
	li a1, 0x56d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x56d
	jal ra, csr_bad_impl
	li a1, 0x56e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x56e
	jal ra, csr_bad_impl
	li a1, 0x56f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x56f
	jal ra, csr_bad_impl
	li a1, 0x570
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x570
	jal ra, csr_bad_impl
	li a1, 0x571
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x571
	jal ra, csr_bad_impl
	li a1, 0x572
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x572
	jal ra, csr_bad_impl
	li a1, 0x573
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x573
	jal ra, csr_bad_impl
	li a1, 0x574
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x574
	jal ra, csr_bad_impl
	li a1, 0x575
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x575
	jal ra, csr_bad_impl
	li a1, 0x576
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x576
	jal ra, csr_bad_impl
	li a1, 0x577
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x577
	jal ra, csr_bad_impl
	li a1, 0x578
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x578
	jal ra, csr_bad_impl
	li a1, 0x579
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x579
	jal ra, csr_bad_impl
	li a1, 0x57a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x57a
	jal ra, csr_bad_impl
	li a1, 0x57b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x57b
	jal ra, csr_bad_impl
	li a1, 0x57c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x57c
	jal ra, csr_bad_impl
	li a1, 0x57d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x57d
	jal ra, csr_bad_impl
	li a1, 0x57e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x57e
	jal ra, csr_bad_impl
	li a1, 0x57f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x57f
	jal ra, csr_bad_impl
	li a1, 0x580
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x580
	jal ra, csr_bad_impl
	li a1, 0x581
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x581
	jal ra, csr_bad_impl
	li a1, 0x582
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x582
	jal ra, csr_bad_impl
	li a1, 0x583
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x583
	jal ra, csr_bad_impl
	li a1, 0x584
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x584
	jal ra, csr_bad_impl
	li a1, 0x585
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x585
	jal ra, csr_bad_impl
	li a1, 0x586
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x586
	jal ra, csr_bad_impl
	li a1, 0x587
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x587
	jal ra, csr_bad_impl
	li a1, 0x588
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x588
	jal ra, csr_bad_impl
	li a1, 0x589
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x589
	jal ra, csr_bad_impl
	li a1, 0x58a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x58a
	jal ra, csr_bad_impl
	li a1, 0x58b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x58b
	jal ra, csr_bad_impl
	li a1, 0x58c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x58c
	jal ra, csr_bad_impl
	li a1, 0x58d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x58d
	jal ra, csr_bad_impl
	li a1, 0x58e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x58e
	jal ra, csr_bad_impl
	li a1, 0x58f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x58f
	jal ra, csr_bad_impl
	li a1, 0x590
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x590
	jal ra, csr_bad_impl
	li a1, 0x591
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x591
	jal ra, csr_bad_impl
	li a1, 0x592
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x592
	jal ra, csr_bad_impl
	li a1, 0x593
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x593
	jal ra, csr_bad_impl
	li a1, 0x594
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x594
	jal ra, csr_bad_impl
	li a1, 0x595
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x595
	jal ra, csr_bad_impl
	li a1, 0x596
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x596
	jal ra, csr_bad_impl
	li a1, 0x597
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x597
	jal ra, csr_bad_impl
	li a1, 0x598
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x598
	jal ra, csr_bad_impl
	li a1, 0x599
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x599
	jal ra, csr_bad_impl
	li a1, 0x59a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x59a
	jal ra, csr_bad_impl
	li a1, 0x59b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x59b
	jal ra, csr_bad_impl
	li a1, 0x59c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x59c
	jal ra, csr_bad_impl
	li a1, 0x59d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x59d
	jal ra, csr_bad_impl
	li a1, 0x59e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x59e
	jal ra, csr_bad_impl
	li a1, 0x59f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x59f
	jal ra, csr_bad_impl
	li a1, 0x5a0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5a0
	jal ra, csr_bad_impl
	li a1, 0x5a1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5a1
	jal ra, csr_bad_impl
	li a1, 0x5a2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5a2
	jal ra, csr_bad_impl
	li a1, 0x5a3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5a3
	jal ra, csr_bad_impl
	li a1, 0x5a4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5a4
	jal ra, csr_bad_impl
	li a1, 0x5a5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5a5
	jal ra, csr_bad_impl
	li a1, 0x5a6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5a6
	jal ra, csr_bad_impl
	li a1, 0x5a7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5a7
	jal ra, csr_bad_impl
	li a1, 0x5a8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5a8
	jal ra, csr_bad_impl
	li a1, 0x5a9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5a9
	jal ra, csr_bad_impl
	li a1, 0x5aa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5aa
	jal ra, csr_bad_impl
	li a1, 0x5ab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ab
	jal ra, csr_bad_impl
	li a1, 0x5ac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ac
	jal ra, csr_bad_impl
	li a1, 0x5ad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ad
	jal ra, csr_bad_impl
	li a1, 0x5ae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ae
	jal ra, csr_bad_impl
	li a1, 0x5af
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5af
	jal ra, csr_bad_impl
	li a1, 0x5b0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5b0
	jal ra, csr_bad_impl
	li a1, 0x5b1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5b1
	jal ra, csr_bad_impl
	li a1, 0x5b2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5b2
	jal ra, csr_bad_impl
	li a1, 0x5b3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5b3
	jal ra, csr_bad_impl
	li a1, 0x5b4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5b4
	jal ra, csr_bad_impl
	li a1, 0x5b5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5b5
	jal ra, csr_bad_impl
	li a1, 0x5b6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5b6
	jal ra, csr_bad_impl
	li a1, 0x5b7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5b7
	jal ra, csr_bad_impl
	li a1, 0x5b8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5b8
	jal ra, csr_bad_impl
	li a1, 0x5b9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5b9
	jal ra, csr_bad_impl
	li a1, 0x5ba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ba
	jal ra, csr_bad_impl
	li a1, 0x5bb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5bb
	jal ra, csr_bad_impl
	li a1, 0x5bc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5bc
	jal ra, csr_bad_impl
	li a1, 0x5bd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5bd
	jal ra, csr_bad_impl
	li a1, 0x5be
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5be
	jal ra, csr_bad_impl
	li a1, 0x5bf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5bf
	jal ra, csr_bad_impl
	li a1, 0x5c0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5c0
	jal ra, csr_bad_impl
	li a1, 0x5c1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5c1
	jal ra, csr_bad_impl
	li a1, 0x5c2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5c2
	jal ra, csr_bad_impl
	li a1, 0x5c3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5c3
	jal ra, csr_bad_impl
	li a1, 0x5c4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5c4
	jal ra, csr_bad_impl
	li a1, 0x5c5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5c5
	jal ra, csr_bad_impl
	li a1, 0x5c6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5c6
	jal ra, csr_bad_impl
	li a1, 0x5c7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5c7
	jal ra, csr_bad_impl
	li a1, 0x5c8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5c8
	jal ra, csr_bad_impl
	li a1, 0x5c9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5c9
	jal ra, csr_bad_impl
	li a1, 0x5ca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ca
	jal ra, csr_bad_impl
	li a1, 0x5cb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5cb
	jal ra, csr_bad_impl
	li a1, 0x5cc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5cc
	jal ra, csr_bad_impl
	li a1, 0x5cd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5cd
	jal ra, csr_bad_impl
	li a1, 0x5ce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ce
	jal ra, csr_bad_impl
	li a1, 0x5cf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5cf
	jal ra, csr_bad_impl
	li a1, 0x5d0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5d0
	jal ra, csr_bad_impl
	li a1, 0x5d1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5d1
	jal ra, csr_bad_impl
	li a1, 0x5d2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5d2
	jal ra, csr_bad_impl
	li a1, 0x5d3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5d3
	jal ra, csr_bad_impl
	li a1, 0x5d4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5d4
	jal ra, csr_bad_impl
	li a1, 0x5d5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5d5
	jal ra, csr_bad_impl
	li a1, 0x5d6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5d6
	jal ra, csr_bad_impl
	li a1, 0x5d7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5d7
	jal ra, csr_bad_impl
	li a1, 0x5d8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5d8
	jal ra, csr_bad_impl
	li a1, 0x5d9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5d9
	jal ra, csr_bad_impl
	li a1, 0x5da
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5da
	jal ra, csr_bad_impl
	li a1, 0x5db
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5db
	jal ra, csr_bad_impl
	li a1, 0x5dc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5dc
	jal ra, csr_bad_impl
	li a1, 0x5dd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5dd
	jal ra, csr_bad_impl
	li a1, 0x5de
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5de
	jal ra, csr_bad_impl
	li a1, 0x5df
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5df
	jal ra, csr_bad_impl
	li a1, 0x5e0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5e0
	jal ra, csr_bad_impl
	li a1, 0x5e1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5e1
	jal ra, csr_bad_impl
	li a1, 0x5e2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5e2
	jal ra, csr_bad_impl
	li a1, 0x5e3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5e3
	jal ra, csr_bad_impl
	li a1, 0x5e4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5e4
	jal ra, csr_bad_impl
	li a1, 0x5e5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5e5
	jal ra, csr_bad_impl
	li a1, 0x5e6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5e6
	jal ra, csr_bad_impl
	li a1, 0x5e7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5e7
	jal ra, csr_bad_impl
	li a1, 0x5e8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5e8
	jal ra, csr_bad_impl
	li a1, 0x5e9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5e9
	jal ra, csr_bad_impl
	li a1, 0x5ea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ea
	jal ra, csr_bad_impl
	li a1, 0x5eb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5eb
	jal ra, csr_bad_impl
	li a1, 0x5ec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ec
	jal ra, csr_bad_impl
	li a1, 0x5ed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ed
	jal ra, csr_bad_impl
	li a1, 0x5ee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ee
	jal ra, csr_bad_impl
	li a1, 0x5ef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ef
	jal ra, csr_bad_impl
	li a1, 0x5f0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5f0
	jal ra, csr_bad_impl
	li a1, 0x5f1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5f1
	jal ra, csr_bad_impl
	li a1, 0x5f2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5f2
	jal ra, csr_bad_impl
	li a1, 0x5f3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5f3
	jal ra, csr_bad_impl
	li a1, 0x5f4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5f4
	jal ra, csr_bad_impl
	li a1, 0x5f5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5f5
	jal ra, csr_bad_impl
	li a1, 0x5f6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5f6
	jal ra, csr_bad_impl
	li a1, 0x5f7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5f7
	jal ra, csr_bad_impl
	li a1, 0x5f8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5f8
	jal ra, csr_bad_impl
	li a1, 0x5f9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5f9
	jal ra, csr_bad_impl
	li a1, 0x5fa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5fa
	jal ra, csr_bad_impl
	li a1, 0x5fb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5fb
	jal ra, csr_bad_impl
	li a1, 0x5fc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5fc
	jal ra, csr_bad_impl
	li a1, 0x5fd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5fd
	jal ra, csr_bad_impl
	li a1, 0x5fe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5fe
	jal ra, csr_bad_impl
	li a1, 0x5ff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x5ff
	jal ra, csr_bad_impl
	li a1, 0x600
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x600
	jal ra, csr_bad_impl
	li a1, 0x601
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x601
	jal ra, csr_bad_impl
	li a1, 0x602
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x602
	jal ra, csr_bad_impl
	li a1, 0x603
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x603
	jal ra, csr_bad_impl
	li a1, 0x604
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x604
	jal ra, csr_bad_impl
	li a1, 0x605
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x605
	jal ra, csr_bad_impl
	li a1, 0x606
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x606
	jal ra, csr_bad_impl
	li a1, 0x607
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x607
	jal ra, csr_bad_impl
	li a1, 0x608
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x608
	jal ra, csr_bad_impl
	li a1, 0x609
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x609
	jal ra, csr_bad_impl
	li a1, 0x60a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x60a
	jal ra, csr_bad_impl
	li a1, 0x60b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x60b
	jal ra, csr_bad_impl
	li a1, 0x60c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x60c
	jal ra, csr_bad_impl
	li a1, 0x60d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x60d
	jal ra, csr_bad_impl
	li a1, 0x60e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x60e
	jal ra, csr_bad_impl
	li a1, 0x60f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x60f
	jal ra, csr_bad_impl
	li a1, 0x610
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x610
	jal ra, csr_bad_impl
	li a1, 0x611
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x611
	jal ra, csr_bad_impl
	li a1, 0x612
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x612
	jal ra, csr_bad_impl
	li a1, 0x613
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x613
	jal ra, csr_bad_impl
	li a1, 0x614
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x614
	jal ra, csr_bad_impl
	li a1, 0x615
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x615
	jal ra, csr_bad_impl
	li a1, 0x616
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x616
	jal ra, csr_bad_impl
	li a1, 0x617
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x617
	jal ra, csr_bad_impl
	li a1, 0x618
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x618
	jal ra, csr_bad_impl
	li a1, 0x619
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x619
	jal ra, csr_bad_impl
	li a1, 0x61a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x61a
	jal ra, csr_bad_impl
	li a1, 0x61b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x61b
	jal ra, csr_bad_impl
	li a1, 0x61c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x61c
	jal ra, csr_bad_impl
	li a1, 0x61d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x61d
	jal ra, csr_bad_impl
	li a1, 0x61e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x61e
	jal ra, csr_bad_impl
	li a1, 0x61f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x61f
	jal ra, csr_bad_impl
	li a1, 0x620
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x620
	jal ra, csr_bad_impl
	li a1, 0x621
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x621
	jal ra, csr_bad_impl
	li a1, 0x622
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x622
	jal ra, csr_bad_impl
	li a1, 0x623
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x623
	jal ra, csr_bad_impl
	li a1, 0x624
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x624
	jal ra, csr_bad_impl
	li a1, 0x625
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x625
	jal ra, csr_bad_impl
	li a1, 0x626
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x626
	jal ra, csr_bad_impl
	li a1, 0x627
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x627
	jal ra, csr_bad_impl
	li a1, 0x628
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x628
	jal ra, csr_bad_impl
	li a1, 0x629
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x629
	jal ra, csr_bad_impl
	li a1, 0x62a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x62a
	jal ra, csr_bad_impl
	li a1, 0x62b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x62b
	jal ra, csr_bad_impl
	li a1, 0x62c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x62c
	jal ra, csr_bad_impl
	li a1, 0x62d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x62d
	jal ra, csr_bad_impl
	li a1, 0x62e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x62e
	jal ra, csr_bad_impl
	li a1, 0x62f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x62f
	jal ra, csr_bad_impl
	li a1, 0x630
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x630
	jal ra, csr_bad_impl
	li a1, 0x631
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x631
	jal ra, csr_bad_impl
	li a1, 0x632
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x632
	jal ra, csr_bad_impl
	li a1, 0x633
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x633
	jal ra, csr_bad_impl
	li a1, 0x634
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x634
	jal ra, csr_bad_impl
	li a1, 0x635
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x635
	jal ra, csr_bad_impl
	li a1, 0x636
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x636
	jal ra, csr_bad_impl
	li a1, 0x637
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x637
	jal ra, csr_bad_impl
	li a1, 0x638
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x638
	jal ra, csr_bad_impl
	li a1, 0x639
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x639
	jal ra, csr_bad_impl
	li a1, 0x63a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x63a
	jal ra, csr_bad_impl
	li a1, 0x63b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x63b
	jal ra, csr_bad_impl
	li a1, 0x63c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x63c
	jal ra, csr_bad_impl
	li a1, 0x63d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x63d
	jal ra, csr_bad_impl
	li a1, 0x63e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x63e
	jal ra, csr_bad_impl
	li a1, 0x63f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x63f
	jal ra, csr_bad_impl
	li a1, 0x640
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x640
	jal ra, csr_bad_impl
	li a1, 0x641
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x641
	jal ra, csr_bad_impl
	li a1, 0x642
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x642
	jal ra, csr_bad_impl
	li a1, 0x643
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x643
	jal ra, csr_bad_impl
	li a1, 0x644
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x644
	jal ra, csr_bad_impl
	li a1, 0x645
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x645
	jal ra, csr_bad_impl
	li a1, 0x646
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x646
	jal ra, csr_bad_impl
	li a1, 0x647
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x647
	jal ra, csr_bad_impl
	li a1, 0x648
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x648
	jal ra, csr_bad_impl
	li a1, 0x649
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x649
	jal ra, csr_bad_impl
	li a1, 0x64a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x64a
	jal ra, csr_bad_impl
	li a1, 0x64b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x64b
	jal ra, csr_bad_impl
	li a1, 0x64c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x64c
	jal ra, csr_bad_impl
	li a1, 0x64d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x64d
	jal ra, csr_bad_impl
	li a1, 0x64e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x64e
	jal ra, csr_bad_impl
	li a1, 0x64f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x64f
	jal ra, csr_bad_impl
	li a1, 0x650
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x650
	jal ra, csr_bad_impl
	li a1, 0x651
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x651
	jal ra, csr_bad_impl
	li a1, 0x652
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x652
	jal ra, csr_bad_impl
	li a1, 0x653
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x653
	jal ra, csr_bad_impl
	li a1, 0x654
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x654
	jal ra, csr_bad_impl
	li a1, 0x655
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x655
	jal ra, csr_bad_impl
	li a1, 0x656
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x656
	jal ra, csr_bad_impl
	li a1, 0x657
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x657
	jal ra, csr_bad_impl
	li a1, 0x658
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x658
	jal ra, csr_bad_impl
	li a1, 0x659
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x659
	jal ra, csr_bad_impl
	li a1, 0x65a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x65a
	jal ra, csr_bad_impl
	li a1, 0x65b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x65b
	jal ra, csr_bad_impl
	li a1, 0x65c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x65c
	jal ra, csr_bad_impl
	li a1, 0x65d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x65d
	jal ra, csr_bad_impl
	li a1, 0x65e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x65e
	jal ra, csr_bad_impl
	li a1, 0x65f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x65f
	jal ra, csr_bad_impl
	li a1, 0x660
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x660
	jal ra, csr_bad_impl
	li a1, 0x661
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x661
	jal ra, csr_bad_impl
	li a1, 0x662
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x662
	jal ra, csr_bad_impl
	li a1, 0x663
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x663
	jal ra, csr_bad_impl
	li a1, 0x664
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x664
	jal ra, csr_bad_impl
	li a1, 0x665
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x665
	jal ra, csr_bad_impl
	li a1, 0x666
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x666
	jal ra, csr_bad_impl
	li a1, 0x667
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x667
	jal ra, csr_bad_impl
	li a1, 0x668
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x668
	jal ra, csr_bad_impl
	li a1, 0x669
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x669
	jal ra, csr_bad_impl
	li a1, 0x66a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x66a
	jal ra, csr_bad_impl
	li a1, 0x66b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x66b
	jal ra, csr_bad_impl
	li a1, 0x66c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x66c
	jal ra, csr_bad_impl
	li a1, 0x66d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x66d
	jal ra, csr_bad_impl
	li a1, 0x66e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x66e
	jal ra, csr_bad_impl
	li a1, 0x66f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x66f
	jal ra, csr_bad_impl
	li a1, 0x670
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x670
	jal ra, csr_bad_impl
	li a1, 0x671
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x671
	jal ra, csr_bad_impl
	li a1, 0x672
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x672
	jal ra, csr_bad_impl
	li a1, 0x673
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x673
	jal ra, csr_bad_impl
	li a1, 0x674
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x674
	jal ra, csr_bad_impl
	li a1, 0x675
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x675
	jal ra, csr_bad_impl
	li a1, 0x676
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x676
	jal ra, csr_bad_impl
	li a1, 0x677
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x677
	jal ra, csr_bad_impl
	li a1, 0x678
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x678
	jal ra, csr_bad_impl
	li a1, 0x679
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x679
	jal ra, csr_bad_impl
	li a1, 0x67a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x67a
	jal ra, csr_bad_impl
	li a1, 0x67b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x67b
	jal ra, csr_bad_impl
	li a1, 0x67c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x67c
	jal ra, csr_bad_impl
	li a1, 0x67d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x67d
	jal ra, csr_bad_impl
	li a1, 0x67e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x67e
	jal ra, csr_bad_impl
	li a1, 0x67f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x67f
	jal ra, csr_bad_impl
	li a1, 0x680
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x680
	jal ra, csr_bad_impl
	li a1, 0x681
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x681
	jal ra, csr_bad_impl
	li a1, 0x682
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x682
	jal ra, csr_bad_impl
	li a1, 0x683
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x683
	jal ra, csr_bad_impl
	li a1, 0x684
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x684
	jal ra, csr_bad_impl
	li a1, 0x685
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x685
	jal ra, csr_bad_impl
	li a1, 0x686
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x686
	jal ra, csr_bad_impl
	li a1, 0x687
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x687
	jal ra, csr_bad_impl
	li a1, 0x688
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x688
	jal ra, csr_bad_impl
	li a1, 0x689
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x689
	jal ra, csr_bad_impl
	li a1, 0x68a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x68a
	jal ra, csr_bad_impl
	li a1, 0x68b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x68b
	jal ra, csr_bad_impl
	li a1, 0x68c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x68c
	jal ra, csr_bad_impl
	li a1, 0x68d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x68d
	jal ra, csr_bad_impl
	li a1, 0x68e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x68e
	jal ra, csr_bad_impl
	li a1, 0x68f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x68f
	jal ra, csr_bad_impl
	li a1, 0x690
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x690
	jal ra, csr_bad_impl
	li a1, 0x691
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x691
	jal ra, csr_bad_impl
	li a1, 0x692
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x692
	jal ra, csr_bad_impl
	li a1, 0x693
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x693
	jal ra, csr_bad_impl
	li a1, 0x694
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x694
	jal ra, csr_bad_impl
	li a1, 0x695
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x695
	jal ra, csr_bad_impl
	li a1, 0x696
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x696
	jal ra, csr_bad_impl
	li a1, 0x697
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x697
	jal ra, csr_bad_impl
	li a1, 0x698
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x698
	jal ra, csr_bad_impl
	li a1, 0x699
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x699
	jal ra, csr_bad_impl
	li a1, 0x69a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x69a
	jal ra, csr_bad_impl
	li a1, 0x69b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x69b
	jal ra, csr_bad_impl
	li a1, 0x69c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x69c
	jal ra, csr_bad_impl
	li a1, 0x69d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x69d
	jal ra, csr_bad_impl
	li a1, 0x69e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x69e
	jal ra, csr_bad_impl
	li a1, 0x69f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x69f
	jal ra, csr_bad_impl
	li a1, 0x6a0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6a0
	jal ra, csr_bad_impl
	li a1, 0x6a1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6a1
	jal ra, csr_bad_impl
	li a1, 0x6a2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6a2
	jal ra, csr_bad_impl
	li a1, 0x6a3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6a3
	jal ra, csr_bad_impl
	li a1, 0x6a4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6a4
	jal ra, csr_bad_impl
	li a1, 0x6a5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6a5
	jal ra, csr_bad_impl
	li a1, 0x6a6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6a6
	jal ra, csr_bad_impl
	li a1, 0x6a7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6a7
	jal ra, csr_bad_impl
	li a1, 0x6a8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6a8
	jal ra, csr_bad_impl
	li a1, 0x6a9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6a9
	jal ra, csr_bad_impl
	li a1, 0x6aa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6aa
	jal ra, csr_bad_impl
	li a1, 0x6ab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ab
	jal ra, csr_bad_impl
	li a1, 0x6ac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ac
	jal ra, csr_bad_impl
	li a1, 0x6ad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ad
	jal ra, csr_bad_impl
	li a1, 0x6ae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ae
	jal ra, csr_bad_impl
	li a1, 0x6af
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6af
	jal ra, csr_bad_impl
	li a1, 0x6b0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6b0
	jal ra, csr_bad_impl
	li a1, 0x6b1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6b1
	jal ra, csr_bad_impl
	li a1, 0x6b2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6b2
	jal ra, csr_bad_impl
	li a1, 0x6b3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6b3
	jal ra, csr_bad_impl
	li a1, 0x6b4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6b4
	jal ra, csr_bad_impl
	li a1, 0x6b5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6b5
	jal ra, csr_bad_impl
	li a1, 0x6b6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6b6
	jal ra, csr_bad_impl
	li a1, 0x6b7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6b7
	jal ra, csr_bad_impl
	li a1, 0x6b8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6b8
	jal ra, csr_bad_impl
	li a1, 0x6b9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6b9
	jal ra, csr_bad_impl
	li a1, 0x6ba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ba
	jal ra, csr_bad_impl
	li a1, 0x6bb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6bb
	jal ra, csr_bad_impl
	li a1, 0x6bc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6bc
	jal ra, csr_bad_impl
	li a1, 0x6bd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6bd
	jal ra, csr_bad_impl
	li a1, 0x6be
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6be
	jal ra, csr_bad_impl
	li a1, 0x6bf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6bf
	jal ra, csr_bad_impl
	li a1, 0x6c0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6c0
	jal ra, csr_bad_impl
	li a1, 0x6c1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6c1
	jal ra, csr_bad_impl
	li a1, 0x6c2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6c2
	jal ra, csr_bad_impl
	li a1, 0x6c3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6c3
	jal ra, csr_bad_impl
	li a1, 0x6c4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6c4
	jal ra, csr_bad_impl
	li a1, 0x6c5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6c5
	jal ra, csr_bad_impl
	li a1, 0x6c6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6c6
	jal ra, csr_bad_impl
	li a1, 0x6c7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6c7
	jal ra, csr_bad_impl
	li a1, 0x6c8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6c8
	jal ra, csr_bad_impl
	li a1, 0x6c9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6c9
	jal ra, csr_bad_impl
	li a1, 0x6ca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ca
	jal ra, csr_bad_impl
	li a1, 0x6cb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6cb
	jal ra, csr_bad_impl
	li a1, 0x6cc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6cc
	jal ra, csr_bad_impl
	li a1, 0x6cd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6cd
	jal ra, csr_bad_impl
	li a1, 0x6ce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ce
	jal ra, csr_bad_impl
	li a1, 0x6cf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6cf
	jal ra, csr_bad_impl
	li a1, 0x6d0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6d0
	jal ra, csr_bad_impl
	li a1, 0x6d1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6d1
	jal ra, csr_bad_impl
	li a1, 0x6d2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6d2
	jal ra, csr_bad_impl
	li a1, 0x6d3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6d3
	jal ra, csr_bad_impl
	li a1, 0x6d4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6d4
	jal ra, csr_bad_impl
	li a1, 0x6d5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6d5
	jal ra, csr_bad_impl
	li a1, 0x6d6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6d6
	jal ra, csr_bad_impl
	li a1, 0x6d7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6d7
	jal ra, csr_bad_impl
	li a1, 0x6d8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6d8
	jal ra, csr_bad_impl
	li a1, 0x6d9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6d9
	jal ra, csr_bad_impl
	li a1, 0x6da
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6da
	jal ra, csr_bad_impl
	li a1, 0x6db
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6db
	jal ra, csr_bad_impl
	li a1, 0x6dc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6dc
	jal ra, csr_bad_impl
	li a1, 0x6dd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6dd
	jal ra, csr_bad_impl
	li a1, 0x6de
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6de
	jal ra, csr_bad_impl
	li a1, 0x6df
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6df
	jal ra, csr_bad_impl
	li a1, 0x6e0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6e0
	jal ra, csr_bad_impl
	li a1, 0x6e1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6e1
	jal ra, csr_bad_impl
	li a1, 0x6e2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6e2
	jal ra, csr_bad_impl
	li a1, 0x6e3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6e3
	jal ra, csr_bad_impl
	li a1, 0x6e4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6e4
	jal ra, csr_bad_impl
	li a1, 0x6e5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6e5
	jal ra, csr_bad_impl
	li a1, 0x6e6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6e6
	jal ra, csr_bad_impl
	li a1, 0x6e7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6e7
	jal ra, csr_bad_impl
	li a1, 0x6e8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6e8
	jal ra, csr_bad_impl
	li a1, 0x6e9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6e9
	jal ra, csr_bad_impl
	li a1, 0x6ea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ea
	jal ra, csr_bad_impl
	li a1, 0x6eb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6eb
	jal ra, csr_bad_impl
	li a1, 0x6ec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ec
	jal ra, csr_bad_impl
	li a1, 0x6ed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ed
	jal ra, csr_bad_impl
	li a1, 0x6ee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ee
	jal ra, csr_bad_impl
	li a1, 0x6ef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ef
	jal ra, csr_bad_impl
	li a1, 0x6f0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6f0
	jal ra, csr_bad_impl
	li a1, 0x6f1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6f1
	jal ra, csr_bad_impl
	li a1, 0x6f2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6f2
	jal ra, csr_bad_impl
	li a1, 0x6f3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6f3
	jal ra, csr_bad_impl
	li a1, 0x6f4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6f4
	jal ra, csr_bad_impl
	li a1, 0x6f5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6f5
	jal ra, csr_bad_impl
	li a1, 0x6f6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6f6
	jal ra, csr_bad_impl
	li a1, 0x6f7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6f7
	jal ra, csr_bad_impl
	li a1, 0x6f8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6f8
	jal ra, csr_bad_impl
	li a1, 0x6f9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6f9
	jal ra, csr_bad_impl
	li a1, 0x6fa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6fa
	jal ra, csr_bad_impl
	li a1, 0x6fb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6fb
	jal ra, csr_bad_impl
	li a1, 0x6fc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6fc
	jal ra, csr_bad_impl
	li a1, 0x6fd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6fd
	jal ra, csr_bad_impl
	li a1, 0x6fe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6fe
	jal ra, csr_bad_impl
	li a1, 0x6ff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x6ff
	jal ra, csr_bad_impl
	li a1, 0x700
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x700
	jal ra, csr_bad_impl
	li a1, 0x701
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x701
	jal ra, csr_bad_impl
	li a1, 0x702
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x702
	jal ra, csr_bad_impl
	li a1, 0x703
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x703
	jal ra, csr_bad_impl
	li a1, 0x704
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x704
	jal ra, csr_bad_impl
	li a1, 0x705
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x705
	jal ra, csr_bad_impl
	li a1, 0x706
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x706
	jal ra, csr_bad_impl
	li a1, 0x707
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x707
	jal ra, csr_bad_impl
	li a1, 0x708
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x708
	jal ra, csr_bad_impl
	li a1, 0x709
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x709
	jal ra, csr_bad_impl
	li a1, 0x70a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x70a
	jal ra, csr_bad_impl
	li a1, 0x70b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x70b
	jal ra, csr_bad_impl
	li a1, 0x70c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x70c
	jal ra, csr_bad_impl
	li a1, 0x70d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x70d
	jal ra, csr_bad_impl
	li a1, 0x70e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x70e
	jal ra, csr_bad_impl
	li a1, 0x70f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x70f
	jal ra, csr_bad_impl
	li a1, 0x710
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x710
	jal ra, csr_bad_impl
	li a1, 0x711
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x711
	jal ra, csr_bad_impl
	li a1, 0x712
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x712
	jal ra, csr_bad_impl
	li a1, 0x713
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x713
	jal ra, csr_bad_impl
	li a1, 0x714
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x714
	jal ra, csr_bad_impl
	li a1, 0x715
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x715
	jal ra, csr_bad_impl
	li a1, 0x716
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x716
	jal ra, csr_bad_impl
	li a1, 0x717
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x717
	jal ra, csr_bad_impl
	li a1, 0x718
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x718
	jal ra, csr_bad_impl
	li a1, 0x719
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x719
	jal ra, csr_bad_impl
	li a1, 0x71a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x71a
	jal ra, csr_bad_impl
	li a1, 0x71b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x71b
	jal ra, csr_bad_impl
	li a1, 0x71c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x71c
	jal ra, csr_bad_impl
	li a1, 0x71d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x71d
	jal ra, csr_bad_impl
	li a1, 0x71e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x71e
	jal ra, csr_bad_impl
	li a1, 0x71f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x71f
	jal ra, csr_bad_impl
	li a1, 0x720
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x720
	jal ra, csr_bad_impl
	li a1, 0x721
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x721
	jal ra, csr_bad_impl
	li a1, 0x722
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x722
	jal ra, csr_bad_impl
	li a1, 0x723
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x723
	jal ra, csr_bad_impl
	li a1, 0x724
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x724
	jal ra, csr_bad_impl
	li a1, 0x725
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x725
	jal ra, csr_bad_impl
	li a1, 0x726
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x726
	jal ra, csr_bad_impl
	li a1, 0x727
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x727
	jal ra, csr_bad_impl
	li a1, 0x728
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x728
	jal ra, csr_bad_impl
	li a1, 0x729
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x729
	jal ra, csr_bad_impl
	li a1, 0x72a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x72a
	jal ra, csr_bad_impl
	li a1, 0x72b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x72b
	jal ra, csr_bad_impl
	li a1, 0x72c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x72c
	jal ra, csr_bad_impl
	li a1, 0x72d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x72d
	jal ra, csr_bad_impl
	li a1, 0x72e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x72e
	jal ra, csr_bad_impl
	li a1, 0x72f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x72f
	jal ra, csr_bad_impl
	li a1, 0x730
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x730
	jal ra, csr_bad_impl
	li a1, 0x731
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x731
	jal ra, csr_bad_impl
	li a1, 0x732
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x732
	jal ra, csr_bad_impl
	li a1, 0x733
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x733
	jal ra, csr_bad_impl
	li a1, 0x734
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x734
	jal ra, csr_bad_impl
	li a1, 0x735
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x735
	jal ra, csr_bad_impl
	li a1, 0x736
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x736
	jal ra, csr_bad_impl
	li a1, 0x737
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x737
	jal ra, csr_bad_impl
	li a1, 0x738
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x738
	jal ra, csr_bad_impl
	li a1, 0x739
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x739
	jal ra, csr_bad_impl
	li a1, 0x73a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x73a
	jal ra, csr_bad_impl
	li a1, 0x73b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x73b
	jal ra, csr_bad_impl
	li a1, 0x73c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x73c
	jal ra, csr_bad_impl
	li a1, 0x73d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x73d
	jal ra, csr_bad_impl
	li a1, 0x73e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x73e
	jal ra, csr_bad_impl
	li a1, 0x73f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x73f
	jal ra, csr_bad_impl
	li a1, 0x740
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x740
	jal ra, csr_bad_impl
	li a1, 0x741
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x741
	jal ra, csr_bad_impl
	li a1, 0x742
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x742
	jal ra, csr_bad_impl
	li a1, 0x743
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x743
	jal ra, csr_bad_impl
	li a1, 0x744
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x744
	jal ra, csr_bad_impl
	li a1, 0x745
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x745
	jal ra, csr_bad_impl
	li a1, 0x746
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x746
	jal ra, csr_bad_impl
	li a1, 0x747
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x747
	jal ra, csr_bad_impl
	li a1, 0x748
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x748
	jal ra, csr_bad_impl
	li a1, 0x749
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x749
	jal ra, csr_bad_impl
	li a1, 0x74a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x74a
	jal ra, csr_bad_impl
	li a1, 0x74b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x74b
	jal ra, csr_bad_impl
	li a1, 0x74c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x74c
	jal ra, csr_bad_impl
	li a1, 0x74d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x74d
	jal ra, csr_bad_impl
	li a1, 0x74e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x74e
	jal ra, csr_bad_impl
	li a1, 0x74f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x74f
	jal ra, csr_bad_impl
	li a1, 0x750
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x750
	jal ra, csr_bad_impl
	li a1, 0x751
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x751
	jal ra, csr_bad_impl
	li a1, 0x752
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x752
	jal ra, csr_bad_impl
	li a1, 0x753
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x753
	jal ra, csr_bad_impl
	li a1, 0x754
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x754
	jal ra, csr_bad_impl
	li a1, 0x755
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x755
	jal ra, csr_bad_impl
	li a1, 0x756
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x756
	jal ra, csr_bad_impl
	li a1, 0x757
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x757
	jal ra, csr_bad_impl
	li a1, 0x758
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x758
	jal ra, csr_bad_impl
	li a1, 0x759
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x759
	jal ra, csr_bad_impl
	li a1, 0x75a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x75a
	jal ra, csr_bad_impl
	li a1, 0x75b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x75b
	jal ra, csr_bad_impl
	li a1, 0x75c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x75c
	jal ra, csr_bad_impl
	li a1, 0x75d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x75d
	jal ra, csr_bad_impl
	li a1, 0x75e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x75e
	jal ra, csr_bad_impl
	li a1, 0x75f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x75f
	jal ra, csr_bad_impl
	li a1, 0x760
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x760
	jal ra, csr_bad_impl
	li a1, 0x761
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x761
	jal ra, csr_bad_impl
	li a1, 0x762
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x762
	jal ra, csr_bad_impl
	li a1, 0x763
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x763
	jal ra, csr_bad_impl
	li a1, 0x764
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x764
	jal ra, csr_bad_impl
	li a1, 0x765
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x765
	jal ra, csr_bad_impl
	li a1, 0x766
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x766
	jal ra, csr_bad_impl
	li a1, 0x767
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x767
	jal ra, csr_bad_impl
	li a1, 0x768
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x768
	jal ra, csr_bad_impl
	li a1, 0x769
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x769
	jal ra, csr_bad_impl
	li a1, 0x76a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x76a
	jal ra, csr_bad_impl
	li a1, 0x76b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x76b
	jal ra, csr_bad_impl
	li a1, 0x76c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x76c
	jal ra, csr_bad_impl
	li a1, 0x76d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x76d
	jal ra, csr_bad_impl
	li a1, 0x76e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x76e
	jal ra, csr_bad_impl
	li a1, 0x76f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x76f
	jal ra, csr_bad_impl
	li a1, 0x770
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x770
	jal ra, csr_bad_impl
	li a1, 0x771
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x771
	jal ra, csr_bad_impl
	li a1, 0x772
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x772
	jal ra, csr_bad_impl
	li a1, 0x773
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x773
	jal ra, csr_bad_impl
	li a1, 0x774
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x774
	jal ra, csr_bad_impl
	li a1, 0x775
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x775
	jal ra, csr_bad_impl
	li a1, 0x776
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x776
	jal ra, csr_bad_impl
	li a1, 0x777
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x777
	jal ra, csr_bad_impl
	li a1, 0x778
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x778
	jal ra, csr_bad_impl
	li a1, 0x779
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x779
	jal ra, csr_bad_impl
	li a1, 0x77a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x77a
	jal ra, csr_bad_impl
	li a1, 0x77b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x77b
	jal ra, csr_bad_impl
	li a1, 0x77c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x77c
	jal ra, csr_bad_impl
	li a1, 0x77d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x77d
	jal ra, csr_bad_impl
	li a1, 0x77e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x77e
	jal ra, csr_bad_impl
	li a1, 0x77f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x77f
	jal ra, csr_bad_impl
	li a1, 0x780
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x780
	jal ra, csr_bad_impl
	li a1, 0x781
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x781
	jal ra, csr_bad_impl
	li a1, 0x782
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x782
	jal ra, csr_bad_impl
	li a1, 0x783
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x783
	jal ra, csr_bad_impl
	li a1, 0x784
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x784
	jal ra, csr_bad_impl
	li a1, 0x785
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x785
	jal ra, csr_bad_impl
	li a1, 0x786
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x786
	jal ra, csr_bad_impl
	li a1, 0x787
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x787
	jal ra, csr_bad_impl
	li a1, 0x788
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x788
	jal ra, csr_bad_impl
	li a1, 0x789
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x789
	jal ra, csr_bad_impl
	li a1, 0x78a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x78a
	jal ra, csr_bad_impl
	li a1, 0x78b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x78b
	jal ra, csr_bad_impl
	li a1, 0x78c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x78c
	jal ra, csr_bad_impl
	li a1, 0x78d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x78d
	jal ra, csr_bad_impl
	li a1, 0x78e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x78e
	jal ra, csr_bad_impl
	li a1, 0x78f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x78f
	jal ra, csr_bad_impl
	li a1, 0x790
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x790
	jal ra, csr_bad_impl
	li a1, 0x791
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x791
	jal ra, csr_bad_impl
	li a1, 0x792
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x792
	jal ra, csr_bad_impl
	li a1, 0x793
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x793
	jal ra, csr_bad_impl
	li a1, 0x794
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x794
	jal ra, csr_bad_impl
	li a1, 0x795
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x795
	jal ra, csr_bad_impl
	li a1, 0x796
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x796
	jal ra, csr_bad_impl
	li a1, 0x797
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x797
	jal ra, csr_bad_impl
	li a1, 0x798
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x798
	jal ra, csr_bad_impl
	li a1, 0x799
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x799
	jal ra, csr_bad_impl
	li a1, 0x79a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x79a
	jal ra, csr_bad_impl
	li a1, 0x79b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x79b
	jal ra, csr_bad_impl
	li a1, 0x79c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x79c
	jal ra, csr_bad_impl
	li a1, 0x79d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x79d
	jal ra, csr_bad_impl
	li a1, 0x79e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x79e
	jal ra, csr_bad_impl
	li a1, 0x79f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x79f
	jal ra, csr_bad_impl
	li a1, 0x7a4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7a4
	jal ra, csr_bad_impl
	li a1, 0x7a5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7a5
	jal ra, csr_bad_impl
	li a1, 0x7a6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7a6
	jal ra, csr_bad_impl
	li a1, 0x7a7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7a7
	jal ra, csr_bad_impl
	li a1, 0x7a9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7a9
	jal ra, csr_bad_impl
	li a1, 0x7ab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ab
	jal ra, csr_bad_impl
	li a1, 0x7ac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ac
	jal ra, csr_bad_impl
	li a1, 0x7ad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ad
	jal ra, csr_bad_impl
	li a1, 0x7ae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ae
	jal ra, csr_bad_impl
	li a1, 0x7af
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7af
	jal ra, csr_bad_impl
	li a1, 0x7b0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7b0
	jal ra, csr_bad_impl
	li a1, 0x7b1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7b1
	jal ra, csr_bad_impl
	li a1, 0x7b2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7b2
	jal ra, csr_bad_impl
	li a1, 0x7b3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7b3
	jal ra, csr_bad_impl
	li a1, 0x7b4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7b4
	jal ra, csr_bad_impl
	li a1, 0x7b5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7b5
	jal ra, csr_bad_impl
	li a1, 0x7b6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7b6
	jal ra, csr_bad_impl
	li a1, 0x7b7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7b7
	jal ra, csr_bad_impl
	li a1, 0x7b8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7b8
	jal ra, csr_bad_impl
	li a1, 0x7b9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7b9
	jal ra, csr_bad_impl
	li a1, 0x7ba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ba
	jal ra, csr_bad_impl
	li a1, 0x7bb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7bb
	jal ra, csr_bad_impl
	li a1, 0x7bc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7bc
	jal ra, csr_bad_impl
	li a1, 0x7bd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7bd
	jal ra, csr_bad_impl
	li a1, 0x7be
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7be
	jal ra, csr_bad_impl
	li a1, 0x7bf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7bf
	jal ra, csr_bad_impl
	li a1, 0x7c0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7c0
	jal ra, csr_bad_impl
	li a1, 0x7c2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7c2
	jal ra, csr_bad_impl
	li a1, 0x7c3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7c3
	jal ra, csr_bad_impl
	li a1, 0x7c4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7c4
	jal ra, csr_bad_impl
	li a1, 0x7c5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7c5
	jal ra, csr_bad_impl
	li a1, 0x7c6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7c6
	jal ra, csr_bad_impl
	li a1, 0x7c7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7c7
	jal ra, csr_bad_impl
	li a1, 0x7c8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7c8
	jal ra, csr_bad_impl
	li a1, 0x7c9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7c9
	jal ra, csr_bad_impl
	li a1, 0x7ca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ca
	jal ra, csr_bad_impl
	li a1, 0x7cb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7cb
	jal ra, csr_bad_impl
	li a1, 0x7cc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7cc
	jal ra, csr_bad_impl
	li a1, 0x7cd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7cd
	jal ra, csr_bad_impl
	li a1, 0x7ce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ce
	jal ra, csr_bad_impl
	li a1, 0x7cf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7cf
	jal ra, csr_bad_impl
	li a1, 0x7d0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7d0
	jal ra, csr_bad_impl
	li a1, 0x7d1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7d1
	jal ra, csr_bad_impl
	li a1, 0x7d2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7d2
	jal ra, csr_bad_impl
	li a1, 0x7d3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7d3
	jal ra, csr_bad_impl
	li a1, 0x7d4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7d4
	jal ra, csr_bad_impl
	li a1, 0x7d5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7d5
	jal ra, csr_bad_impl
	li a1, 0x7d6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7d6
	jal ra, csr_bad_impl
	li a1, 0x7d7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7d7
	jal ra, csr_bad_impl
	li a1, 0x7d8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7d8
	jal ra, csr_bad_impl
	li a1, 0x7d9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7d9
	jal ra, csr_bad_impl
	li a1, 0x7da
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7da
	jal ra, csr_bad_impl
	li a1, 0x7db
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7db
	jal ra, csr_bad_impl
	li a1, 0x7dc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7dc
	jal ra, csr_bad_impl
	li a1, 0x7dd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7dd
	jal ra, csr_bad_impl
	li a1, 0x7de
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7de
	jal ra, csr_bad_impl
	li a1, 0x7df
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7df
	jal ra, csr_bad_impl
	li a1, 0x7e0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7e0
	jal ra, csr_bad_impl
	li a1, 0x7e1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7e1
	jal ra, csr_bad_impl
	li a1, 0x7e2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7e2
	jal ra, csr_bad_impl
	li a1, 0x7e3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7e3
	jal ra, csr_bad_impl
	li a1, 0x7e4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7e4
	jal ra, csr_bad_impl
	li a1, 0x7e5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7e5
	jal ra, csr_bad_impl
	li a1, 0x7e6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7e6
	jal ra, csr_bad_impl
	li a1, 0x7e7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7e7
	jal ra, csr_bad_impl
	li a1, 0x7e8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7e8
	jal ra, csr_bad_impl
	li a1, 0x7e9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7e9
	jal ra, csr_bad_impl
	li a1, 0x7ea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ea
	jal ra, csr_bad_impl
	li a1, 0x7eb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7eb
	jal ra, csr_bad_impl
	li a1, 0x7ec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ec
	jal ra, csr_bad_impl
	li a1, 0x7ed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ed
	jal ra, csr_bad_impl
	li a1, 0x7ee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ee
	jal ra, csr_bad_impl
	li a1, 0x7ef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ef
	jal ra, csr_bad_impl
	li a1, 0x7f0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7f0
	jal ra, csr_bad_impl
	li a1, 0x7f1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7f1
	jal ra, csr_bad_impl
	li a1, 0x7f2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7f2
	jal ra, csr_bad_impl
	li a1, 0x7f3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7f3
	jal ra, csr_bad_impl
	li a1, 0x7f4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7f4
	jal ra, csr_bad_impl
	li a1, 0x7f5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7f5
	jal ra, csr_bad_impl
	li a1, 0x7f6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7f6
	jal ra, csr_bad_impl
	li a1, 0x7f7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7f7
	jal ra, csr_bad_impl
	li a1, 0x7f8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7f8
	jal ra, csr_bad_impl
	li a1, 0x7f9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7f9
	jal ra, csr_bad_impl
	li a1, 0x7fa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7fa
	jal ra, csr_bad_impl
	li a1, 0x7fb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7fb
	jal ra, csr_bad_impl
	li a1, 0x7fc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7fc
	jal ra, csr_bad_impl
	li a1, 0x7fd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7fd
	jal ra, csr_bad_impl
	li a1, 0x7fe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7fe
	jal ra, csr_bad_impl
	li a1, 0x7ff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x7ff
	jal ra, csr_bad_impl
	li a1, 0x800
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x800
	jal ra, csr_bad_impl
	li a1, 0x801
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x801
	jal ra, csr_bad_impl
	li a1, 0x802
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x802
	jal ra, csr_bad_impl
	li a1, 0x803
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x803
	jal ra, csr_bad_impl
	li a1, 0x804
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x804
	jal ra, csr_bad_impl
	li a1, 0x805
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x805
	jal ra, csr_bad_impl
	li a1, 0x806
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x806
	jal ra, csr_bad_impl
	li a1, 0x807
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x807
	jal ra, csr_bad_impl
	li a1, 0x808
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x808
	jal ra, csr_bad_impl
	li a1, 0x809
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x809
	jal ra, csr_bad_impl
	li a1, 0x80a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x80a
	jal ra, csr_bad_impl
	li a1, 0x80b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x80b
	jal ra, csr_bad_impl
	li a1, 0x80c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x80c
	jal ra, csr_bad_impl
	li a1, 0x80d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x80d
	jal ra, csr_bad_impl
	li a1, 0x80e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x80e
	jal ra, csr_bad_impl
	li a1, 0x80f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x80f
	jal ra, csr_bad_impl
	li a1, 0x810
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x810
	jal ra, csr_bad_impl
	li a1, 0x811
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x811
	jal ra, csr_bad_impl
	li a1, 0x812
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x812
	jal ra, csr_bad_impl
	li a1, 0x813
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x813
	jal ra, csr_bad_impl
	li a1, 0x814
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x814
	jal ra, csr_bad_impl
	li a1, 0x815
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x815
	jal ra, csr_bad_impl
	li a1, 0x816
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x816
	jal ra, csr_bad_impl
	li a1, 0x817
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x817
	jal ra, csr_bad_impl
	li a1, 0x818
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x818
	jal ra, csr_bad_impl
	li a1, 0x819
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x819
	jal ra, csr_bad_impl
	li a1, 0x81a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x81a
	jal ra, csr_bad_impl
	li a1, 0x81b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x81b
	jal ra, csr_bad_impl
	li a1, 0x81c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x81c
	jal ra, csr_bad_impl
	li a1, 0x81d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x81d
	jal ra, csr_bad_impl
	li a1, 0x81e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x81e
	jal ra, csr_bad_impl
	li a1, 0x81f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x81f
	jal ra, csr_bad_impl
	li a1, 0x820
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x820
	jal ra, csr_bad_impl
	li a1, 0x821
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x821
	jal ra, csr_bad_impl
	li a1, 0x822
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x822
	jal ra, csr_bad_impl
	li a1, 0x823
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x823
	jal ra, csr_bad_impl
	li a1, 0x824
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x824
	jal ra, csr_bad_impl
	li a1, 0x825
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x825
	jal ra, csr_bad_impl
	li a1, 0x826
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x826
	jal ra, csr_bad_impl
	li a1, 0x827
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x827
	jal ra, csr_bad_impl
	li a1, 0x828
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x828
	jal ra, csr_bad_impl
	li a1, 0x829
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x829
	jal ra, csr_bad_impl
	li a1, 0x82a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x82a
	jal ra, csr_bad_impl
	li a1, 0x82b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x82b
	jal ra, csr_bad_impl
	li a1, 0x82c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x82c
	jal ra, csr_bad_impl
	li a1, 0x82d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x82d
	jal ra, csr_bad_impl
	li a1, 0x82e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x82e
	jal ra, csr_bad_impl
	li a1, 0x82f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x82f
	jal ra, csr_bad_impl
	li a1, 0x830
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x830
	jal ra, csr_bad_impl
	li a1, 0x831
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x831
	jal ra, csr_bad_impl
	li a1, 0x832
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x832
	jal ra, csr_bad_impl
	li a1, 0x833
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x833
	jal ra, csr_bad_impl
	li a1, 0x834
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x834
	jal ra, csr_bad_impl
	li a1, 0x835
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x835
	jal ra, csr_bad_impl
	li a1, 0x836
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x836
	jal ra, csr_bad_impl
	li a1, 0x837
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x837
	jal ra, csr_bad_impl
	li a1, 0x838
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x838
	jal ra, csr_bad_impl
	li a1, 0x839
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x839
	jal ra, csr_bad_impl
	li a1, 0x83a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x83a
	jal ra, csr_bad_impl
	li a1, 0x83b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x83b
	jal ra, csr_bad_impl
	li a1, 0x83c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x83c
	jal ra, csr_bad_impl
	li a1, 0x83d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x83d
	jal ra, csr_bad_impl
	li a1, 0x83e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x83e
	jal ra, csr_bad_impl
	li a1, 0x83f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x83f
	jal ra, csr_bad_impl
	li a1, 0x840
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x840
	jal ra, csr_bad_impl
	li a1, 0x841
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x841
	jal ra, csr_bad_impl
	li a1, 0x842
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x842
	jal ra, csr_bad_impl
	li a1, 0x843
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x843
	jal ra, csr_bad_impl
	li a1, 0x844
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x844
	jal ra, csr_bad_impl
	li a1, 0x845
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x845
	jal ra, csr_bad_impl
	li a1, 0x846
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x846
	jal ra, csr_bad_impl
	li a1, 0x847
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x847
	jal ra, csr_bad_impl
	li a1, 0x848
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x848
	jal ra, csr_bad_impl
	li a1, 0x849
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x849
	jal ra, csr_bad_impl
	li a1, 0x84a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x84a
	jal ra, csr_bad_impl
	li a1, 0x84b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x84b
	jal ra, csr_bad_impl
	li a1, 0x84c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x84c
	jal ra, csr_bad_impl
	li a1, 0x84d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x84d
	jal ra, csr_bad_impl
	li a1, 0x84e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x84e
	jal ra, csr_bad_impl
	li a1, 0x84f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x84f
	jal ra, csr_bad_impl
	li a1, 0x850
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x850
	jal ra, csr_bad_impl
	li a1, 0x851
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x851
	jal ra, csr_bad_impl
	li a1, 0x852
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x852
	jal ra, csr_bad_impl
	li a1, 0x853
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x853
	jal ra, csr_bad_impl
	li a1, 0x854
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x854
	jal ra, csr_bad_impl
	li a1, 0x855
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x855
	jal ra, csr_bad_impl
	li a1, 0x856
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x856
	jal ra, csr_bad_impl
	li a1, 0x857
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x857
	jal ra, csr_bad_impl
	li a1, 0x858
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x858
	jal ra, csr_bad_impl
	li a1, 0x859
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x859
	jal ra, csr_bad_impl
	li a1, 0x85a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x85a
	jal ra, csr_bad_impl
	li a1, 0x85b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x85b
	jal ra, csr_bad_impl
	li a1, 0x85c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x85c
	jal ra, csr_bad_impl
	li a1, 0x85d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x85d
	jal ra, csr_bad_impl
	li a1, 0x85e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x85e
	jal ra, csr_bad_impl
	li a1, 0x85f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x85f
	jal ra, csr_bad_impl
	li a1, 0x860
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x860
	jal ra, csr_bad_impl
	li a1, 0x861
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x861
	jal ra, csr_bad_impl
	li a1, 0x862
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x862
	jal ra, csr_bad_impl
	li a1, 0x863
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x863
	jal ra, csr_bad_impl
	li a1, 0x864
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x864
	jal ra, csr_bad_impl
	li a1, 0x865
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x865
	jal ra, csr_bad_impl
	li a1, 0x866
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x866
	jal ra, csr_bad_impl
	li a1, 0x867
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x867
	jal ra, csr_bad_impl
	li a1, 0x868
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x868
	jal ra, csr_bad_impl
	li a1, 0x869
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x869
	jal ra, csr_bad_impl
	li a1, 0x86a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x86a
	jal ra, csr_bad_impl
	li a1, 0x86b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x86b
	jal ra, csr_bad_impl
	li a1, 0x86c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x86c
	jal ra, csr_bad_impl
	li a1, 0x86d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x86d
	jal ra, csr_bad_impl
	li a1, 0x86e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x86e
	jal ra, csr_bad_impl
	li a1, 0x86f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x86f
	jal ra, csr_bad_impl
	li a1, 0x870
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x870
	jal ra, csr_bad_impl
	li a1, 0x871
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x871
	jal ra, csr_bad_impl
	li a1, 0x872
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x872
	jal ra, csr_bad_impl
	li a1, 0x873
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x873
	jal ra, csr_bad_impl
	li a1, 0x874
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x874
	jal ra, csr_bad_impl
	li a1, 0x875
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x875
	jal ra, csr_bad_impl
	li a1, 0x876
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x876
	jal ra, csr_bad_impl
	li a1, 0x877
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x877
	jal ra, csr_bad_impl
	li a1, 0x878
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x878
	jal ra, csr_bad_impl
	li a1, 0x879
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x879
	jal ra, csr_bad_impl
	li a1, 0x87a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x87a
	jal ra, csr_bad_impl
	li a1, 0x87b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x87b
	jal ra, csr_bad_impl
	li a1, 0x87c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x87c
	jal ra, csr_bad_impl
	li a1, 0x87d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x87d
	jal ra, csr_bad_impl
	li a1, 0x87e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x87e
	jal ra, csr_bad_impl
	li a1, 0x87f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x87f
	jal ra, csr_bad_impl
	li a1, 0x880
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x880
	jal ra, csr_bad_impl
	li a1, 0x881
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x881
	jal ra, csr_bad_impl
	li a1, 0x882
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x882
	jal ra, csr_bad_impl
	li a1, 0x883
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x883
	jal ra, csr_bad_impl
	li a1, 0x884
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x884
	jal ra, csr_bad_impl
	li a1, 0x885
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x885
	jal ra, csr_bad_impl
	li a1, 0x886
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x886
	jal ra, csr_bad_impl
	li a1, 0x887
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x887
	jal ra, csr_bad_impl
	li a1, 0x888
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x888
	jal ra, csr_bad_impl
	li a1, 0x889
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x889
	jal ra, csr_bad_impl
	li a1, 0x88a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x88a
	jal ra, csr_bad_impl
	li a1, 0x88b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x88b
	jal ra, csr_bad_impl
	li a1, 0x88c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x88c
	jal ra, csr_bad_impl
	li a1, 0x88d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x88d
	jal ra, csr_bad_impl
	li a1, 0x88e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x88e
	jal ra, csr_bad_impl
	li a1, 0x88f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x88f
	jal ra, csr_bad_impl
	li a1, 0x890
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x890
	jal ra, csr_bad_impl
	li a1, 0x891
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x891
	jal ra, csr_bad_impl
	li a1, 0x892
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x892
	jal ra, csr_bad_impl
	li a1, 0x893
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x893
	jal ra, csr_bad_impl
	li a1, 0x894
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x894
	jal ra, csr_bad_impl
	li a1, 0x895
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x895
	jal ra, csr_bad_impl
	li a1, 0x896
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x896
	jal ra, csr_bad_impl
	li a1, 0x897
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x897
	jal ra, csr_bad_impl
	li a1, 0x898
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x898
	jal ra, csr_bad_impl
	li a1, 0x899
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x899
	jal ra, csr_bad_impl
	li a1, 0x89a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x89a
	jal ra, csr_bad_impl
	li a1, 0x89b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x89b
	jal ra, csr_bad_impl
	li a1, 0x89c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x89c
	jal ra, csr_bad_impl
	li a1, 0x89d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x89d
	jal ra, csr_bad_impl
	li a1, 0x89e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x89e
	jal ra, csr_bad_impl
	li a1, 0x89f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x89f
	jal ra, csr_bad_impl
	li a1, 0x8a0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8a0
	jal ra, csr_bad_impl
	li a1, 0x8a1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8a1
	jal ra, csr_bad_impl
	li a1, 0x8a2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8a2
	jal ra, csr_bad_impl
	li a1, 0x8a3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8a3
	jal ra, csr_bad_impl
	li a1, 0x8a4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8a4
	jal ra, csr_bad_impl
	li a1, 0x8a5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8a5
	jal ra, csr_bad_impl
	li a1, 0x8a6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8a6
	jal ra, csr_bad_impl
	li a1, 0x8a7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8a7
	jal ra, csr_bad_impl
	li a1, 0x8a8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8a8
	jal ra, csr_bad_impl
	li a1, 0x8a9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8a9
	jal ra, csr_bad_impl
	li a1, 0x8aa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8aa
	jal ra, csr_bad_impl
	li a1, 0x8ab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ab
	jal ra, csr_bad_impl
	li a1, 0x8ac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ac
	jal ra, csr_bad_impl
	li a1, 0x8ad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ad
	jal ra, csr_bad_impl
	li a1, 0x8ae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ae
	jal ra, csr_bad_impl
	li a1, 0x8af
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8af
	jal ra, csr_bad_impl
	li a1, 0x8b0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8b0
	jal ra, csr_bad_impl
	li a1, 0x8b1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8b1
	jal ra, csr_bad_impl
	li a1, 0x8b2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8b2
	jal ra, csr_bad_impl
	li a1, 0x8b3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8b3
	jal ra, csr_bad_impl
	li a1, 0x8b4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8b4
	jal ra, csr_bad_impl
	li a1, 0x8b5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8b5
	jal ra, csr_bad_impl
	li a1, 0x8b6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8b6
	jal ra, csr_bad_impl
	li a1, 0x8b7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8b7
	jal ra, csr_bad_impl
	li a1, 0x8b8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8b8
	jal ra, csr_bad_impl
	li a1, 0x8b9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8b9
	jal ra, csr_bad_impl
	li a1, 0x8ba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ba
	jal ra, csr_bad_impl
	li a1, 0x8bb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8bb
	jal ra, csr_bad_impl
	li a1, 0x8bc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8bc
	jal ra, csr_bad_impl
	li a1, 0x8bd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8bd
	jal ra, csr_bad_impl
	li a1, 0x8be
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8be
	jal ra, csr_bad_impl
	li a1, 0x8bf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8bf
	jal ra, csr_bad_impl
	li a1, 0x8c0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8c0
	jal ra, csr_bad_impl
	li a1, 0x8c1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8c1
	jal ra, csr_bad_impl
	li a1, 0x8c2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8c2
	jal ra, csr_bad_impl
	li a1, 0x8c3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8c3
	jal ra, csr_bad_impl
	li a1, 0x8c4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8c4
	jal ra, csr_bad_impl
	li a1, 0x8c5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8c5
	jal ra, csr_bad_impl
	li a1, 0x8c6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8c6
	jal ra, csr_bad_impl
	li a1, 0x8c7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8c7
	jal ra, csr_bad_impl
	li a1, 0x8c8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8c8
	jal ra, csr_bad_impl
	li a1, 0x8c9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8c9
	jal ra, csr_bad_impl
	li a1, 0x8ca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ca
	jal ra, csr_bad_impl
	li a1, 0x8cb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8cb
	jal ra, csr_bad_impl
	li a1, 0x8cc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8cc
	jal ra, csr_bad_impl
	li a1, 0x8cd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8cd
	jal ra, csr_bad_impl
	li a1, 0x8ce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ce
	jal ra, csr_bad_impl
	li a1, 0x8cf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8cf
	jal ra, csr_bad_impl
	li a1, 0x8d0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8d0
	jal ra, csr_bad_impl
	li a1, 0x8d1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8d1
	jal ra, csr_bad_impl
	li a1, 0x8d2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8d2
	jal ra, csr_bad_impl
	li a1, 0x8d3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8d3
	jal ra, csr_bad_impl
	li a1, 0x8d4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8d4
	jal ra, csr_bad_impl
	li a1, 0x8d5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8d5
	jal ra, csr_bad_impl
	li a1, 0x8d6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8d6
	jal ra, csr_bad_impl
	li a1, 0x8d7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8d7
	jal ra, csr_bad_impl
	li a1, 0x8d8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8d8
	jal ra, csr_bad_impl
	li a1, 0x8d9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8d9
	jal ra, csr_bad_impl
	li a1, 0x8da
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8da
	jal ra, csr_bad_impl
	li a1, 0x8db
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8db
	jal ra, csr_bad_impl
	li a1, 0x8dc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8dc
	jal ra, csr_bad_impl
	li a1, 0x8dd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8dd
	jal ra, csr_bad_impl
	li a1, 0x8de
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8de
	jal ra, csr_bad_impl
	li a1, 0x8df
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8df
	jal ra, csr_bad_impl
	li a1, 0x8e0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8e0
	jal ra, csr_bad_impl
	li a1, 0x8e1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8e1
	jal ra, csr_bad_impl
	li a1, 0x8e2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8e2
	jal ra, csr_bad_impl
	li a1, 0x8e3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8e3
	jal ra, csr_bad_impl
	li a1, 0x8e4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8e4
	jal ra, csr_bad_impl
	li a1, 0x8e5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8e5
	jal ra, csr_bad_impl
	li a1, 0x8e6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8e6
	jal ra, csr_bad_impl
	li a1, 0x8e7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8e7
	jal ra, csr_bad_impl
	li a1, 0x8e8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8e8
	jal ra, csr_bad_impl
	li a1, 0x8e9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8e9
	jal ra, csr_bad_impl
	li a1, 0x8ea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ea
	jal ra, csr_bad_impl
	li a1, 0x8eb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8eb
	jal ra, csr_bad_impl
	li a1, 0x8ec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ec
	jal ra, csr_bad_impl
	li a1, 0x8ed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ed
	jal ra, csr_bad_impl
	li a1, 0x8ee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ee
	jal ra, csr_bad_impl
	li a1, 0x8ef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ef
	jal ra, csr_bad_impl
	li a1, 0x8f0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8f0
	jal ra, csr_bad_impl
	li a1, 0x8f1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8f1
	jal ra, csr_bad_impl
	li a1, 0x8f2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8f2
	jal ra, csr_bad_impl
	li a1, 0x8f3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8f3
	jal ra, csr_bad_impl
	li a1, 0x8f4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8f4
	jal ra, csr_bad_impl
	li a1, 0x8f5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8f5
	jal ra, csr_bad_impl
	li a1, 0x8f6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8f6
	jal ra, csr_bad_impl
	li a1, 0x8f7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8f7
	jal ra, csr_bad_impl
	li a1, 0x8f8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8f8
	jal ra, csr_bad_impl
	li a1, 0x8f9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8f9
	jal ra, csr_bad_impl
	li a1, 0x8fa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8fa
	jal ra, csr_bad_impl
	li a1, 0x8fb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8fb
	jal ra, csr_bad_impl
	li a1, 0x8fc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8fc
	jal ra, csr_bad_impl
	li a1, 0x8fd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8fd
	jal ra, csr_bad_impl
	li a1, 0x8fe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8fe
	jal ra, csr_bad_impl
	li a1, 0x8ff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x8ff
	jal ra, csr_bad_impl
	li a1, 0x900
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x900
	jal ra, csr_bad_impl
	li a1, 0x901
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x901
	jal ra, csr_bad_impl
	li a1, 0x902
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x902
	jal ra, csr_bad_impl
	li a1, 0x903
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x903
	jal ra, csr_bad_impl
	li a1, 0x904
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x904
	jal ra, csr_bad_impl
	li a1, 0x905
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x905
	jal ra, csr_bad_impl
	li a1, 0x906
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x906
	jal ra, csr_bad_impl
	li a1, 0x907
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x907
	jal ra, csr_bad_impl
	li a1, 0x908
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x908
	jal ra, csr_bad_impl
	li a1, 0x909
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x909
	jal ra, csr_bad_impl
	li a1, 0x90a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x90a
	jal ra, csr_bad_impl
	li a1, 0x90b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x90b
	jal ra, csr_bad_impl
	li a1, 0x90c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x90c
	jal ra, csr_bad_impl
	li a1, 0x90d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x90d
	jal ra, csr_bad_impl
	li a1, 0x90e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x90e
	jal ra, csr_bad_impl
	li a1, 0x90f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x90f
	jal ra, csr_bad_impl
	li a1, 0x910
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x910
	jal ra, csr_bad_impl
	li a1, 0x911
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x911
	jal ra, csr_bad_impl
	li a1, 0x912
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x912
	jal ra, csr_bad_impl
	li a1, 0x913
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x913
	jal ra, csr_bad_impl
	li a1, 0x914
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x914
	jal ra, csr_bad_impl
	li a1, 0x915
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x915
	jal ra, csr_bad_impl
	li a1, 0x916
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x916
	jal ra, csr_bad_impl
	li a1, 0x917
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x917
	jal ra, csr_bad_impl
	li a1, 0x918
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x918
	jal ra, csr_bad_impl
	li a1, 0x919
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x919
	jal ra, csr_bad_impl
	li a1, 0x91a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x91a
	jal ra, csr_bad_impl
	li a1, 0x91b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x91b
	jal ra, csr_bad_impl
	li a1, 0x91c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x91c
	jal ra, csr_bad_impl
	li a1, 0x91d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x91d
	jal ra, csr_bad_impl
	li a1, 0x91e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x91e
	jal ra, csr_bad_impl
	li a1, 0x91f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x91f
	jal ra, csr_bad_impl
	li a1, 0x920
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x920
	jal ra, csr_bad_impl
	li a1, 0x921
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x921
	jal ra, csr_bad_impl
	li a1, 0x922
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x922
	jal ra, csr_bad_impl
	li a1, 0x923
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x923
	jal ra, csr_bad_impl
	li a1, 0x924
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x924
	jal ra, csr_bad_impl
	li a1, 0x925
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x925
	jal ra, csr_bad_impl
	li a1, 0x926
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x926
	jal ra, csr_bad_impl
	li a1, 0x927
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x927
	jal ra, csr_bad_impl
	li a1, 0x928
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x928
	jal ra, csr_bad_impl
	li a1, 0x929
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x929
	jal ra, csr_bad_impl
	li a1, 0x92a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x92a
	jal ra, csr_bad_impl
	li a1, 0x92b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x92b
	jal ra, csr_bad_impl
	li a1, 0x92c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x92c
	jal ra, csr_bad_impl
	li a1, 0x92d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x92d
	jal ra, csr_bad_impl
	li a1, 0x92e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x92e
	jal ra, csr_bad_impl
	li a1, 0x92f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x92f
	jal ra, csr_bad_impl
	li a1, 0x930
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x930
	jal ra, csr_bad_impl
	li a1, 0x931
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x931
	jal ra, csr_bad_impl
	li a1, 0x932
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x932
	jal ra, csr_bad_impl
	li a1, 0x933
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x933
	jal ra, csr_bad_impl
	li a1, 0x934
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x934
	jal ra, csr_bad_impl
	li a1, 0x935
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x935
	jal ra, csr_bad_impl
	li a1, 0x936
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x936
	jal ra, csr_bad_impl
	li a1, 0x937
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x937
	jal ra, csr_bad_impl
	li a1, 0x938
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x938
	jal ra, csr_bad_impl
	li a1, 0x939
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x939
	jal ra, csr_bad_impl
	li a1, 0x93a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x93a
	jal ra, csr_bad_impl
	li a1, 0x93b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x93b
	jal ra, csr_bad_impl
	li a1, 0x93c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x93c
	jal ra, csr_bad_impl
	li a1, 0x93d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x93d
	jal ra, csr_bad_impl
	li a1, 0x93e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x93e
	jal ra, csr_bad_impl
	li a1, 0x93f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x93f
	jal ra, csr_bad_impl
	li a1, 0x940
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x940
	jal ra, csr_bad_impl
	li a1, 0x941
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x941
	jal ra, csr_bad_impl
	li a1, 0x942
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x942
	jal ra, csr_bad_impl
	li a1, 0x943
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x943
	jal ra, csr_bad_impl
	li a1, 0x944
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x944
	jal ra, csr_bad_impl
	li a1, 0x945
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x945
	jal ra, csr_bad_impl
	li a1, 0x946
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x946
	jal ra, csr_bad_impl
	li a1, 0x947
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x947
	jal ra, csr_bad_impl
	li a1, 0x948
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x948
	jal ra, csr_bad_impl
	li a1, 0x949
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x949
	jal ra, csr_bad_impl
	li a1, 0x94a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x94a
	jal ra, csr_bad_impl
	li a1, 0x94b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x94b
	jal ra, csr_bad_impl
	li a1, 0x94c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x94c
	jal ra, csr_bad_impl
	li a1, 0x94d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x94d
	jal ra, csr_bad_impl
	li a1, 0x94e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x94e
	jal ra, csr_bad_impl
	li a1, 0x94f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x94f
	jal ra, csr_bad_impl
	li a1, 0x950
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x950
	jal ra, csr_bad_impl
	li a1, 0x951
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x951
	jal ra, csr_bad_impl
	li a1, 0x952
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x952
	jal ra, csr_bad_impl
	li a1, 0x953
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x953
	jal ra, csr_bad_impl
	li a1, 0x954
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x954
	jal ra, csr_bad_impl
	li a1, 0x955
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x955
	jal ra, csr_bad_impl
	li a1, 0x956
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x956
	jal ra, csr_bad_impl
	li a1, 0x957
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x957
	jal ra, csr_bad_impl
	li a1, 0x958
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x958
	jal ra, csr_bad_impl
	li a1, 0x959
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x959
	jal ra, csr_bad_impl
	li a1, 0x95a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x95a
	jal ra, csr_bad_impl
	li a1, 0x95b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x95b
	jal ra, csr_bad_impl
	li a1, 0x95c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x95c
	jal ra, csr_bad_impl
	li a1, 0x95d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x95d
	jal ra, csr_bad_impl
	li a1, 0x95e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x95e
	jal ra, csr_bad_impl
	li a1, 0x95f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x95f
	jal ra, csr_bad_impl
	li a1, 0x960
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x960
	jal ra, csr_bad_impl
	li a1, 0x961
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x961
	jal ra, csr_bad_impl
	li a1, 0x962
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x962
	jal ra, csr_bad_impl
	li a1, 0x963
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x963
	jal ra, csr_bad_impl
	li a1, 0x964
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x964
	jal ra, csr_bad_impl
	li a1, 0x965
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x965
	jal ra, csr_bad_impl
	li a1, 0x966
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x966
	jal ra, csr_bad_impl
	li a1, 0x967
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x967
	jal ra, csr_bad_impl
	li a1, 0x968
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x968
	jal ra, csr_bad_impl
	li a1, 0x969
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x969
	jal ra, csr_bad_impl
	li a1, 0x96a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x96a
	jal ra, csr_bad_impl
	li a1, 0x96b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x96b
	jal ra, csr_bad_impl
	li a1, 0x96c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x96c
	jal ra, csr_bad_impl
	li a1, 0x96d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x96d
	jal ra, csr_bad_impl
	li a1, 0x96e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x96e
	jal ra, csr_bad_impl
	li a1, 0x96f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x96f
	jal ra, csr_bad_impl
	li a1, 0x970
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x970
	jal ra, csr_bad_impl
	li a1, 0x971
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x971
	jal ra, csr_bad_impl
	li a1, 0x972
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x972
	jal ra, csr_bad_impl
	li a1, 0x973
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x973
	jal ra, csr_bad_impl
	li a1, 0x974
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x974
	jal ra, csr_bad_impl
	li a1, 0x975
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x975
	jal ra, csr_bad_impl
	li a1, 0x976
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x976
	jal ra, csr_bad_impl
	li a1, 0x977
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x977
	jal ra, csr_bad_impl
	li a1, 0x978
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x978
	jal ra, csr_bad_impl
	li a1, 0x979
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x979
	jal ra, csr_bad_impl
	li a1, 0x97a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x97a
	jal ra, csr_bad_impl
	li a1, 0x97b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x97b
	jal ra, csr_bad_impl
	li a1, 0x97c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x97c
	jal ra, csr_bad_impl
	li a1, 0x97d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x97d
	jal ra, csr_bad_impl
	li a1, 0x97e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x97e
	jal ra, csr_bad_impl
	li a1, 0x97f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x97f
	jal ra, csr_bad_impl
	li a1, 0x980
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x980
	jal ra, csr_bad_impl
	li a1, 0x981
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x981
	jal ra, csr_bad_impl
	li a1, 0x982
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x982
	jal ra, csr_bad_impl
	li a1, 0x983
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x983
	jal ra, csr_bad_impl
	li a1, 0x984
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x984
	jal ra, csr_bad_impl
	li a1, 0x985
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x985
	jal ra, csr_bad_impl
	li a1, 0x986
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x986
	jal ra, csr_bad_impl
	li a1, 0x987
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x987
	jal ra, csr_bad_impl
	li a1, 0x988
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x988
	jal ra, csr_bad_impl
	li a1, 0x989
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x989
	jal ra, csr_bad_impl
	li a1, 0x98a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x98a
	jal ra, csr_bad_impl
	li a1, 0x98b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x98b
	jal ra, csr_bad_impl
	li a1, 0x98c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x98c
	jal ra, csr_bad_impl
	li a1, 0x98d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x98d
	jal ra, csr_bad_impl
	li a1, 0x98e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x98e
	jal ra, csr_bad_impl
	li a1, 0x98f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x98f
	jal ra, csr_bad_impl
	li a1, 0x990
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x990
	jal ra, csr_bad_impl
	li a1, 0x991
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x991
	jal ra, csr_bad_impl
	li a1, 0x992
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x992
	jal ra, csr_bad_impl
	li a1, 0x993
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x993
	jal ra, csr_bad_impl
	li a1, 0x994
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x994
	jal ra, csr_bad_impl
	li a1, 0x995
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x995
	jal ra, csr_bad_impl
	li a1, 0x996
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x996
	jal ra, csr_bad_impl
	li a1, 0x997
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x997
	jal ra, csr_bad_impl
	li a1, 0x998
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x998
	jal ra, csr_bad_impl
	li a1, 0x999
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x999
	jal ra, csr_bad_impl
	li a1, 0x99a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x99a
	jal ra, csr_bad_impl
	li a1, 0x99b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x99b
	jal ra, csr_bad_impl
	li a1, 0x99c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x99c
	jal ra, csr_bad_impl
	li a1, 0x99d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x99d
	jal ra, csr_bad_impl
	li a1, 0x99e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x99e
	jal ra, csr_bad_impl
	li a1, 0x99f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x99f
	jal ra, csr_bad_impl
	li a1, 0x9a0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9a0
	jal ra, csr_bad_impl
	li a1, 0x9a1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9a1
	jal ra, csr_bad_impl
	li a1, 0x9a2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9a2
	jal ra, csr_bad_impl
	li a1, 0x9a3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9a3
	jal ra, csr_bad_impl
	li a1, 0x9a4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9a4
	jal ra, csr_bad_impl
	li a1, 0x9a5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9a5
	jal ra, csr_bad_impl
	li a1, 0x9a6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9a6
	jal ra, csr_bad_impl
	li a1, 0x9a7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9a7
	jal ra, csr_bad_impl
	li a1, 0x9a8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9a8
	jal ra, csr_bad_impl
	li a1, 0x9a9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9a9
	jal ra, csr_bad_impl
	li a1, 0x9aa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9aa
	jal ra, csr_bad_impl
	li a1, 0x9ab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ab
	jal ra, csr_bad_impl
	li a1, 0x9ac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ac
	jal ra, csr_bad_impl
	li a1, 0x9ad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ad
	jal ra, csr_bad_impl
	li a1, 0x9ae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ae
	jal ra, csr_bad_impl
	li a1, 0x9af
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9af
	jal ra, csr_bad_impl
	li a1, 0x9b0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9b0
	jal ra, csr_bad_impl
	li a1, 0x9b1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9b1
	jal ra, csr_bad_impl
	li a1, 0x9b2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9b2
	jal ra, csr_bad_impl
	li a1, 0x9b3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9b3
	jal ra, csr_bad_impl
	li a1, 0x9b4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9b4
	jal ra, csr_bad_impl
	li a1, 0x9b5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9b5
	jal ra, csr_bad_impl
	li a1, 0x9b6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9b6
	jal ra, csr_bad_impl
	li a1, 0x9b7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9b7
	jal ra, csr_bad_impl
	li a1, 0x9b8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9b8
	jal ra, csr_bad_impl
	li a1, 0x9b9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9b9
	jal ra, csr_bad_impl
	li a1, 0x9ba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ba
	jal ra, csr_bad_impl
	li a1, 0x9bb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9bb
	jal ra, csr_bad_impl
	li a1, 0x9bc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9bc
	jal ra, csr_bad_impl
	li a1, 0x9bd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9bd
	jal ra, csr_bad_impl
	li a1, 0x9be
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9be
	jal ra, csr_bad_impl
	li a1, 0x9bf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9bf
	jal ra, csr_bad_impl
	li a1, 0x9c0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9c0
	jal ra, csr_bad_impl
	li a1, 0x9c1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9c1
	jal ra, csr_bad_impl
	li a1, 0x9c2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9c2
	jal ra, csr_bad_impl
	li a1, 0x9c3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9c3
	jal ra, csr_bad_impl
	li a1, 0x9c4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9c4
	jal ra, csr_bad_impl
	li a1, 0x9c5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9c5
	jal ra, csr_bad_impl
	li a1, 0x9c6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9c6
	jal ra, csr_bad_impl
	li a1, 0x9c7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9c7
	jal ra, csr_bad_impl
	li a1, 0x9c8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9c8
	jal ra, csr_bad_impl
	li a1, 0x9c9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9c9
	jal ra, csr_bad_impl
	li a1, 0x9ca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ca
	jal ra, csr_bad_impl
	li a1, 0x9cb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9cb
	jal ra, csr_bad_impl
	li a1, 0x9cc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9cc
	jal ra, csr_bad_impl
	li a1, 0x9cd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9cd
	jal ra, csr_bad_impl
	li a1, 0x9ce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ce
	jal ra, csr_bad_impl
	li a1, 0x9cf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9cf
	jal ra, csr_bad_impl
	li a1, 0x9d0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9d0
	jal ra, csr_bad_impl
	li a1, 0x9d1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9d1
	jal ra, csr_bad_impl
	li a1, 0x9d2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9d2
	jal ra, csr_bad_impl
	li a1, 0x9d3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9d3
	jal ra, csr_bad_impl
	li a1, 0x9d4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9d4
	jal ra, csr_bad_impl
	li a1, 0x9d5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9d5
	jal ra, csr_bad_impl
	li a1, 0x9d6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9d6
	jal ra, csr_bad_impl
	li a1, 0x9d7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9d7
	jal ra, csr_bad_impl
	li a1, 0x9d8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9d8
	jal ra, csr_bad_impl
	li a1, 0x9d9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9d9
	jal ra, csr_bad_impl
	li a1, 0x9da
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9da
	jal ra, csr_bad_impl
	li a1, 0x9db
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9db
	jal ra, csr_bad_impl
	li a1, 0x9dc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9dc
	jal ra, csr_bad_impl
	li a1, 0x9dd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9dd
	jal ra, csr_bad_impl
	li a1, 0x9de
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9de
	jal ra, csr_bad_impl
	li a1, 0x9df
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9df
	jal ra, csr_bad_impl
	li a1, 0x9e0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9e0
	jal ra, csr_bad_impl
	li a1, 0x9e1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9e1
	jal ra, csr_bad_impl
	li a1, 0x9e2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9e2
	jal ra, csr_bad_impl
	li a1, 0x9e3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9e3
	jal ra, csr_bad_impl
	li a1, 0x9e4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9e4
	jal ra, csr_bad_impl
	li a1, 0x9e5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9e5
	jal ra, csr_bad_impl
	li a1, 0x9e6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9e6
	jal ra, csr_bad_impl
	li a1, 0x9e7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9e7
	jal ra, csr_bad_impl
	li a1, 0x9e8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9e8
	jal ra, csr_bad_impl
	li a1, 0x9e9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9e9
	jal ra, csr_bad_impl
	li a1, 0x9ea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ea
	jal ra, csr_bad_impl
	li a1, 0x9eb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9eb
	jal ra, csr_bad_impl
	li a1, 0x9ec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ec
	jal ra, csr_bad_impl
	li a1, 0x9ed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ed
	jal ra, csr_bad_impl
	li a1, 0x9ee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ee
	jal ra, csr_bad_impl
	li a1, 0x9ef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ef
	jal ra, csr_bad_impl
	li a1, 0x9f0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9f0
	jal ra, csr_bad_impl
	li a1, 0x9f1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9f1
	jal ra, csr_bad_impl
	li a1, 0x9f2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9f2
	jal ra, csr_bad_impl
	li a1, 0x9f3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9f3
	jal ra, csr_bad_impl
	li a1, 0x9f4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9f4
	jal ra, csr_bad_impl
	li a1, 0x9f5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9f5
	jal ra, csr_bad_impl
	li a1, 0x9f6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9f6
	jal ra, csr_bad_impl
	li a1, 0x9f7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9f7
	jal ra, csr_bad_impl
	li a1, 0x9f8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9f8
	jal ra, csr_bad_impl
	li a1, 0x9f9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9f9
	jal ra, csr_bad_impl
	li a1, 0x9fa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9fa
	jal ra, csr_bad_impl
	li a1, 0x9fb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9fb
	jal ra, csr_bad_impl
	li a1, 0x9fc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9fc
	jal ra, csr_bad_impl
	li a1, 0x9fd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9fd
	jal ra, csr_bad_impl
	li a1, 0x9fe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9fe
	jal ra, csr_bad_impl
	li a1, 0x9ff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0x9ff
	jal ra, csr_bad_impl
	li a1, 0xa00
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa00
	jal ra, csr_bad_impl
	li a1, 0xa01
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa01
	jal ra, csr_bad_impl
	li a1, 0xa02
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa02
	jal ra, csr_bad_impl
	li a1, 0xa03
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa03
	jal ra, csr_bad_impl
	li a1, 0xa04
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa04
	jal ra, csr_bad_impl
	li a1, 0xa05
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa05
	jal ra, csr_bad_impl
	li a1, 0xa06
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa06
	jal ra, csr_bad_impl
	li a1, 0xa07
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa07
	jal ra, csr_bad_impl
	li a1, 0xa08
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa08
	jal ra, csr_bad_impl
	li a1, 0xa09
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa09
	jal ra, csr_bad_impl
	li a1, 0xa0a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa0a
	jal ra, csr_bad_impl
	li a1, 0xa0b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa0b
	jal ra, csr_bad_impl
	li a1, 0xa0c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa0c
	jal ra, csr_bad_impl
	li a1, 0xa0d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa0d
	jal ra, csr_bad_impl
	li a1, 0xa0e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa0e
	jal ra, csr_bad_impl
	li a1, 0xa0f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa0f
	jal ra, csr_bad_impl
	li a1, 0xa10
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa10
	jal ra, csr_bad_impl
	li a1, 0xa11
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa11
	jal ra, csr_bad_impl
	li a1, 0xa12
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa12
	jal ra, csr_bad_impl
	li a1, 0xa13
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa13
	jal ra, csr_bad_impl
	li a1, 0xa14
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa14
	jal ra, csr_bad_impl
	li a1, 0xa15
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa15
	jal ra, csr_bad_impl
	li a1, 0xa16
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa16
	jal ra, csr_bad_impl
	li a1, 0xa17
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa17
	jal ra, csr_bad_impl
	li a1, 0xa18
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa18
	jal ra, csr_bad_impl
	li a1, 0xa19
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa19
	jal ra, csr_bad_impl
	li a1, 0xa1a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa1a
	jal ra, csr_bad_impl
	li a1, 0xa1b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa1b
	jal ra, csr_bad_impl
	li a1, 0xa1c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa1c
	jal ra, csr_bad_impl
	li a1, 0xa1d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa1d
	jal ra, csr_bad_impl
	li a1, 0xa1e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa1e
	jal ra, csr_bad_impl
	li a1, 0xa1f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa1f
	jal ra, csr_bad_impl
	li a1, 0xa20
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa20
	jal ra, csr_bad_impl
	li a1, 0xa21
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa21
	jal ra, csr_bad_impl
	li a1, 0xa22
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa22
	jal ra, csr_bad_impl
	li a1, 0xa23
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa23
	jal ra, csr_bad_impl
	li a1, 0xa24
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa24
	jal ra, csr_bad_impl
	li a1, 0xa25
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa25
	jal ra, csr_bad_impl
	li a1, 0xa26
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa26
	jal ra, csr_bad_impl
	li a1, 0xa27
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa27
	jal ra, csr_bad_impl
	li a1, 0xa28
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa28
	jal ra, csr_bad_impl
	li a1, 0xa29
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa29
	jal ra, csr_bad_impl
	li a1, 0xa2a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa2a
	jal ra, csr_bad_impl
	li a1, 0xa2b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa2b
	jal ra, csr_bad_impl
	li a1, 0xa2c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa2c
	jal ra, csr_bad_impl
	li a1, 0xa2d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa2d
	jal ra, csr_bad_impl
	li a1, 0xa2e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa2e
	jal ra, csr_bad_impl
	li a1, 0xa2f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa2f
	jal ra, csr_bad_impl
	li a1, 0xa30
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa30
	jal ra, csr_bad_impl
	li a1, 0xa31
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa31
	jal ra, csr_bad_impl
	li a1, 0xa32
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa32
	jal ra, csr_bad_impl
	li a1, 0xa33
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa33
	jal ra, csr_bad_impl
	li a1, 0xa34
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa34
	jal ra, csr_bad_impl
	li a1, 0xa35
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa35
	jal ra, csr_bad_impl
	li a1, 0xa36
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa36
	jal ra, csr_bad_impl
	li a1, 0xa37
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa37
	jal ra, csr_bad_impl
	li a1, 0xa38
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa38
	jal ra, csr_bad_impl
	li a1, 0xa39
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa39
	jal ra, csr_bad_impl
	li a1, 0xa3a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa3a
	jal ra, csr_bad_impl
	li a1, 0xa3b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa3b
	jal ra, csr_bad_impl
	li a1, 0xa3c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa3c
	jal ra, csr_bad_impl
	li a1, 0xa3d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa3d
	jal ra, csr_bad_impl
	li a1, 0xa3e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa3e
	jal ra, csr_bad_impl
	li a1, 0xa3f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa3f
	jal ra, csr_bad_impl
	li a1, 0xa40
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa40
	jal ra, csr_bad_impl
	li a1, 0xa41
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa41
	jal ra, csr_bad_impl
	li a1, 0xa42
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa42
	jal ra, csr_bad_impl
	li a1, 0xa43
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa43
	jal ra, csr_bad_impl
	li a1, 0xa44
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa44
	jal ra, csr_bad_impl
	li a1, 0xa45
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa45
	jal ra, csr_bad_impl
	li a1, 0xa46
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa46
	jal ra, csr_bad_impl
	li a1, 0xa47
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa47
	jal ra, csr_bad_impl
	li a1, 0xa48
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa48
	jal ra, csr_bad_impl
	li a1, 0xa49
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa49
	jal ra, csr_bad_impl
	li a1, 0xa4a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa4a
	jal ra, csr_bad_impl
	li a1, 0xa4b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa4b
	jal ra, csr_bad_impl
	li a1, 0xa4c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa4c
	jal ra, csr_bad_impl
	li a1, 0xa4d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa4d
	jal ra, csr_bad_impl
	li a1, 0xa4e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa4e
	jal ra, csr_bad_impl
	li a1, 0xa4f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa4f
	jal ra, csr_bad_impl
	li a1, 0xa50
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa50
	jal ra, csr_bad_impl
	li a1, 0xa51
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa51
	jal ra, csr_bad_impl
	li a1, 0xa52
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa52
	jal ra, csr_bad_impl
	li a1, 0xa53
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa53
	jal ra, csr_bad_impl
	li a1, 0xa54
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa54
	jal ra, csr_bad_impl
	li a1, 0xa55
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa55
	jal ra, csr_bad_impl
	li a1, 0xa56
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa56
	jal ra, csr_bad_impl
	li a1, 0xa57
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa57
	jal ra, csr_bad_impl
	li a1, 0xa58
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa58
	jal ra, csr_bad_impl
	li a1, 0xa59
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa59
	jal ra, csr_bad_impl
	li a1, 0xa5a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa5a
	jal ra, csr_bad_impl
	li a1, 0xa5b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa5b
	jal ra, csr_bad_impl
	li a1, 0xa5c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa5c
	jal ra, csr_bad_impl
	li a1, 0xa5d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa5d
	jal ra, csr_bad_impl
	li a1, 0xa5e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa5e
	jal ra, csr_bad_impl
	li a1, 0xa5f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa5f
	jal ra, csr_bad_impl
	li a1, 0xa60
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa60
	jal ra, csr_bad_impl
	li a1, 0xa61
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa61
	jal ra, csr_bad_impl
	li a1, 0xa62
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa62
	jal ra, csr_bad_impl
	li a1, 0xa63
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa63
	jal ra, csr_bad_impl
	li a1, 0xa64
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa64
	jal ra, csr_bad_impl
	li a1, 0xa65
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa65
	jal ra, csr_bad_impl
	li a1, 0xa66
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa66
	jal ra, csr_bad_impl
	li a1, 0xa67
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa67
	jal ra, csr_bad_impl
	li a1, 0xa68
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa68
	jal ra, csr_bad_impl
	li a1, 0xa69
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa69
	jal ra, csr_bad_impl
	li a1, 0xa6a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa6a
	jal ra, csr_bad_impl
	li a1, 0xa6b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa6b
	jal ra, csr_bad_impl
	li a1, 0xa6c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa6c
	jal ra, csr_bad_impl
	li a1, 0xa6d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa6d
	jal ra, csr_bad_impl
	li a1, 0xa6e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa6e
	jal ra, csr_bad_impl
	li a1, 0xa6f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa6f
	jal ra, csr_bad_impl
	li a1, 0xa70
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa70
	jal ra, csr_bad_impl
	li a1, 0xa71
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa71
	jal ra, csr_bad_impl
	li a1, 0xa72
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa72
	jal ra, csr_bad_impl
	li a1, 0xa73
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa73
	jal ra, csr_bad_impl
	li a1, 0xa74
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa74
	jal ra, csr_bad_impl
	li a1, 0xa75
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa75
	jal ra, csr_bad_impl
	li a1, 0xa76
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa76
	jal ra, csr_bad_impl
	li a1, 0xa77
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa77
	jal ra, csr_bad_impl
	li a1, 0xa78
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa78
	jal ra, csr_bad_impl
	li a1, 0xa79
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa79
	jal ra, csr_bad_impl
	li a1, 0xa7a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa7a
	jal ra, csr_bad_impl
	li a1, 0xa7b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa7b
	jal ra, csr_bad_impl
	li a1, 0xa7c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa7c
	jal ra, csr_bad_impl
	li a1, 0xa7d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa7d
	jal ra, csr_bad_impl
	li a1, 0xa7e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa7e
	jal ra, csr_bad_impl
	li a1, 0xa7f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa7f
	jal ra, csr_bad_impl
	li a1, 0xa80
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa80
	jal ra, csr_bad_impl
	li a1, 0xa81
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa81
	jal ra, csr_bad_impl
	li a1, 0xa82
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa82
	jal ra, csr_bad_impl
	li a1, 0xa83
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa83
	jal ra, csr_bad_impl
	li a1, 0xa84
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa84
	jal ra, csr_bad_impl
	li a1, 0xa85
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa85
	jal ra, csr_bad_impl
	li a1, 0xa86
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa86
	jal ra, csr_bad_impl
	li a1, 0xa87
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa87
	jal ra, csr_bad_impl
	li a1, 0xa88
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa88
	jal ra, csr_bad_impl
	li a1, 0xa89
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa89
	jal ra, csr_bad_impl
	li a1, 0xa8a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa8a
	jal ra, csr_bad_impl
	li a1, 0xa8b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa8b
	jal ra, csr_bad_impl
	li a1, 0xa8c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa8c
	jal ra, csr_bad_impl
	li a1, 0xa8d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa8d
	jal ra, csr_bad_impl
	li a1, 0xa8e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa8e
	jal ra, csr_bad_impl
	li a1, 0xa8f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa8f
	jal ra, csr_bad_impl
	li a1, 0xa90
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa90
	jal ra, csr_bad_impl
	li a1, 0xa91
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa91
	jal ra, csr_bad_impl
	li a1, 0xa92
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa92
	jal ra, csr_bad_impl
	li a1, 0xa93
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa93
	jal ra, csr_bad_impl
	li a1, 0xa94
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa94
	jal ra, csr_bad_impl
	li a1, 0xa95
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa95
	jal ra, csr_bad_impl
	li a1, 0xa96
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa96
	jal ra, csr_bad_impl
	li a1, 0xa97
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa97
	jal ra, csr_bad_impl
	li a1, 0xa98
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa98
	jal ra, csr_bad_impl
	li a1, 0xa99
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa99
	jal ra, csr_bad_impl
	li a1, 0xa9a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa9a
	jal ra, csr_bad_impl
	li a1, 0xa9b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa9b
	jal ra, csr_bad_impl
	li a1, 0xa9c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa9c
	jal ra, csr_bad_impl
	li a1, 0xa9d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa9d
	jal ra, csr_bad_impl
	li a1, 0xa9e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa9e
	jal ra, csr_bad_impl
	li a1, 0xa9f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xa9f
	jal ra, csr_bad_impl
	li a1, 0xaa0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaa0
	jal ra, csr_bad_impl
	li a1, 0xaa1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaa1
	jal ra, csr_bad_impl
	li a1, 0xaa2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaa2
	jal ra, csr_bad_impl
	li a1, 0xaa3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaa3
	jal ra, csr_bad_impl
	li a1, 0xaa4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaa4
	jal ra, csr_bad_impl
	li a1, 0xaa5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaa5
	jal ra, csr_bad_impl
	li a1, 0xaa6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaa6
	jal ra, csr_bad_impl
	li a1, 0xaa7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaa7
	jal ra, csr_bad_impl
	li a1, 0xaa8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaa8
	jal ra, csr_bad_impl
	li a1, 0xaa9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaa9
	jal ra, csr_bad_impl
	li a1, 0xaaa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaaa
	jal ra, csr_bad_impl
	li a1, 0xaab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaab
	jal ra, csr_bad_impl
	li a1, 0xaac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaac
	jal ra, csr_bad_impl
	li a1, 0xaad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaad
	jal ra, csr_bad_impl
	li a1, 0xaae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaae
	jal ra, csr_bad_impl
	li a1, 0xaaf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaaf
	jal ra, csr_bad_impl
	li a1, 0xab0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xab0
	jal ra, csr_bad_impl
	li a1, 0xab1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xab1
	jal ra, csr_bad_impl
	li a1, 0xab2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xab2
	jal ra, csr_bad_impl
	li a1, 0xab3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xab3
	jal ra, csr_bad_impl
	li a1, 0xab4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xab4
	jal ra, csr_bad_impl
	li a1, 0xab5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xab5
	jal ra, csr_bad_impl
	li a1, 0xab6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xab6
	jal ra, csr_bad_impl
	li a1, 0xab7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xab7
	jal ra, csr_bad_impl
	li a1, 0xab8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xab8
	jal ra, csr_bad_impl
	li a1, 0xab9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xab9
	jal ra, csr_bad_impl
	li a1, 0xaba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaba
	jal ra, csr_bad_impl
	li a1, 0xabb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xabb
	jal ra, csr_bad_impl
	li a1, 0xabc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xabc
	jal ra, csr_bad_impl
	li a1, 0xabd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xabd
	jal ra, csr_bad_impl
	li a1, 0xabe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xabe
	jal ra, csr_bad_impl
	li a1, 0xabf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xabf
	jal ra, csr_bad_impl
	li a1, 0xac0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xac0
	jal ra, csr_bad_impl
	li a1, 0xac1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xac1
	jal ra, csr_bad_impl
	li a1, 0xac2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xac2
	jal ra, csr_bad_impl
	li a1, 0xac3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xac3
	jal ra, csr_bad_impl
	li a1, 0xac4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xac4
	jal ra, csr_bad_impl
	li a1, 0xac5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xac5
	jal ra, csr_bad_impl
	li a1, 0xac6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xac6
	jal ra, csr_bad_impl
	li a1, 0xac7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xac7
	jal ra, csr_bad_impl
	li a1, 0xac8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xac8
	jal ra, csr_bad_impl
	li a1, 0xac9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xac9
	jal ra, csr_bad_impl
	li a1, 0xaca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaca
	jal ra, csr_bad_impl
	li a1, 0xacb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xacb
	jal ra, csr_bad_impl
	li a1, 0xacc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xacc
	jal ra, csr_bad_impl
	li a1, 0xacd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xacd
	jal ra, csr_bad_impl
	li a1, 0xace
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xace
	jal ra, csr_bad_impl
	li a1, 0xacf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xacf
	jal ra, csr_bad_impl
	li a1, 0xad0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xad0
	jal ra, csr_bad_impl
	li a1, 0xad1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xad1
	jal ra, csr_bad_impl
	li a1, 0xad2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xad2
	jal ra, csr_bad_impl
	li a1, 0xad3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xad3
	jal ra, csr_bad_impl
	li a1, 0xad4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xad4
	jal ra, csr_bad_impl
	li a1, 0xad5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xad5
	jal ra, csr_bad_impl
	li a1, 0xad6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xad6
	jal ra, csr_bad_impl
	li a1, 0xad7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xad7
	jal ra, csr_bad_impl
	li a1, 0xad8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xad8
	jal ra, csr_bad_impl
	li a1, 0xad9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xad9
	jal ra, csr_bad_impl
	li a1, 0xada
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xada
	jal ra, csr_bad_impl
	li a1, 0xadb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xadb
	jal ra, csr_bad_impl
	li a1, 0xadc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xadc
	jal ra, csr_bad_impl
	li a1, 0xadd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xadd
	jal ra, csr_bad_impl
	li a1, 0xade
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xade
	jal ra, csr_bad_impl
	li a1, 0xadf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xadf
	jal ra, csr_bad_impl
	li a1, 0xae0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xae0
	jal ra, csr_bad_impl
	li a1, 0xae1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xae1
	jal ra, csr_bad_impl
	li a1, 0xae2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xae2
	jal ra, csr_bad_impl
	li a1, 0xae3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xae3
	jal ra, csr_bad_impl
	li a1, 0xae4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xae4
	jal ra, csr_bad_impl
	li a1, 0xae5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xae5
	jal ra, csr_bad_impl
	li a1, 0xae6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xae6
	jal ra, csr_bad_impl
	li a1, 0xae7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xae7
	jal ra, csr_bad_impl
	li a1, 0xae8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xae8
	jal ra, csr_bad_impl
	li a1, 0xae9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xae9
	jal ra, csr_bad_impl
	li a1, 0xaea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaea
	jal ra, csr_bad_impl
	li a1, 0xaeb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaeb
	jal ra, csr_bad_impl
	li a1, 0xaec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaec
	jal ra, csr_bad_impl
	li a1, 0xaed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaed
	jal ra, csr_bad_impl
	li a1, 0xaee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaee
	jal ra, csr_bad_impl
	li a1, 0xaef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaef
	jal ra, csr_bad_impl
	li a1, 0xaf0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaf0
	jal ra, csr_bad_impl
	li a1, 0xaf1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaf1
	jal ra, csr_bad_impl
	li a1, 0xaf2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaf2
	jal ra, csr_bad_impl
	li a1, 0xaf3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaf3
	jal ra, csr_bad_impl
	li a1, 0xaf4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaf4
	jal ra, csr_bad_impl
	li a1, 0xaf5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaf5
	jal ra, csr_bad_impl
	li a1, 0xaf6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaf6
	jal ra, csr_bad_impl
	li a1, 0xaf7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaf7
	jal ra, csr_bad_impl
	li a1, 0xaf8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaf8
	jal ra, csr_bad_impl
	li a1, 0xaf9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaf9
	jal ra, csr_bad_impl
	li a1, 0xafa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xafa
	jal ra, csr_bad_impl
	li a1, 0xafb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xafb
	jal ra, csr_bad_impl
	li a1, 0xafc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xafc
	jal ra, csr_bad_impl
	li a1, 0xafd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xafd
	jal ra, csr_bad_impl
	li a1, 0xafe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xafe
	jal ra, csr_bad_impl
	li a1, 0xaff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xaff
	jal ra, csr_bad_impl
	li a1, 0xb01
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb01
	jal ra, csr_bad_impl
	li a1, 0xb0d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb0d
	jal ra, csr_bad_impl
	li a1, 0xb0e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb0e
	jal ra, csr_bad_impl
	li a1, 0xb0f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb0f
	jal ra, csr_bad_impl
	li a1, 0xb10
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb10
	jal ra, csr_bad_impl
	li a1, 0xb11
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb11
	jal ra, csr_bad_impl
	li a1, 0xb12
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb12
	jal ra, csr_bad_impl
	li a1, 0xb13
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb13
	jal ra, csr_bad_impl
	li a1, 0xb14
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb14
	jal ra, csr_bad_impl
	li a1, 0xb15
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb15
	jal ra, csr_bad_impl
	li a1, 0xb16
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb16
	jal ra, csr_bad_impl
	li a1, 0xb17
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb17
	jal ra, csr_bad_impl
	li a1, 0xb18
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb18
	jal ra, csr_bad_impl
	li a1, 0xb19
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb19
	jal ra, csr_bad_impl
	li a1, 0xb1a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb1a
	jal ra, csr_bad_impl
	li a1, 0xb1b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb1b
	jal ra, csr_bad_impl
	li a1, 0xb1c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb1c
	jal ra, csr_bad_impl
	li a1, 0xb1d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb1d
	jal ra, csr_bad_impl
	li a1, 0xb1e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb1e
	jal ra, csr_bad_impl
	li a1, 0xb1f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb1f
	jal ra, csr_bad_impl
	li a1, 0xb20
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb20
	jal ra, csr_bad_impl
	li a1, 0xb21
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb21
	jal ra, csr_bad_impl
	li a1, 0xb22
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb22
	jal ra, csr_bad_impl
	li a1, 0xb23
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb23
	jal ra, csr_bad_impl
	li a1, 0xb24
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb24
	jal ra, csr_bad_impl
	li a1, 0xb25
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb25
	jal ra, csr_bad_impl
	li a1, 0xb26
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb26
	jal ra, csr_bad_impl
	li a1, 0xb27
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb27
	jal ra, csr_bad_impl
	li a1, 0xb28
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb28
	jal ra, csr_bad_impl
	li a1, 0xb29
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb29
	jal ra, csr_bad_impl
	li a1, 0xb2a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb2a
	jal ra, csr_bad_impl
	li a1, 0xb2b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb2b
	jal ra, csr_bad_impl
	li a1, 0xb2c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb2c
	jal ra, csr_bad_impl
	li a1, 0xb2d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb2d
	jal ra, csr_bad_impl
	li a1, 0xb2e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb2e
	jal ra, csr_bad_impl
	li a1, 0xb2f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb2f
	jal ra, csr_bad_impl
	li a1, 0xb30
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb30
	jal ra, csr_bad_impl
	li a1, 0xb31
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb31
	jal ra, csr_bad_impl
	li a1, 0xb32
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb32
	jal ra, csr_bad_impl
	li a1, 0xb33
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb33
	jal ra, csr_bad_impl
	li a1, 0xb34
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb34
	jal ra, csr_bad_impl
	li a1, 0xb35
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb35
	jal ra, csr_bad_impl
	li a1, 0xb36
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb36
	jal ra, csr_bad_impl
	li a1, 0xb37
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb37
	jal ra, csr_bad_impl
	li a1, 0xb38
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb38
	jal ra, csr_bad_impl
	li a1, 0xb39
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb39
	jal ra, csr_bad_impl
	li a1, 0xb3a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb3a
	jal ra, csr_bad_impl
	li a1, 0xb3b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb3b
	jal ra, csr_bad_impl
	li a1, 0xb3c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb3c
	jal ra, csr_bad_impl
	li a1, 0xb3d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb3d
	jal ra, csr_bad_impl
	li a1, 0xb3e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb3e
	jal ra, csr_bad_impl
	li a1, 0xb3f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb3f
	jal ra, csr_bad_impl
	li a1, 0xb40
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb40
	jal ra, csr_bad_impl
	li a1, 0xb41
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb41
	jal ra, csr_bad_impl
	li a1, 0xb42
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb42
	jal ra, csr_bad_impl
	li a1, 0xb43
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb43
	jal ra, csr_bad_impl
	li a1, 0xb44
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb44
	jal ra, csr_bad_impl
	li a1, 0xb45
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb45
	jal ra, csr_bad_impl
	li a1, 0xb46
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb46
	jal ra, csr_bad_impl
	li a1, 0xb47
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb47
	jal ra, csr_bad_impl
	li a1, 0xb48
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb48
	jal ra, csr_bad_impl
	li a1, 0xb49
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb49
	jal ra, csr_bad_impl
	li a1, 0xb4a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb4a
	jal ra, csr_bad_impl
	li a1, 0xb4b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb4b
	jal ra, csr_bad_impl
	li a1, 0xb4c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb4c
	jal ra, csr_bad_impl
	li a1, 0xb4d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb4d
	jal ra, csr_bad_impl
	li a1, 0xb4e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb4e
	jal ra, csr_bad_impl
	li a1, 0xb4f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb4f
	jal ra, csr_bad_impl
	li a1, 0xb50
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb50
	jal ra, csr_bad_impl
	li a1, 0xb51
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb51
	jal ra, csr_bad_impl
	li a1, 0xb52
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb52
	jal ra, csr_bad_impl
	li a1, 0xb53
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb53
	jal ra, csr_bad_impl
	li a1, 0xb54
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb54
	jal ra, csr_bad_impl
	li a1, 0xb55
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb55
	jal ra, csr_bad_impl
	li a1, 0xb56
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb56
	jal ra, csr_bad_impl
	li a1, 0xb57
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb57
	jal ra, csr_bad_impl
	li a1, 0xb58
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb58
	jal ra, csr_bad_impl
	li a1, 0xb59
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb59
	jal ra, csr_bad_impl
	li a1, 0xb5a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb5a
	jal ra, csr_bad_impl
	li a1, 0xb5b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb5b
	jal ra, csr_bad_impl
	li a1, 0xb5c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb5c
	jal ra, csr_bad_impl
	li a1, 0xb5d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb5d
	jal ra, csr_bad_impl
	li a1, 0xb5e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb5e
	jal ra, csr_bad_impl
	li a1, 0xb5f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb5f
	jal ra, csr_bad_impl
	li a1, 0xb60
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb60
	jal ra, csr_bad_impl
	li a1, 0xb61
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb61
	jal ra, csr_bad_impl
	li a1, 0xb62
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb62
	jal ra, csr_bad_impl
	li a1, 0xb63
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb63
	jal ra, csr_bad_impl
	li a1, 0xb64
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb64
	jal ra, csr_bad_impl
	li a1, 0xb65
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb65
	jal ra, csr_bad_impl
	li a1, 0xb66
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb66
	jal ra, csr_bad_impl
	li a1, 0xb67
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb67
	jal ra, csr_bad_impl
	li a1, 0xb68
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb68
	jal ra, csr_bad_impl
	li a1, 0xb69
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb69
	jal ra, csr_bad_impl
	li a1, 0xb6a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb6a
	jal ra, csr_bad_impl
	li a1, 0xb6b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb6b
	jal ra, csr_bad_impl
	li a1, 0xb6c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb6c
	jal ra, csr_bad_impl
	li a1, 0xb6d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb6d
	jal ra, csr_bad_impl
	li a1, 0xb6e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb6e
	jal ra, csr_bad_impl
	li a1, 0xb6f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb6f
	jal ra, csr_bad_impl
	li a1, 0xb70
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb70
	jal ra, csr_bad_impl
	li a1, 0xb71
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb71
	jal ra, csr_bad_impl
	li a1, 0xb72
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb72
	jal ra, csr_bad_impl
	li a1, 0xb73
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb73
	jal ra, csr_bad_impl
	li a1, 0xb74
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb74
	jal ra, csr_bad_impl
	li a1, 0xb75
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb75
	jal ra, csr_bad_impl
	li a1, 0xb76
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb76
	jal ra, csr_bad_impl
	li a1, 0xb77
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb77
	jal ra, csr_bad_impl
	li a1, 0xb78
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb78
	jal ra, csr_bad_impl
	li a1, 0xb79
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb79
	jal ra, csr_bad_impl
	li a1, 0xb7a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb7a
	jal ra, csr_bad_impl
	li a1, 0xb7b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb7b
	jal ra, csr_bad_impl
	li a1, 0xb7c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb7c
	jal ra, csr_bad_impl
	li a1, 0xb7d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb7d
	jal ra, csr_bad_impl
	li a1, 0xb7e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb7e
	jal ra, csr_bad_impl
	li a1, 0xb7f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb7f
	jal ra, csr_bad_impl
	li a1, 0xb81
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb81
	jal ra, csr_bad_impl
	li a1, 0xb8d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb8d
	jal ra, csr_bad_impl
	li a1, 0xb8e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb8e
	jal ra, csr_bad_impl
	li a1, 0xb8f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb8f
	jal ra, csr_bad_impl
	li a1, 0xb90
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb90
	jal ra, csr_bad_impl
	li a1, 0xb91
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb91
	jal ra, csr_bad_impl
	li a1, 0xb92
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb92
	jal ra, csr_bad_impl
	li a1, 0xb93
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb93
	jal ra, csr_bad_impl
	li a1, 0xb94
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb94
	jal ra, csr_bad_impl
	li a1, 0xb95
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb95
	jal ra, csr_bad_impl
	li a1, 0xb96
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb96
	jal ra, csr_bad_impl
	li a1, 0xb97
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb97
	jal ra, csr_bad_impl
	li a1, 0xb98
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb98
	jal ra, csr_bad_impl
	li a1, 0xb99
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb99
	jal ra, csr_bad_impl
	li a1, 0xb9a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb9a
	jal ra, csr_bad_impl
	li a1, 0xb9b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb9b
	jal ra, csr_bad_impl
	li a1, 0xb9c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb9c
	jal ra, csr_bad_impl
	li a1, 0xb9d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb9d
	jal ra, csr_bad_impl
	li a1, 0xb9e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb9e
	jal ra, csr_bad_impl
	li a1, 0xb9f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xb9f
	jal ra, csr_bad_impl
	li a1, 0xba0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xba0
	jal ra, csr_bad_impl
	li a1, 0xba1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xba1
	jal ra, csr_bad_impl
	li a1, 0xba2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xba2
	jal ra, csr_bad_impl
	li a1, 0xba3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xba3
	jal ra, csr_bad_impl
	li a1, 0xba4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xba4
	jal ra, csr_bad_impl
	li a1, 0xba5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xba5
	jal ra, csr_bad_impl
	li a1, 0xba6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xba6
	jal ra, csr_bad_impl
	li a1, 0xba7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xba7
	jal ra, csr_bad_impl
	li a1, 0xba8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xba8
	jal ra, csr_bad_impl
	li a1, 0xba9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xba9
	jal ra, csr_bad_impl
	li a1, 0xbaa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbaa
	jal ra, csr_bad_impl
	li a1, 0xbab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbab
	jal ra, csr_bad_impl
	li a1, 0xbac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbac
	jal ra, csr_bad_impl
	li a1, 0xbad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbad
	jal ra, csr_bad_impl
	li a1, 0xbae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbae
	jal ra, csr_bad_impl
	li a1, 0xbaf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbaf
	jal ra, csr_bad_impl
	li a1, 0xbb0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbb0
	jal ra, csr_bad_impl
	li a1, 0xbb1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbb1
	jal ra, csr_bad_impl
	li a1, 0xbb2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbb2
	jal ra, csr_bad_impl
	li a1, 0xbb3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbb3
	jal ra, csr_bad_impl
	li a1, 0xbb4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbb4
	jal ra, csr_bad_impl
	li a1, 0xbb5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbb5
	jal ra, csr_bad_impl
	li a1, 0xbb6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbb6
	jal ra, csr_bad_impl
	li a1, 0xbb7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbb7
	jal ra, csr_bad_impl
	li a1, 0xbb8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbb8
	jal ra, csr_bad_impl
	li a1, 0xbb9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbb9
	jal ra, csr_bad_impl
	li a1, 0xbba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbba
	jal ra, csr_bad_impl
	li a1, 0xbbb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbbb
	jal ra, csr_bad_impl
	li a1, 0xbbc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbbc
	jal ra, csr_bad_impl
	li a1, 0xbbd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbbd
	jal ra, csr_bad_impl
	li a1, 0xbbe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbbe
	jal ra, csr_bad_impl
	li a1, 0xbbf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbbf
	jal ra, csr_bad_impl
	li a1, 0xbc0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbc0
	jal ra, csr_bad_impl
	li a1, 0xbc1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbc1
	jal ra, csr_bad_impl
	li a1, 0xbc2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbc2
	jal ra, csr_bad_impl
	li a1, 0xbc3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbc3
	jal ra, csr_bad_impl
	li a1, 0xbc4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbc4
	jal ra, csr_bad_impl
	li a1, 0xbc5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbc5
	jal ra, csr_bad_impl
	li a1, 0xbc6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbc6
	jal ra, csr_bad_impl
	li a1, 0xbc7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbc7
	jal ra, csr_bad_impl
	li a1, 0xbc8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbc8
	jal ra, csr_bad_impl
	li a1, 0xbc9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbc9
	jal ra, csr_bad_impl
	li a1, 0xbca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbca
	jal ra, csr_bad_impl
	li a1, 0xbcb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbcb
	jal ra, csr_bad_impl
	li a1, 0xbcc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbcc
	jal ra, csr_bad_impl
	li a1, 0xbcd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbcd
	jal ra, csr_bad_impl
	li a1, 0xbce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbce
	jal ra, csr_bad_impl
	li a1, 0xbcf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbcf
	jal ra, csr_bad_impl
	li a1, 0xbd0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbd0
	jal ra, csr_bad_impl
	li a1, 0xbd1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbd1
	jal ra, csr_bad_impl
	li a1, 0xbd2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbd2
	jal ra, csr_bad_impl
	li a1, 0xbd3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbd3
	jal ra, csr_bad_impl
	li a1, 0xbd4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbd4
	jal ra, csr_bad_impl
	li a1, 0xbd5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbd5
	jal ra, csr_bad_impl
	li a1, 0xbd6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbd6
	jal ra, csr_bad_impl
	li a1, 0xbd7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbd7
	jal ra, csr_bad_impl
	li a1, 0xbd8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbd8
	jal ra, csr_bad_impl
	li a1, 0xbd9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbd9
	jal ra, csr_bad_impl
	li a1, 0xbda
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbda
	jal ra, csr_bad_impl
	li a1, 0xbdb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbdb
	jal ra, csr_bad_impl
	li a1, 0xbdc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbdc
	jal ra, csr_bad_impl
	li a1, 0xbdd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbdd
	jal ra, csr_bad_impl
	li a1, 0xbde
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbde
	jal ra, csr_bad_impl
	li a1, 0xbdf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbdf
	jal ra, csr_bad_impl
	li a1, 0xbe0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbe0
	jal ra, csr_bad_impl
	li a1, 0xbe1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbe1
	jal ra, csr_bad_impl
	li a1, 0xbe2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbe2
	jal ra, csr_bad_impl
	li a1, 0xbe3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbe3
	jal ra, csr_bad_impl
	li a1, 0xbe4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbe4
	jal ra, csr_bad_impl
	li a1, 0xbe5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbe5
	jal ra, csr_bad_impl
	li a1, 0xbe6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbe6
	jal ra, csr_bad_impl
	li a1, 0xbe7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbe7
	jal ra, csr_bad_impl
	li a1, 0xbe8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbe8
	jal ra, csr_bad_impl
	li a1, 0xbe9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbe9
	jal ra, csr_bad_impl
	li a1, 0xbea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbea
	jal ra, csr_bad_impl
	li a1, 0xbeb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbeb
	jal ra, csr_bad_impl
	li a1, 0xbec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbec
	jal ra, csr_bad_impl
	li a1, 0xbed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbed
	jal ra, csr_bad_impl
	li a1, 0xbee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbee
	jal ra, csr_bad_impl
	li a1, 0xbef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbef
	jal ra, csr_bad_impl
	li a1, 0xbf0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbf0
	jal ra, csr_bad_impl
	li a1, 0xbf1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbf1
	jal ra, csr_bad_impl
	li a1, 0xbf2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbf2
	jal ra, csr_bad_impl
	li a1, 0xbf3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbf3
	jal ra, csr_bad_impl
	li a1, 0xbf4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbf4
	jal ra, csr_bad_impl
	li a1, 0xbf5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbf5
	jal ra, csr_bad_impl
	li a1, 0xbf6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbf6
	jal ra, csr_bad_impl
	li a1, 0xbf7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbf7
	jal ra, csr_bad_impl
	li a1, 0xbf8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbf8
	jal ra, csr_bad_impl
	li a1, 0xbf9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbf9
	jal ra, csr_bad_impl
	li a1, 0xbfa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbfa
	jal ra, csr_bad_impl
	li a1, 0xbfb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbfb
	jal ra, csr_bad_impl
	li a1, 0xbfc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbfc
	jal ra, csr_bad_impl
	li a1, 0xbfd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbfd
	jal ra, csr_bad_impl
	li a1, 0xbfe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbfe
	jal ra, csr_bad_impl
	li a1, 0xbff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xbff
	jal ra, csr_bad_impl
	li a1, 0xc01
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc01
	jal ra, csr_bad_impl
	li a1, 0xc03
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc03
	jal ra, csr_bad_impl
	li a1, 0xc04
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc04
	jal ra, csr_bad_impl
	li a1, 0xc05
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc05
	jal ra, csr_bad_impl
	li a1, 0xc06
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc06
	jal ra, csr_bad_impl
	li a1, 0xc07
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc07
	jal ra, csr_bad_impl
	li a1, 0xc08
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc08
	jal ra, csr_bad_impl
	li a1, 0xc09
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc09
	jal ra, csr_bad_impl
	li a1, 0xc0a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc0a
	jal ra, csr_bad_impl
	li a1, 0xc0b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc0b
	jal ra, csr_bad_impl
	li a1, 0xc0c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc0c
	jal ra, csr_bad_impl
	li a1, 0xc0d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc0d
	jal ra, csr_bad_impl
	li a1, 0xc0e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc0e
	jal ra, csr_bad_impl
	li a1, 0xc0f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc0f
	jal ra, csr_bad_impl
	li a1, 0xc10
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc10
	jal ra, csr_bad_impl
	li a1, 0xc11
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc11
	jal ra, csr_bad_impl
	li a1, 0xc12
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc12
	jal ra, csr_bad_impl
	li a1, 0xc13
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc13
	jal ra, csr_bad_impl
	li a1, 0xc14
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc14
	jal ra, csr_bad_impl
	li a1, 0xc15
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc15
	jal ra, csr_bad_impl
	li a1, 0xc16
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc16
	jal ra, csr_bad_impl
	li a1, 0xc17
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc17
	jal ra, csr_bad_impl
	li a1, 0xc18
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc18
	jal ra, csr_bad_impl
	li a1, 0xc19
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc19
	jal ra, csr_bad_impl
	li a1, 0xc1a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc1a
	jal ra, csr_bad_impl
	li a1, 0xc1b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc1b
	jal ra, csr_bad_impl
	li a1, 0xc1c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc1c
	jal ra, csr_bad_impl
	li a1, 0xc1d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc1d
	jal ra, csr_bad_impl
	li a1, 0xc1e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc1e
	jal ra, csr_bad_impl
	li a1, 0xc1f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc1f
	jal ra, csr_bad_impl
	li a1, 0xc20
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc20
	jal ra, csr_bad_impl
	li a1, 0xc21
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc21
	jal ra, csr_bad_impl
	li a1, 0xc22
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc22
	jal ra, csr_bad_impl
	li a1, 0xc23
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc23
	jal ra, csr_bad_impl
	li a1, 0xc24
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc24
	jal ra, csr_bad_impl
	li a1, 0xc25
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc25
	jal ra, csr_bad_impl
	li a1, 0xc26
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc26
	jal ra, csr_bad_impl
	li a1, 0xc27
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc27
	jal ra, csr_bad_impl
	li a1, 0xc28
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc28
	jal ra, csr_bad_impl
	li a1, 0xc29
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc29
	jal ra, csr_bad_impl
	li a1, 0xc2a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc2a
	jal ra, csr_bad_impl
	li a1, 0xc2b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc2b
	jal ra, csr_bad_impl
	li a1, 0xc2c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc2c
	jal ra, csr_bad_impl
	li a1, 0xc2d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc2d
	jal ra, csr_bad_impl
	li a1, 0xc2e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc2e
	jal ra, csr_bad_impl
	li a1, 0xc2f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc2f
	jal ra, csr_bad_impl
	li a1, 0xc30
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc30
	jal ra, csr_bad_impl
	li a1, 0xc31
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc31
	jal ra, csr_bad_impl
	li a1, 0xc32
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc32
	jal ra, csr_bad_impl
	li a1, 0xc33
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc33
	jal ra, csr_bad_impl
	li a1, 0xc34
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc34
	jal ra, csr_bad_impl
	li a1, 0xc35
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc35
	jal ra, csr_bad_impl
	li a1, 0xc36
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc36
	jal ra, csr_bad_impl
	li a1, 0xc37
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc37
	jal ra, csr_bad_impl
	li a1, 0xc38
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc38
	jal ra, csr_bad_impl
	li a1, 0xc39
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc39
	jal ra, csr_bad_impl
	li a1, 0xc3a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc3a
	jal ra, csr_bad_impl
	li a1, 0xc3b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc3b
	jal ra, csr_bad_impl
	li a1, 0xc3c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc3c
	jal ra, csr_bad_impl
	li a1, 0xc3d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc3d
	jal ra, csr_bad_impl
	li a1, 0xc3e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc3e
	jal ra, csr_bad_impl
	li a1, 0xc3f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc3f
	jal ra, csr_bad_impl
	li a1, 0xc40
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc40
	jal ra, csr_bad_impl
	li a1, 0xc41
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc41
	jal ra, csr_bad_impl
	li a1, 0xc42
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc42
	jal ra, csr_bad_impl
	li a1, 0xc43
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc43
	jal ra, csr_bad_impl
	li a1, 0xc44
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc44
	jal ra, csr_bad_impl
	li a1, 0xc45
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc45
	jal ra, csr_bad_impl
	li a1, 0xc46
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc46
	jal ra, csr_bad_impl
	li a1, 0xc47
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc47
	jal ra, csr_bad_impl
	li a1, 0xc48
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc48
	jal ra, csr_bad_impl
	li a1, 0xc49
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc49
	jal ra, csr_bad_impl
	li a1, 0xc4a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc4a
	jal ra, csr_bad_impl
	li a1, 0xc4b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc4b
	jal ra, csr_bad_impl
	li a1, 0xc4c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc4c
	jal ra, csr_bad_impl
	li a1, 0xc4d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc4d
	jal ra, csr_bad_impl
	li a1, 0xc4e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc4e
	jal ra, csr_bad_impl
	li a1, 0xc4f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc4f
	jal ra, csr_bad_impl
	li a1, 0xc50
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc50
	jal ra, csr_bad_impl
	li a1, 0xc51
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc51
	jal ra, csr_bad_impl
	li a1, 0xc52
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc52
	jal ra, csr_bad_impl
	li a1, 0xc53
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc53
	jal ra, csr_bad_impl
	li a1, 0xc54
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc54
	jal ra, csr_bad_impl
	li a1, 0xc55
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc55
	jal ra, csr_bad_impl
	li a1, 0xc56
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc56
	jal ra, csr_bad_impl
	li a1, 0xc57
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc57
	jal ra, csr_bad_impl
	li a1, 0xc58
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc58
	jal ra, csr_bad_impl
	li a1, 0xc59
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc59
	jal ra, csr_bad_impl
	li a1, 0xc5a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc5a
	jal ra, csr_bad_impl
	li a1, 0xc5b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc5b
	jal ra, csr_bad_impl
	li a1, 0xc5c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc5c
	jal ra, csr_bad_impl
	li a1, 0xc5d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc5d
	jal ra, csr_bad_impl
	li a1, 0xc5e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc5e
	jal ra, csr_bad_impl
	li a1, 0xc5f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc5f
	jal ra, csr_bad_impl
	li a1, 0xc60
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc60
	jal ra, csr_bad_impl
	li a1, 0xc61
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc61
	jal ra, csr_bad_impl
	li a1, 0xc62
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc62
	jal ra, csr_bad_impl
	li a1, 0xc63
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc63
	jal ra, csr_bad_impl
	li a1, 0xc64
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc64
	jal ra, csr_bad_impl
	li a1, 0xc65
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc65
	jal ra, csr_bad_impl
	li a1, 0xc66
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc66
	jal ra, csr_bad_impl
	li a1, 0xc67
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc67
	jal ra, csr_bad_impl
	li a1, 0xc68
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc68
	jal ra, csr_bad_impl
	li a1, 0xc69
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc69
	jal ra, csr_bad_impl
	li a1, 0xc6a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc6a
	jal ra, csr_bad_impl
	li a1, 0xc6b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc6b
	jal ra, csr_bad_impl
	li a1, 0xc6c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc6c
	jal ra, csr_bad_impl
	li a1, 0xc6d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc6d
	jal ra, csr_bad_impl
	li a1, 0xc6e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc6e
	jal ra, csr_bad_impl
	li a1, 0xc6f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc6f
	jal ra, csr_bad_impl
	li a1, 0xc70
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc70
	jal ra, csr_bad_impl
	li a1, 0xc71
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc71
	jal ra, csr_bad_impl
	li a1, 0xc72
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc72
	jal ra, csr_bad_impl
	li a1, 0xc73
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc73
	jal ra, csr_bad_impl
	li a1, 0xc74
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc74
	jal ra, csr_bad_impl
	li a1, 0xc75
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc75
	jal ra, csr_bad_impl
	li a1, 0xc76
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc76
	jal ra, csr_bad_impl
	li a1, 0xc77
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc77
	jal ra, csr_bad_impl
	li a1, 0xc78
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc78
	jal ra, csr_bad_impl
	li a1, 0xc79
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc79
	jal ra, csr_bad_impl
	li a1, 0xc7a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc7a
	jal ra, csr_bad_impl
	li a1, 0xc7b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc7b
	jal ra, csr_bad_impl
	li a1, 0xc7c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc7c
	jal ra, csr_bad_impl
	li a1, 0xc7d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc7d
	jal ra, csr_bad_impl
	li a1, 0xc7e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc7e
	jal ra, csr_bad_impl
	li a1, 0xc7f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc7f
	jal ra, csr_bad_impl
	li a1, 0xc81
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc81
	jal ra, csr_bad_impl
	li a1, 0xc83
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc83
	jal ra, csr_bad_impl
	li a1, 0xc84
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc84
	jal ra, csr_bad_impl
	li a1, 0xc85
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc85
	jal ra, csr_bad_impl
	li a1, 0xc86
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc86
	jal ra, csr_bad_impl
	li a1, 0xc87
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc87
	jal ra, csr_bad_impl
	li a1, 0xc88
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc88
	jal ra, csr_bad_impl
	li a1, 0xc89
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc89
	jal ra, csr_bad_impl
	li a1, 0xc8a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc8a
	jal ra, csr_bad_impl
	li a1, 0xc8b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc8b
	jal ra, csr_bad_impl
	li a1, 0xc8c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc8c
	jal ra, csr_bad_impl
	li a1, 0xc8d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc8d
	jal ra, csr_bad_impl
	li a1, 0xc8e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc8e
	jal ra, csr_bad_impl
	li a1, 0xc8f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc8f
	jal ra, csr_bad_impl
	li a1, 0xc90
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc90
	jal ra, csr_bad_impl
	li a1, 0xc91
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc91
	jal ra, csr_bad_impl
	li a1, 0xc92
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc92
	jal ra, csr_bad_impl
	li a1, 0xc93
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc93
	jal ra, csr_bad_impl
	li a1, 0xc94
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc94
	jal ra, csr_bad_impl
	li a1, 0xc95
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc95
	jal ra, csr_bad_impl
	li a1, 0xc96
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc96
	jal ra, csr_bad_impl
	li a1, 0xc97
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc97
	jal ra, csr_bad_impl
	li a1, 0xc98
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc98
	jal ra, csr_bad_impl
	li a1, 0xc99
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc99
	jal ra, csr_bad_impl
	li a1, 0xc9a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc9a
	jal ra, csr_bad_impl
	li a1, 0xc9b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc9b
	jal ra, csr_bad_impl
	li a1, 0xc9c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc9c
	jal ra, csr_bad_impl
	li a1, 0xc9d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc9d
	jal ra, csr_bad_impl
	li a1, 0xc9e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc9e
	jal ra, csr_bad_impl
	li a1, 0xc9f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xc9f
	jal ra, csr_bad_impl
	li a1, 0xca0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xca0
	jal ra, csr_bad_impl
	li a1, 0xca1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xca1
	jal ra, csr_bad_impl
	li a1, 0xca2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xca2
	jal ra, csr_bad_impl
	li a1, 0xca3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xca3
	jal ra, csr_bad_impl
	li a1, 0xca4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xca4
	jal ra, csr_bad_impl
	li a1, 0xca5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xca5
	jal ra, csr_bad_impl
	li a1, 0xca6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xca6
	jal ra, csr_bad_impl
	li a1, 0xca7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xca7
	jal ra, csr_bad_impl
	li a1, 0xca8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xca8
	jal ra, csr_bad_impl
	li a1, 0xca9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xca9
	jal ra, csr_bad_impl
	li a1, 0xcaa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcaa
	jal ra, csr_bad_impl
	li a1, 0xcab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcab
	jal ra, csr_bad_impl
	li a1, 0xcac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcac
	jal ra, csr_bad_impl
	li a1, 0xcad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcad
	jal ra, csr_bad_impl
	li a1, 0xcae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcae
	jal ra, csr_bad_impl
	li a1, 0xcaf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcaf
	jal ra, csr_bad_impl
	li a1, 0xcb0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcb0
	jal ra, csr_bad_impl
	li a1, 0xcb1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcb1
	jal ra, csr_bad_impl
	li a1, 0xcb2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcb2
	jal ra, csr_bad_impl
	li a1, 0xcb3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcb3
	jal ra, csr_bad_impl
	li a1, 0xcb4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcb4
	jal ra, csr_bad_impl
	li a1, 0xcb5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcb5
	jal ra, csr_bad_impl
	li a1, 0xcb6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcb6
	jal ra, csr_bad_impl
	li a1, 0xcb7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcb7
	jal ra, csr_bad_impl
	li a1, 0xcb8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcb8
	jal ra, csr_bad_impl
	li a1, 0xcb9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcb9
	jal ra, csr_bad_impl
	li a1, 0xcba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcba
	jal ra, csr_bad_impl
	li a1, 0xcbb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcbb
	jal ra, csr_bad_impl
	li a1, 0xcbc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcbc
	jal ra, csr_bad_impl
	li a1, 0xcbd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcbd
	jal ra, csr_bad_impl
	li a1, 0xcbe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcbe
	jal ra, csr_bad_impl
	li a1, 0xcbf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcbf
	jal ra, csr_bad_impl
	li a1, 0xcc0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcc0
	jal ra, csr_bad_impl
	li a1, 0xcc1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcc1
	jal ra, csr_bad_impl
	li a1, 0xcc2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcc2
	jal ra, csr_bad_impl
	li a1, 0xcc3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcc3
	jal ra, csr_bad_impl
	li a1, 0xcc4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcc4
	jal ra, csr_bad_impl
	li a1, 0xcc5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcc5
	jal ra, csr_bad_impl
	li a1, 0xcc6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcc6
	jal ra, csr_bad_impl
	li a1, 0xcc7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcc7
	jal ra, csr_bad_impl
	li a1, 0xcc8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcc8
	jal ra, csr_bad_impl
	li a1, 0xcc9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcc9
	jal ra, csr_bad_impl
	li a1, 0xcca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcca
	jal ra, csr_bad_impl
	li a1, 0xccb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xccb
	jal ra, csr_bad_impl
	li a1, 0xccc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xccc
	jal ra, csr_bad_impl
	li a1, 0xccd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xccd
	jal ra, csr_bad_impl
	li a1, 0xcce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcce
	jal ra, csr_bad_impl
	li a1, 0xccf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xccf
	jal ra, csr_bad_impl
	li a1, 0xcd0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcd0
	jal ra, csr_bad_impl
	li a1, 0xcd1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcd1
	jal ra, csr_bad_impl
	li a1, 0xcd2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcd2
	jal ra, csr_bad_impl
	li a1, 0xcd3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcd3
	jal ra, csr_bad_impl
	li a1, 0xcd4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcd4
	jal ra, csr_bad_impl
	li a1, 0xcd5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcd5
	jal ra, csr_bad_impl
	li a1, 0xcd6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcd6
	jal ra, csr_bad_impl
	li a1, 0xcd7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcd7
	jal ra, csr_bad_impl
	li a1, 0xcd8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcd8
	jal ra, csr_bad_impl
	li a1, 0xcd9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcd9
	jal ra, csr_bad_impl
	li a1, 0xcda
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcda
	jal ra, csr_bad_impl
	li a1, 0xcdb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcdb
	jal ra, csr_bad_impl
	li a1, 0xcdc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcdc
	jal ra, csr_bad_impl
	li a1, 0xcdd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcdd
	jal ra, csr_bad_impl
	li a1, 0xcde
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcde
	jal ra, csr_bad_impl
	li a1, 0xcdf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcdf
	jal ra, csr_bad_impl
	li a1, 0xce0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xce0
	jal ra, csr_bad_impl
	li a1, 0xce1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xce1
	jal ra, csr_bad_impl
	li a1, 0xce2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xce2
	jal ra, csr_bad_impl
	li a1, 0xce3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xce3
	jal ra, csr_bad_impl
	li a1, 0xce4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xce4
	jal ra, csr_bad_impl
	li a1, 0xce5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xce5
	jal ra, csr_bad_impl
	li a1, 0xce6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xce6
	jal ra, csr_bad_impl
	li a1, 0xce7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xce7
	jal ra, csr_bad_impl
	li a1, 0xce8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xce8
	jal ra, csr_bad_impl
	li a1, 0xce9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xce9
	jal ra, csr_bad_impl
	li a1, 0xcea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcea
	jal ra, csr_bad_impl
	li a1, 0xceb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xceb
	jal ra, csr_bad_impl
	li a1, 0xcec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcec
	jal ra, csr_bad_impl
	li a1, 0xced
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xced
	jal ra, csr_bad_impl
	li a1, 0xcee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcee
	jal ra, csr_bad_impl
	li a1, 0xcef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcef
	jal ra, csr_bad_impl
	li a1, 0xcf0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcf0
	jal ra, csr_bad_impl
	li a1, 0xcf1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcf1
	jal ra, csr_bad_impl
	li a1, 0xcf2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcf2
	jal ra, csr_bad_impl
	li a1, 0xcf3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcf3
	jal ra, csr_bad_impl
	li a1, 0xcf4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcf4
	jal ra, csr_bad_impl
	li a1, 0xcf5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcf5
	jal ra, csr_bad_impl
	li a1, 0xcf6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcf6
	jal ra, csr_bad_impl
	li a1, 0xcf7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcf7
	jal ra, csr_bad_impl
	li a1, 0xcf8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcf8
	jal ra, csr_bad_impl
	li a1, 0xcf9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcf9
	jal ra, csr_bad_impl
	li a1, 0xcfa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcfa
	jal ra, csr_bad_impl
	li a1, 0xcfb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcfb
	jal ra, csr_bad_impl
	li a1, 0xcfc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcfc
	jal ra, csr_bad_impl
	li a1, 0xcfd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcfd
	jal ra, csr_bad_impl
	li a1, 0xcfe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcfe
	jal ra, csr_bad_impl
	li a1, 0xcff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xcff
	jal ra, csr_bad_impl
	li a1, 0xd00
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd00
	jal ra, csr_bad_impl
	li a1, 0xd01
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd01
	jal ra, csr_bad_impl
	li a1, 0xd02
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd02
	jal ra, csr_bad_impl
	li a1, 0xd03
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd03
	jal ra, csr_bad_impl
	li a1, 0xd04
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd04
	jal ra, csr_bad_impl
	li a1, 0xd05
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd05
	jal ra, csr_bad_impl
	li a1, 0xd06
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd06
	jal ra, csr_bad_impl
	li a1, 0xd07
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd07
	jal ra, csr_bad_impl
	li a1, 0xd08
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd08
	jal ra, csr_bad_impl
	li a1, 0xd09
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd09
	jal ra, csr_bad_impl
	li a1, 0xd0a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd0a
	jal ra, csr_bad_impl
	li a1, 0xd0b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd0b
	jal ra, csr_bad_impl
	li a1, 0xd0c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd0c
	jal ra, csr_bad_impl
	li a1, 0xd0d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd0d
	jal ra, csr_bad_impl
	li a1, 0xd0e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd0e
	jal ra, csr_bad_impl
	li a1, 0xd0f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd0f
	jal ra, csr_bad_impl
	li a1, 0xd10
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd10
	jal ra, csr_bad_impl
	li a1, 0xd11
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd11
	jal ra, csr_bad_impl
	li a1, 0xd12
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd12
	jal ra, csr_bad_impl
	li a1, 0xd13
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd13
	jal ra, csr_bad_impl
	li a1, 0xd14
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd14
	jal ra, csr_bad_impl
	li a1, 0xd15
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd15
	jal ra, csr_bad_impl
	li a1, 0xd16
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd16
	jal ra, csr_bad_impl
	li a1, 0xd17
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd17
	jal ra, csr_bad_impl
	li a1, 0xd18
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd18
	jal ra, csr_bad_impl
	li a1, 0xd19
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd19
	jal ra, csr_bad_impl
	li a1, 0xd1a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd1a
	jal ra, csr_bad_impl
	li a1, 0xd1b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd1b
	jal ra, csr_bad_impl
	li a1, 0xd1c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd1c
	jal ra, csr_bad_impl
	li a1, 0xd1d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd1d
	jal ra, csr_bad_impl
	li a1, 0xd1e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd1e
	jal ra, csr_bad_impl
	li a1, 0xd1f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd1f
	jal ra, csr_bad_impl
	li a1, 0xd20
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd20
	jal ra, csr_bad_impl
	li a1, 0xd21
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd21
	jal ra, csr_bad_impl
	li a1, 0xd22
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd22
	jal ra, csr_bad_impl
	li a1, 0xd23
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd23
	jal ra, csr_bad_impl
	li a1, 0xd24
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd24
	jal ra, csr_bad_impl
	li a1, 0xd25
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd25
	jal ra, csr_bad_impl
	li a1, 0xd26
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd26
	jal ra, csr_bad_impl
	li a1, 0xd27
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd27
	jal ra, csr_bad_impl
	li a1, 0xd28
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd28
	jal ra, csr_bad_impl
	li a1, 0xd29
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd29
	jal ra, csr_bad_impl
	li a1, 0xd2a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd2a
	jal ra, csr_bad_impl
	li a1, 0xd2b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd2b
	jal ra, csr_bad_impl
	li a1, 0xd2c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd2c
	jal ra, csr_bad_impl
	li a1, 0xd2d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd2d
	jal ra, csr_bad_impl
	li a1, 0xd2e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd2e
	jal ra, csr_bad_impl
	li a1, 0xd2f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd2f
	jal ra, csr_bad_impl
	li a1, 0xd30
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd30
	jal ra, csr_bad_impl
	li a1, 0xd31
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd31
	jal ra, csr_bad_impl
	li a1, 0xd32
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd32
	jal ra, csr_bad_impl
	li a1, 0xd33
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd33
	jal ra, csr_bad_impl
	li a1, 0xd34
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd34
	jal ra, csr_bad_impl
	li a1, 0xd35
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd35
	jal ra, csr_bad_impl
	li a1, 0xd36
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd36
	jal ra, csr_bad_impl
	li a1, 0xd37
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd37
	jal ra, csr_bad_impl
	li a1, 0xd38
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd38
	jal ra, csr_bad_impl
	li a1, 0xd39
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd39
	jal ra, csr_bad_impl
	li a1, 0xd3a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd3a
	jal ra, csr_bad_impl
	li a1, 0xd3b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd3b
	jal ra, csr_bad_impl
	li a1, 0xd3c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd3c
	jal ra, csr_bad_impl
	li a1, 0xd3d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd3d
	jal ra, csr_bad_impl
	li a1, 0xd3e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd3e
	jal ra, csr_bad_impl
	li a1, 0xd3f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd3f
	jal ra, csr_bad_impl
	li a1, 0xd40
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd40
	jal ra, csr_bad_impl
	li a1, 0xd41
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd41
	jal ra, csr_bad_impl
	li a1, 0xd42
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd42
	jal ra, csr_bad_impl
	li a1, 0xd43
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd43
	jal ra, csr_bad_impl
	li a1, 0xd44
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd44
	jal ra, csr_bad_impl
	li a1, 0xd45
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd45
	jal ra, csr_bad_impl
	li a1, 0xd46
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd46
	jal ra, csr_bad_impl
	li a1, 0xd47
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd47
	jal ra, csr_bad_impl
	li a1, 0xd48
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd48
	jal ra, csr_bad_impl
	li a1, 0xd49
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd49
	jal ra, csr_bad_impl
	li a1, 0xd4a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd4a
	jal ra, csr_bad_impl
	li a1, 0xd4b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd4b
	jal ra, csr_bad_impl
	li a1, 0xd4c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd4c
	jal ra, csr_bad_impl
	li a1, 0xd4d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd4d
	jal ra, csr_bad_impl
	li a1, 0xd4e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd4e
	jal ra, csr_bad_impl
	li a1, 0xd4f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd4f
	jal ra, csr_bad_impl
	li a1, 0xd50
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd50
	jal ra, csr_bad_impl
	li a1, 0xd51
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd51
	jal ra, csr_bad_impl
	li a1, 0xd52
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd52
	jal ra, csr_bad_impl
	li a1, 0xd53
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd53
	jal ra, csr_bad_impl
	li a1, 0xd54
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd54
	jal ra, csr_bad_impl
	li a1, 0xd55
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd55
	jal ra, csr_bad_impl
	li a1, 0xd56
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd56
	jal ra, csr_bad_impl
	li a1, 0xd57
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd57
	jal ra, csr_bad_impl
	li a1, 0xd58
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd58
	jal ra, csr_bad_impl
	li a1, 0xd59
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd59
	jal ra, csr_bad_impl
	li a1, 0xd5a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd5a
	jal ra, csr_bad_impl
	li a1, 0xd5b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd5b
	jal ra, csr_bad_impl
	li a1, 0xd5c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd5c
	jal ra, csr_bad_impl
	li a1, 0xd5d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd5d
	jal ra, csr_bad_impl
	li a1, 0xd5e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd5e
	jal ra, csr_bad_impl
	li a1, 0xd5f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd5f
	jal ra, csr_bad_impl
	li a1, 0xd60
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd60
	jal ra, csr_bad_impl
	li a1, 0xd61
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd61
	jal ra, csr_bad_impl
	li a1, 0xd62
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd62
	jal ra, csr_bad_impl
	li a1, 0xd63
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd63
	jal ra, csr_bad_impl
	li a1, 0xd64
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd64
	jal ra, csr_bad_impl
	li a1, 0xd65
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd65
	jal ra, csr_bad_impl
	li a1, 0xd66
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd66
	jal ra, csr_bad_impl
	li a1, 0xd67
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd67
	jal ra, csr_bad_impl
	li a1, 0xd68
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd68
	jal ra, csr_bad_impl
	li a1, 0xd69
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd69
	jal ra, csr_bad_impl
	li a1, 0xd6a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd6a
	jal ra, csr_bad_impl
	li a1, 0xd6b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd6b
	jal ra, csr_bad_impl
	li a1, 0xd6c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd6c
	jal ra, csr_bad_impl
	li a1, 0xd6d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd6d
	jal ra, csr_bad_impl
	li a1, 0xd6e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd6e
	jal ra, csr_bad_impl
	li a1, 0xd6f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd6f
	jal ra, csr_bad_impl
	li a1, 0xd70
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd70
	jal ra, csr_bad_impl
	li a1, 0xd71
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd71
	jal ra, csr_bad_impl
	li a1, 0xd72
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd72
	jal ra, csr_bad_impl
	li a1, 0xd73
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd73
	jal ra, csr_bad_impl
	li a1, 0xd74
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd74
	jal ra, csr_bad_impl
	li a1, 0xd75
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd75
	jal ra, csr_bad_impl
	li a1, 0xd76
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd76
	jal ra, csr_bad_impl
	li a1, 0xd77
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd77
	jal ra, csr_bad_impl
	li a1, 0xd78
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd78
	jal ra, csr_bad_impl
	li a1, 0xd79
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd79
	jal ra, csr_bad_impl
	li a1, 0xd7a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd7a
	jal ra, csr_bad_impl
	li a1, 0xd7b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd7b
	jal ra, csr_bad_impl
	li a1, 0xd7c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd7c
	jal ra, csr_bad_impl
	li a1, 0xd7d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd7d
	jal ra, csr_bad_impl
	li a1, 0xd7e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd7e
	jal ra, csr_bad_impl
	li a1, 0xd7f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd7f
	jal ra, csr_bad_impl
	li a1, 0xd80
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd80
	jal ra, csr_bad_impl
	li a1, 0xd81
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd81
	jal ra, csr_bad_impl
	li a1, 0xd82
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd82
	jal ra, csr_bad_impl
	li a1, 0xd83
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd83
	jal ra, csr_bad_impl
	li a1, 0xd84
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd84
	jal ra, csr_bad_impl
	li a1, 0xd85
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd85
	jal ra, csr_bad_impl
	li a1, 0xd86
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd86
	jal ra, csr_bad_impl
	li a1, 0xd87
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd87
	jal ra, csr_bad_impl
	li a1, 0xd88
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd88
	jal ra, csr_bad_impl
	li a1, 0xd89
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd89
	jal ra, csr_bad_impl
	li a1, 0xd8a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd8a
	jal ra, csr_bad_impl
	li a1, 0xd8b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd8b
	jal ra, csr_bad_impl
	li a1, 0xd8c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd8c
	jal ra, csr_bad_impl
	li a1, 0xd8d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd8d
	jal ra, csr_bad_impl
	li a1, 0xd8e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd8e
	jal ra, csr_bad_impl
	li a1, 0xd8f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd8f
	jal ra, csr_bad_impl
	li a1, 0xd90
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd90
	jal ra, csr_bad_impl
	li a1, 0xd91
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd91
	jal ra, csr_bad_impl
	li a1, 0xd92
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd92
	jal ra, csr_bad_impl
	li a1, 0xd93
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd93
	jal ra, csr_bad_impl
	li a1, 0xd94
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd94
	jal ra, csr_bad_impl
	li a1, 0xd95
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd95
	jal ra, csr_bad_impl
	li a1, 0xd96
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd96
	jal ra, csr_bad_impl
	li a1, 0xd97
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd97
	jal ra, csr_bad_impl
	li a1, 0xd98
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd98
	jal ra, csr_bad_impl
	li a1, 0xd99
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd99
	jal ra, csr_bad_impl
	li a1, 0xd9a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd9a
	jal ra, csr_bad_impl
	li a1, 0xd9b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd9b
	jal ra, csr_bad_impl
	li a1, 0xd9c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd9c
	jal ra, csr_bad_impl
	li a1, 0xd9d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd9d
	jal ra, csr_bad_impl
	li a1, 0xd9e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd9e
	jal ra, csr_bad_impl
	li a1, 0xd9f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xd9f
	jal ra, csr_bad_impl
	li a1, 0xda0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xda0
	jal ra, csr_bad_impl
	li a1, 0xda1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xda1
	jal ra, csr_bad_impl
	li a1, 0xda2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xda2
	jal ra, csr_bad_impl
	li a1, 0xda3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xda3
	jal ra, csr_bad_impl
	li a1, 0xda4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xda4
	jal ra, csr_bad_impl
	li a1, 0xda5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xda5
	jal ra, csr_bad_impl
	li a1, 0xda6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xda6
	jal ra, csr_bad_impl
	li a1, 0xda7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xda7
	jal ra, csr_bad_impl
	li a1, 0xda8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xda8
	jal ra, csr_bad_impl
	li a1, 0xda9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xda9
	jal ra, csr_bad_impl
	li a1, 0xdaa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdaa
	jal ra, csr_bad_impl
	li a1, 0xdab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdab
	jal ra, csr_bad_impl
	li a1, 0xdac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdac
	jal ra, csr_bad_impl
	li a1, 0xdad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdad
	jal ra, csr_bad_impl
	li a1, 0xdae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdae
	jal ra, csr_bad_impl
	li a1, 0xdaf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdaf
	jal ra, csr_bad_impl
	li a1, 0xdb0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdb0
	jal ra, csr_bad_impl
	li a1, 0xdb1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdb1
	jal ra, csr_bad_impl
	li a1, 0xdb2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdb2
	jal ra, csr_bad_impl
	li a1, 0xdb3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdb3
	jal ra, csr_bad_impl
	li a1, 0xdb4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdb4
	jal ra, csr_bad_impl
	li a1, 0xdb5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdb5
	jal ra, csr_bad_impl
	li a1, 0xdb6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdb6
	jal ra, csr_bad_impl
	li a1, 0xdb7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdb7
	jal ra, csr_bad_impl
	li a1, 0xdb8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdb8
	jal ra, csr_bad_impl
	li a1, 0xdb9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdb9
	jal ra, csr_bad_impl
	li a1, 0xdba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdba
	jal ra, csr_bad_impl
	li a1, 0xdbb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdbb
	jal ra, csr_bad_impl
	li a1, 0xdbc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdbc
	jal ra, csr_bad_impl
	li a1, 0xdbd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdbd
	jal ra, csr_bad_impl
	li a1, 0xdbe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdbe
	jal ra, csr_bad_impl
	li a1, 0xdbf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdbf
	jal ra, csr_bad_impl
	li a1, 0xdc0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdc0
	jal ra, csr_bad_impl
	li a1, 0xdc1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdc1
	jal ra, csr_bad_impl
	li a1, 0xdc2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdc2
	jal ra, csr_bad_impl
	li a1, 0xdc3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdc3
	jal ra, csr_bad_impl
	li a1, 0xdc4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdc4
	jal ra, csr_bad_impl
	li a1, 0xdc5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdc5
	jal ra, csr_bad_impl
	li a1, 0xdc6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdc6
	jal ra, csr_bad_impl
	li a1, 0xdc7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdc7
	jal ra, csr_bad_impl
	li a1, 0xdc8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdc8
	jal ra, csr_bad_impl
	li a1, 0xdc9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdc9
	jal ra, csr_bad_impl
	li a1, 0xdca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdca
	jal ra, csr_bad_impl
	li a1, 0xdcb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdcb
	jal ra, csr_bad_impl
	li a1, 0xdcc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdcc
	jal ra, csr_bad_impl
	li a1, 0xdcd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdcd
	jal ra, csr_bad_impl
	li a1, 0xdce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdce
	jal ra, csr_bad_impl
	li a1, 0xdcf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdcf
	jal ra, csr_bad_impl
	li a1, 0xdd0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdd0
	jal ra, csr_bad_impl
	li a1, 0xdd1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdd1
	jal ra, csr_bad_impl
	li a1, 0xdd2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdd2
	jal ra, csr_bad_impl
	li a1, 0xdd3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdd3
	jal ra, csr_bad_impl
	li a1, 0xdd4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdd4
	jal ra, csr_bad_impl
	li a1, 0xdd5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdd5
	jal ra, csr_bad_impl
	li a1, 0xdd6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdd6
	jal ra, csr_bad_impl
	li a1, 0xdd7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdd7
	jal ra, csr_bad_impl
	li a1, 0xdd8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdd8
	jal ra, csr_bad_impl
	li a1, 0xdd9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdd9
	jal ra, csr_bad_impl
	li a1, 0xdda
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdda
	jal ra, csr_bad_impl
	li a1, 0xddb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xddb
	jal ra, csr_bad_impl
	li a1, 0xddc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xddc
	jal ra, csr_bad_impl
	li a1, 0xddd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xddd
	jal ra, csr_bad_impl
	li a1, 0xdde
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdde
	jal ra, csr_bad_impl
	li a1, 0xddf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xddf
	jal ra, csr_bad_impl
	li a1, 0xde0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xde0
	jal ra, csr_bad_impl
	li a1, 0xde1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xde1
	jal ra, csr_bad_impl
	li a1, 0xde2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xde2
	jal ra, csr_bad_impl
	li a1, 0xde3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xde3
	jal ra, csr_bad_impl
	li a1, 0xde4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xde4
	jal ra, csr_bad_impl
	li a1, 0xde5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xde5
	jal ra, csr_bad_impl
	li a1, 0xde6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xde6
	jal ra, csr_bad_impl
	li a1, 0xde7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xde7
	jal ra, csr_bad_impl
	li a1, 0xde8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xde8
	jal ra, csr_bad_impl
	li a1, 0xde9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xde9
	jal ra, csr_bad_impl
	li a1, 0xdea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdea
	jal ra, csr_bad_impl
	li a1, 0xdeb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdeb
	jal ra, csr_bad_impl
	li a1, 0xdec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdec
	jal ra, csr_bad_impl
	li a1, 0xded
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xded
	jal ra, csr_bad_impl
	li a1, 0xdee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdee
	jal ra, csr_bad_impl
	li a1, 0xdef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdef
	jal ra, csr_bad_impl
	li a1, 0xdf0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdf0
	jal ra, csr_bad_impl
	li a1, 0xdf1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdf1
	jal ra, csr_bad_impl
	li a1, 0xdf2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdf2
	jal ra, csr_bad_impl
	li a1, 0xdf3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdf3
	jal ra, csr_bad_impl
	li a1, 0xdf4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdf4
	jal ra, csr_bad_impl
	li a1, 0xdf5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdf5
	jal ra, csr_bad_impl
	li a1, 0xdf6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdf6
	jal ra, csr_bad_impl
	li a1, 0xdf7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdf7
	jal ra, csr_bad_impl
	li a1, 0xdf8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdf8
	jal ra, csr_bad_impl
	li a1, 0xdf9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdf9
	jal ra, csr_bad_impl
	li a1, 0xdfa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdfa
	jal ra, csr_bad_impl
	li a1, 0xdfb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdfb
	jal ra, csr_bad_impl
	li a1, 0xdfc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdfc
	jal ra, csr_bad_impl
	li a1, 0xdfd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdfd
	jal ra, csr_bad_impl
	li a1, 0xdfe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdfe
	jal ra, csr_bad_impl
	li a1, 0xdff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xdff
	jal ra, csr_bad_impl
	li a1, 0xe00
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe00
	jal ra, csr_bad_impl
	li a1, 0xe01
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe01
	jal ra, csr_bad_impl
	li a1, 0xe02
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe02
	jal ra, csr_bad_impl
	li a1, 0xe03
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe03
	jal ra, csr_bad_impl
	li a1, 0xe04
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe04
	jal ra, csr_bad_impl
	li a1, 0xe05
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe05
	jal ra, csr_bad_impl
	li a1, 0xe06
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe06
	jal ra, csr_bad_impl
	li a1, 0xe07
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe07
	jal ra, csr_bad_impl
	li a1, 0xe08
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe08
	jal ra, csr_bad_impl
	li a1, 0xe09
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe09
	jal ra, csr_bad_impl
	li a1, 0xe0a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe0a
	jal ra, csr_bad_impl
	li a1, 0xe0b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe0b
	jal ra, csr_bad_impl
	li a1, 0xe0c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe0c
	jal ra, csr_bad_impl
	li a1, 0xe0d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe0d
	jal ra, csr_bad_impl
	li a1, 0xe0e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe0e
	jal ra, csr_bad_impl
	li a1, 0xe0f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe0f
	jal ra, csr_bad_impl
	li a1, 0xe10
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe10
	jal ra, csr_bad_impl
	li a1, 0xe11
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe11
	jal ra, csr_bad_impl
	li a1, 0xe12
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe12
	jal ra, csr_bad_impl
	li a1, 0xe13
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe13
	jal ra, csr_bad_impl
	li a1, 0xe14
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe14
	jal ra, csr_bad_impl
	li a1, 0xe15
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe15
	jal ra, csr_bad_impl
	li a1, 0xe16
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe16
	jal ra, csr_bad_impl
	li a1, 0xe17
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe17
	jal ra, csr_bad_impl
	li a1, 0xe18
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe18
	jal ra, csr_bad_impl
	li a1, 0xe19
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe19
	jal ra, csr_bad_impl
	li a1, 0xe1a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe1a
	jal ra, csr_bad_impl
	li a1, 0xe1b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe1b
	jal ra, csr_bad_impl
	li a1, 0xe1c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe1c
	jal ra, csr_bad_impl
	li a1, 0xe1d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe1d
	jal ra, csr_bad_impl
	li a1, 0xe1e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe1e
	jal ra, csr_bad_impl
	li a1, 0xe1f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe1f
	jal ra, csr_bad_impl
	li a1, 0xe20
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe20
	jal ra, csr_bad_impl
	li a1, 0xe21
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe21
	jal ra, csr_bad_impl
	li a1, 0xe22
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe22
	jal ra, csr_bad_impl
	li a1, 0xe23
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe23
	jal ra, csr_bad_impl
	li a1, 0xe24
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe24
	jal ra, csr_bad_impl
	li a1, 0xe25
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe25
	jal ra, csr_bad_impl
	li a1, 0xe26
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe26
	jal ra, csr_bad_impl
	li a1, 0xe27
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe27
	jal ra, csr_bad_impl
	li a1, 0xe28
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe28
	jal ra, csr_bad_impl
	li a1, 0xe29
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe29
	jal ra, csr_bad_impl
	li a1, 0xe2a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe2a
	jal ra, csr_bad_impl
	li a1, 0xe2b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe2b
	jal ra, csr_bad_impl
	li a1, 0xe2c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe2c
	jal ra, csr_bad_impl
	li a1, 0xe2d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe2d
	jal ra, csr_bad_impl
	li a1, 0xe2e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe2e
	jal ra, csr_bad_impl
	li a1, 0xe2f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe2f
	jal ra, csr_bad_impl
	li a1, 0xe30
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe30
	jal ra, csr_bad_impl
	li a1, 0xe31
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe31
	jal ra, csr_bad_impl
	li a1, 0xe32
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe32
	jal ra, csr_bad_impl
	li a1, 0xe33
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe33
	jal ra, csr_bad_impl
	li a1, 0xe34
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe34
	jal ra, csr_bad_impl
	li a1, 0xe35
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe35
	jal ra, csr_bad_impl
	li a1, 0xe36
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe36
	jal ra, csr_bad_impl
	li a1, 0xe37
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe37
	jal ra, csr_bad_impl
	li a1, 0xe38
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe38
	jal ra, csr_bad_impl
	li a1, 0xe39
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe39
	jal ra, csr_bad_impl
	li a1, 0xe3a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe3a
	jal ra, csr_bad_impl
	li a1, 0xe3b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe3b
	jal ra, csr_bad_impl
	li a1, 0xe3c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe3c
	jal ra, csr_bad_impl
	li a1, 0xe3d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe3d
	jal ra, csr_bad_impl
	li a1, 0xe3e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe3e
	jal ra, csr_bad_impl
	li a1, 0xe3f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe3f
	jal ra, csr_bad_impl
	li a1, 0xe40
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe40
	jal ra, csr_bad_impl
	li a1, 0xe41
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe41
	jal ra, csr_bad_impl
	li a1, 0xe42
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe42
	jal ra, csr_bad_impl
	li a1, 0xe43
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe43
	jal ra, csr_bad_impl
	li a1, 0xe44
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe44
	jal ra, csr_bad_impl
	li a1, 0xe45
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe45
	jal ra, csr_bad_impl
	li a1, 0xe46
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe46
	jal ra, csr_bad_impl
	li a1, 0xe47
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe47
	jal ra, csr_bad_impl
	li a1, 0xe48
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe48
	jal ra, csr_bad_impl
	li a1, 0xe49
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe49
	jal ra, csr_bad_impl
	li a1, 0xe4a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe4a
	jal ra, csr_bad_impl
	li a1, 0xe4b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe4b
	jal ra, csr_bad_impl
	li a1, 0xe4c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe4c
	jal ra, csr_bad_impl
	li a1, 0xe4d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe4d
	jal ra, csr_bad_impl
	li a1, 0xe4e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe4e
	jal ra, csr_bad_impl
	li a1, 0xe4f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe4f
	jal ra, csr_bad_impl
	li a1, 0xe50
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe50
	jal ra, csr_bad_impl
	li a1, 0xe51
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe51
	jal ra, csr_bad_impl
	li a1, 0xe52
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe52
	jal ra, csr_bad_impl
	li a1, 0xe53
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe53
	jal ra, csr_bad_impl
	li a1, 0xe54
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe54
	jal ra, csr_bad_impl
	li a1, 0xe55
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe55
	jal ra, csr_bad_impl
	li a1, 0xe56
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe56
	jal ra, csr_bad_impl
	li a1, 0xe57
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe57
	jal ra, csr_bad_impl
	li a1, 0xe58
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe58
	jal ra, csr_bad_impl
	li a1, 0xe59
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe59
	jal ra, csr_bad_impl
	li a1, 0xe5a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe5a
	jal ra, csr_bad_impl
	li a1, 0xe5b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe5b
	jal ra, csr_bad_impl
	li a1, 0xe5c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe5c
	jal ra, csr_bad_impl
	li a1, 0xe5d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe5d
	jal ra, csr_bad_impl
	li a1, 0xe5e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe5e
	jal ra, csr_bad_impl
	li a1, 0xe5f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe5f
	jal ra, csr_bad_impl
	li a1, 0xe60
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe60
	jal ra, csr_bad_impl
	li a1, 0xe61
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe61
	jal ra, csr_bad_impl
	li a1, 0xe62
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe62
	jal ra, csr_bad_impl
	li a1, 0xe63
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe63
	jal ra, csr_bad_impl
	li a1, 0xe64
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe64
	jal ra, csr_bad_impl
	li a1, 0xe65
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe65
	jal ra, csr_bad_impl
	li a1, 0xe66
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe66
	jal ra, csr_bad_impl
	li a1, 0xe67
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe67
	jal ra, csr_bad_impl
	li a1, 0xe68
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe68
	jal ra, csr_bad_impl
	li a1, 0xe69
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe69
	jal ra, csr_bad_impl
	li a1, 0xe6a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe6a
	jal ra, csr_bad_impl
	li a1, 0xe6b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe6b
	jal ra, csr_bad_impl
	li a1, 0xe6c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe6c
	jal ra, csr_bad_impl
	li a1, 0xe6d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe6d
	jal ra, csr_bad_impl
	li a1, 0xe6e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe6e
	jal ra, csr_bad_impl
	li a1, 0xe6f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe6f
	jal ra, csr_bad_impl
	li a1, 0xe70
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe70
	jal ra, csr_bad_impl
	li a1, 0xe71
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe71
	jal ra, csr_bad_impl
	li a1, 0xe72
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe72
	jal ra, csr_bad_impl
	li a1, 0xe73
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe73
	jal ra, csr_bad_impl
	li a1, 0xe74
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe74
	jal ra, csr_bad_impl
	li a1, 0xe75
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe75
	jal ra, csr_bad_impl
	li a1, 0xe76
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe76
	jal ra, csr_bad_impl
	li a1, 0xe77
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe77
	jal ra, csr_bad_impl
	li a1, 0xe78
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe78
	jal ra, csr_bad_impl
	li a1, 0xe79
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe79
	jal ra, csr_bad_impl
	li a1, 0xe7a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe7a
	jal ra, csr_bad_impl
	li a1, 0xe7b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe7b
	jal ra, csr_bad_impl
	li a1, 0xe7c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe7c
	jal ra, csr_bad_impl
	li a1, 0xe7d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe7d
	jal ra, csr_bad_impl
	li a1, 0xe7e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe7e
	jal ra, csr_bad_impl
	li a1, 0xe7f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe7f
	jal ra, csr_bad_impl
	li a1, 0xe80
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe80
	jal ra, csr_bad_impl
	li a1, 0xe81
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe81
	jal ra, csr_bad_impl
	li a1, 0xe82
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe82
	jal ra, csr_bad_impl
	li a1, 0xe83
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe83
	jal ra, csr_bad_impl
	li a1, 0xe84
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe84
	jal ra, csr_bad_impl
	li a1, 0xe85
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe85
	jal ra, csr_bad_impl
	li a1, 0xe86
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe86
	jal ra, csr_bad_impl
	li a1, 0xe87
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe87
	jal ra, csr_bad_impl
	li a1, 0xe88
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe88
	jal ra, csr_bad_impl
	li a1, 0xe89
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe89
	jal ra, csr_bad_impl
	li a1, 0xe8a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe8a
	jal ra, csr_bad_impl
	li a1, 0xe8b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe8b
	jal ra, csr_bad_impl
	li a1, 0xe8c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe8c
	jal ra, csr_bad_impl
	li a1, 0xe8d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe8d
	jal ra, csr_bad_impl
	li a1, 0xe8e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe8e
	jal ra, csr_bad_impl
	li a1, 0xe8f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe8f
	jal ra, csr_bad_impl
	li a1, 0xe90
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe90
	jal ra, csr_bad_impl
	li a1, 0xe91
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe91
	jal ra, csr_bad_impl
	li a1, 0xe92
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe92
	jal ra, csr_bad_impl
	li a1, 0xe93
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe93
	jal ra, csr_bad_impl
	li a1, 0xe94
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe94
	jal ra, csr_bad_impl
	li a1, 0xe95
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe95
	jal ra, csr_bad_impl
	li a1, 0xe96
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe96
	jal ra, csr_bad_impl
	li a1, 0xe97
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe97
	jal ra, csr_bad_impl
	li a1, 0xe98
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe98
	jal ra, csr_bad_impl
	li a1, 0xe99
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe99
	jal ra, csr_bad_impl
	li a1, 0xe9a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe9a
	jal ra, csr_bad_impl
	li a1, 0xe9b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe9b
	jal ra, csr_bad_impl
	li a1, 0xe9c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe9c
	jal ra, csr_bad_impl
	li a1, 0xe9d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe9d
	jal ra, csr_bad_impl
	li a1, 0xe9e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe9e
	jal ra, csr_bad_impl
	li a1, 0xe9f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xe9f
	jal ra, csr_bad_impl
	li a1, 0xea0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xea0
	jal ra, csr_bad_impl
	li a1, 0xea1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xea1
	jal ra, csr_bad_impl
	li a1, 0xea2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xea2
	jal ra, csr_bad_impl
	li a1, 0xea3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xea3
	jal ra, csr_bad_impl
	li a1, 0xea4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xea4
	jal ra, csr_bad_impl
	li a1, 0xea5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xea5
	jal ra, csr_bad_impl
	li a1, 0xea6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xea6
	jal ra, csr_bad_impl
	li a1, 0xea7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xea7
	jal ra, csr_bad_impl
	li a1, 0xea8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xea8
	jal ra, csr_bad_impl
	li a1, 0xea9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xea9
	jal ra, csr_bad_impl
	li a1, 0xeaa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeaa
	jal ra, csr_bad_impl
	li a1, 0xeab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeab
	jal ra, csr_bad_impl
	li a1, 0xeac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeac
	jal ra, csr_bad_impl
	li a1, 0xead
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xead
	jal ra, csr_bad_impl
	li a1, 0xeae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeae
	jal ra, csr_bad_impl
	li a1, 0xeaf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeaf
	jal ra, csr_bad_impl
	li a1, 0xeb0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeb0
	jal ra, csr_bad_impl
	li a1, 0xeb1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeb1
	jal ra, csr_bad_impl
	li a1, 0xeb2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeb2
	jal ra, csr_bad_impl
	li a1, 0xeb3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeb3
	jal ra, csr_bad_impl
	li a1, 0xeb4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeb4
	jal ra, csr_bad_impl
	li a1, 0xeb5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeb5
	jal ra, csr_bad_impl
	li a1, 0xeb6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeb6
	jal ra, csr_bad_impl
	li a1, 0xeb7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeb7
	jal ra, csr_bad_impl
	li a1, 0xeb8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeb8
	jal ra, csr_bad_impl
	li a1, 0xeb9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeb9
	jal ra, csr_bad_impl
	li a1, 0xeba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeba
	jal ra, csr_bad_impl
	li a1, 0xebb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xebb
	jal ra, csr_bad_impl
	li a1, 0xebc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xebc
	jal ra, csr_bad_impl
	li a1, 0xebd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xebd
	jal ra, csr_bad_impl
	li a1, 0xebe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xebe
	jal ra, csr_bad_impl
	li a1, 0xebf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xebf
	jal ra, csr_bad_impl
	li a1, 0xec0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xec0
	jal ra, csr_bad_impl
	li a1, 0xec1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xec1
	jal ra, csr_bad_impl
	li a1, 0xec2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xec2
	jal ra, csr_bad_impl
	li a1, 0xec3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xec3
	jal ra, csr_bad_impl
	li a1, 0xec4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xec4
	jal ra, csr_bad_impl
	li a1, 0xec5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xec5
	jal ra, csr_bad_impl
	li a1, 0xec6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xec6
	jal ra, csr_bad_impl
	li a1, 0xec7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xec7
	jal ra, csr_bad_impl
	li a1, 0xec8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xec8
	jal ra, csr_bad_impl
	li a1, 0xec9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xec9
	jal ra, csr_bad_impl
	li a1, 0xeca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeca
	jal ra, csr_bad_impl
	li a1, 0xecb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xecb
	jal ra, csr_bad_impl
	li a1, 0xecc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xecc
	jal ra, csr_bad_impl
	li a1, 0xecd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xecd
	jal ra, csr_bad_impl
	li a1, 0xece
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xece
	jal ra, csr_bad_impl
	li a1, 0xecf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xecf
	jal ra, csr_bad_impl
	li a1, 0xed0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xed0
	jal ra, csr_bad_impl
	li a1, 0xed1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xed1
	jal ra, csr_bad_impl
	li a1, 0xed2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xed2
	jal ra, csr_bad_impl
	li a1, 0xed3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xed3
	jal ra, csr_bad_impl
	li a1, 0xed4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xed4
	jal ra, csr_bad_impl
	li a1, 0xed5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xed5
	jal ra, csr_bad_impl
	li a1, 0xed6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xed6
	jal ra, csr_bad_impl
	li a1, 0xed7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xed7
	jal ra, csr_bad_impl
	li a1, 0xed8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xed8
	jal ra, csr_bad_impl
	li a1, 0xed9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xed9
	jal ra, csr_bad_impl
	li a1, 0xeda
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeda
	jal ra, csr_bad_impl
	li a1, 0xedb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xedb
	jal ra, csr_bad_impl
	li a1, 0xedc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xedc
	jal ra, csr_bad_impl
	li a1, 0xedd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xedd
	jal ra, csr_bad_impl
	li a1, 0xede
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xede
	jal ra, csr_bad_impl
	li a1, 0xedf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xedf
	jal ra, csr_bad_impl
	li a1, 0xee0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xee0
	jal ra, csr_bad_impl
	li a1, 0xee1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xee1
	jal ra, csr_bad_impl
	li a1, 0xee2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xee2
	jal ra, csr_bad_impl
	li a1, 0xee3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xee3
	jal ra, csr_bad_impl
	li a1, 0xee4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xee4
	jal ra, csr_bad_impl
	li a1, 0xee5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xee5
	jal ra, csr_bad_impl
	li a1, 0xee6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xee6
	jal ra, csr_bad_impl
	li a1, 0xee7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xee7
	jal ra, csr_bad_impl
	li a1, 0xee8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xee8
	jal ra, csr_bad_impl
	li a1, 0xee9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xee9
	jal ra, csr_bad_impl
	li a1, 0xeea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeea
	jal ra, csr_bad_impl
	li a1, 0xeeb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeeb
	jal ra, csr_bad_impl
	li a1, 0xeec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeec
	jal ra, csr_bad_impl
	li a1, 0xeed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeed
	jal ra, csr_bad_impl
	li a1, 0xeee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeee
	jal ra, csr_bad_impl
	li a1, 0xeef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeef
	jal ra, csr_bad_impl
	li a1, 0xef0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xef0
	jal ra, csr_bad_impl
	li a1, 0xef1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xef1
	jal ra, csr_bad_impl
	li a1, 0xef2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xef2
	jal ra, csr_bad_impl
	li a1, 0xef3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xef3
	jal ra, csr_bad_impl
	li a1, 0xef4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xef4
	jal ra, csr_bad_impl
	li a1, 0xef5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xef5
	jal ra, csr_bad_impl
	li a1, 0xef6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xef6
	jal ra, csr_bad_impl
	li a1, 0xef7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xef7
	jal ra, csr_bad_impl
	li a1, 0xef8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xef8
	jal ra, csr_bad_impl
	li a1, 0xef9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xef9
	jal ra, csr_bad_impl
	li a1, 0xefa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xefa
	jal ra, csr_bad_impl
	li a1, 0xefb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xefb
	jal ra, csr_bad_impl
	li a1, 0xefc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xefc
	jal ra, csr_bad_impl
	li a1, 0xefd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xefd
	jal ra, csr_bad_impl
	li a1, 0xefe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xefe
	jal ra, csr_bad_impl
	li a1, 0xeff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xeff
	jal ra, csr_bad_impl
	li a1, 0xf00
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf00
	jal ra, csr_bad_impl
	li a1, 0xf01
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf01
	jal ra, csr_bad_impl
	li a1, 0xf02
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf02
	jal ra, csr_bad_impl
	li a1, 0xf03
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf03
	jal ra, csr_bad_impl
	li a1, 0xf04
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf04
	jal ra, csr_bad_impl
	li a1, 0xf05
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf05
	jal ra, csr_bad_impl
	li a1, 0xf06
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf06
	jal ra, csr_bad_impl
	li a1, 0xf07
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf07
	jal ra, csr_bad_impl
	li a1, 0xf08
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf08
	jal ra, csr_bad_impl
	li a1, 0xf09
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf09
	jal ra, csr_bad_impl
	li a1, 0xf0a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf0a
	jal ra, csr_bad_impl
	li a1, 0xf0b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf0b
	jal ra, csr_bad_impl
	li a1, 0xf0c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf0c
	jal ra, csr_bad_impl
	li a1, 0xf0d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf0d
	jal ra, csr_bad_impl
	li a1, 0xf0e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf0e
	jal ra, csr_bad_impl
	li a1, 0xf0f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf0f
	jal ra, csr_bad_impl
	li a1, 0xf10
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf10
	jal ra, csr_bad_impl
	li a1, 0xf16
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf16
	jal ra, csr_bad_impl
	li a1, 0xf17
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf17
	jal ra, csr_bad_impl
	li a1, 0xf18
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf18
	jal ra, csr_bad_impl
	li a1, 0xf19
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf19
	jal ra, csr_bad_impl
	li a1, 0xf1a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf1a
	jal ra, csr_bad_impl
	li a1, 0xf1b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf1b
	jal ra, csr_bad_impl
	li a1, 0xf1c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf1c
	jal ra, csr_bad_impl
	li a1, 0xf1d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf1d
	jal ra, csr_bad_impl
	li a1, 0xf1e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf1e
	jal ra, csr_bad_impl
	li a1, 0xf1f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf1f
	jal ra, csr_bad_impl
	li a1, 0xf20
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf20
	jal ra, csr_bad_impl
	li a1, 0xf21
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf21
	jal ra, csr_bad_impl
	li a1, 0xf22
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf22
	jal ra, csr_bad_impl
	li a1, 0xf23
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf23
	jal ra, csr_bad_impl
	li a1, 0xf24
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf24
	jal ra, csr_bad_impl
	li a1, 0xf25
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf25
	jal ra, csr_bad_impl
	li a1, 0xf26
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf26
	jal ra, csr_bad_impl
	li a1, 0xf27
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf27
	jal ra, csr_bad_impl
	li a1, 0xf28
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf28
	jal ra, csr_bad_impl
	li a1, 0xf29
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf29
	jal ra, csr_bad_impl
	li a1, 0xf2a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf2a
	jal ra, csr_bad_impl
	li a1, 0xf2b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf2b
	jal ra, csr_bad_impl
	li a1, 0xf2c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf2c
	jal ra, csr_bad_impl
	li a1, 0xf2d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf2d
	jal ra, csr_bad_impl
	li a1, 0xf2e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf2e
	jal ra, csr_bad_impl
	li a1, 0xf2f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf2f
	jal ra, csr_bad_impl
	li a1, 0xf30
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf30
	jal ra, csr_bad_impl
	li a1, 0xf31
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf31
	jal ra, csr_bad_impl
	li a1, 0xf32
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf32
	jal ra, csr_bad_impl
	li a1, 0xf33
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf33
	jal ra, csr_bad_impl
	li a1, 0xf34
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf34
	jal ra, csr_bad_impl
	li a1, 0xf35
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf35
	jal ra, csr_bad_impl
	li a1, 0xf36
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf36
	jal ra, csr_bad_impl
	li a1, 0xf37
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf37
	jal ra, csr_bad_impl
	li a1, 0xf38
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf38
	jal ra, csr_bad_impl
	li a1, 0xf39
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf39
	jal ra, csr_bad_impl
	li a1, 0xf3a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf3a
	jal ra, csr_bad_impl
	li a1, 0xf3b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf3b
	jal ra, csr_bad_impl
	li a1, 0xf3c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf3c
	jal ra, csr_bad_impl
	li a1, 0xf3d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf3d
	jal ra, csr_bad_impl
	li a1, 0xf3e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf3e
	jal ra, csr_bad_impl
	li a1, 0xf3f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf3f
	jal ra, csr_bad_impl
	li a1, 0xf40
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf40
	jal ra, csr_bad_impl
	li a1, 0xf41
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf41
	jal ra, csr_bad_impl
	li a1, 0xf42
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf42
	jal ra, csr_bad_impl
	li a1, 0xf43
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf43
	jal ra, csr_bad_impl
	li a1, 0xf44
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf44
	jal ra, csr_bad_impl
	li a1, 0xf45
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf45
	jal ra, csr_bad_impl
	li a1, 0xf46
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf46
	jal ra, csr_bad_impl
	li a1, 0xf47
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf47
	jal ra, csr_bad_impl
	li a1, 0xf48
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf48
	jal ra, csr_bad_impl
	li a1, 0xf49
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf49
	jal ra, csr_bad_impl
	li a1, 0xf4a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf4a
	jal ra, csr_bad_impl
	li a1, 0xf4b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf4b
	jal ra, csr_bad_impl
	li a1, 0xf4c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf4c
	jal ra, csr_bad_impl
	li a1, 0xf4d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf4d
	jal ra, csr_bad_impl
	li a1, 0xf4e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf4e
	jal ra, csr_bad_impl
	li a1, 0xf4f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf4f
	jal ra, csr_bad_impl
	li a1, 0xf50
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf50
	jal ra, csr_bad_impl
	li a1, 0xf51
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf51
	jal ra, csr_bad_impl
	li a1, 0xf52
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf52
	jal ra, csr_bad_impl
	li a1, 0xf53
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf53
	jal ra, csr_bad_impl
	li a1, 0xf54
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf54
	jal ra, csr_bad_impl
	li a1, 0xf55
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf55
	jal ra, csr_bad_impl
	li a1, 0xf56
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf56
	jal ra, csr_bad_impl
	li a1, 0xf57
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf57
	jal ra, csr_bad_impl
	li a1, 0xf58
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf58
	jal ra, csr_bad_impl
	li a1, 0xf59
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf59
	jal ra, csr_bad_impl
	li a1, 0xf5a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf5a
	jal ra, csr_bad_impl
	li a1, 0xf5b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf5b
	jal ra, csr_bad_impl
	li a1, 0xf5c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf5c
	jal ra, csr_bad_impl
	li a1, 0xf5d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf5d
	jal ra, csr_bad_impl
	li a1, 0xf5e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf5e
	jal ra, csr_bad_impl
	li a1, 0xf5f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf5f
	jal ra, csr_bad_impl
	li a1, 0xf60
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf60
	jal ra, csr_bad_impl
	li a1, 0xf61
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf61
	jal ra, csr_bad_impl
	li a1, 0xf62
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf62
	jal ra, csr_bad_impl
	li a1, 0xf63
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf63
	jal ra, csr_bad_impl
	li a1, 0xf64
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf64
	jal ra, csr_bad_impl
	li a1, 0xf65
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf65
	jal ra, csr_bad_impl
	li a1, 0xf66
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf66
	jal ra, csr_bad_impl
	li a1, 0xf67
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf67
	jal ra, csr_bad_impl
	li a1, 0xf68
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf68
	jal ra, csr_bad_impl
	li a1, 0xf69
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf69
	jal ra, csr_bad_impl
	li a1, 0xf6a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf6a
	jal ra, csr_bad_impl
	li a1, 0xf6b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf6b
	jal ra, csr_bad_impl
	li a1, 0xf6c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf6c
	jal ra, csr_bad_impl
	li a1, 0xf6d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf6d
	jal ra, csr_bad_impl
	li a1, 0xf6e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf6e
	jal ra, csr_bad_impl
	li a1, 0xf6f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf6f
	jal ra, csr_bad_impl
	li a1, 0xf70
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf70
	jal ra, csr_bad_impl
	li a1, 0xf71
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf71
	jal ra, csr_bad_impl
	li a1, 0xf72
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf72
	jal ra, csr_bad_impl
	li a1, 0xf73
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf73
	jal ra, csr_bad_impl
	li a1, 0xf74
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf74
	jal ra, csr_bad_impl
	li a1, 0xf75
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf75
	jal ra, csr_bad_impl
	li a1, 0xf76
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf76
	jal ra, csr_bad_impl
	li a1, 0xf77
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf77
	jal ra, csr_bad_impl
	li a1, 0xf78
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf78
	jal ra, csr_bad_impl
	li a1, 0xf79
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf79
	jal ra, csr_bad_impl
	li a1, 0xf7a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf7a
	jal ra, csr_bad_impl
	li a1, 0xf7b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf7b
	jal ra, csr_bad_impl
	li a1, 0xf7c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf7c
	jal ra, csr_bad_impl
	li a1, 0xf7d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf7d
	jal ra, csr_bad_impl
	li a1, 0xf7e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf7e
	jal ra, csr_bad_impl
	li a1, 0xf7f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf7f
	jal ra, csr_bad_impl
	li a1, 0xf80
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf80
	jal ra, csr_bad_impl
	li a1, 0xf81
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf81
	jal ra, csr_bad_impl
	li a1, 0xf82
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf82
	jal ra, csr_bad_impl
	li a1, 0xf83
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf83
	jal ra, csr_bad_impl
	li a1, 0xf84
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf84
	jal ra, csr_bad_impl
	li a1, 0xf85
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf85
	jal ra, csr_bad_impl
	li a1, 0xf86
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf86
	jal ra, csr_bad_impl
	li a1, 0xf87
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf87
	jal ra, csr_bad_impl
	li a1, 0xf88
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf88
	jal ra, csr_bad_impl
	li a1, 0xf89
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf89
	jal ra, csr_bad_impl
	li a1, 0xf8a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf8a
	jal ra, csr_bad_impl
	li a1, 0xf8b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf8b
	jal ra, csr_bad_impl
	li a1, 0xf8c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf8c
	jal ra, csr_bad_impl
	li a1, 0xf8d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf8d
	jal ra, csr_bad_impl
	li a1, 0xf8e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf8e
	jal ra, csr_bad_impl
	li a1, 0xf8f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf8f
	jal ra, csr_bad_impl
	li a1, 0xf90
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf90
	jal ra, csr_bad_impl
	li a1, 0xf91
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf91
	jal ra, csr_bad_impl
	li a1, 0xf92
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf92
	jal ra, csr_bad_impl
	li a1, 0xf93
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf93
	jal ra, csr_bad_impl
	li a1, 0xf94
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf94
	jal ra, csr_bad_impl
	li a1, 0xf95
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf95
	jal ra, csr_bad_impl
	li a1, 0xf96
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf96
	jal ra, csr_bad_impl
	li a1, 0xf97
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf97
	jal ra, csr_bad_impl
	li a1, 0xf98
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf98
	jal ra, csr_bad_impl
	li a1, 0xf99
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf99
	jal ra, csr_bad_impl
	li a1, 0xf9a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf9a
	jal ra, csr_bad_impl
	li a1, 0xf9b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf9b
	jal ra, csr_bad_impl
	li a1, 0xf9c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf9c
	jal ra, csr_bad_impl
	li a1, 0xf9d
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf9d
	jal ra, csr_bad_impl
	li a1, 0xf9e
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf9e
	jal ra, csr_bad_impl
	li a1, 0xf9f
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xf9f
	jal ra, csr_bad_impl
	li a1, 0xfa0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfa0
	jal ra, csr_bad_impl
	li a1, 0xfa1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfa1
	jal ra, csr_bad_impl
	li a1, 0xfa2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfa2
	jal ra, csr_bad_impl
	li a1, 0xfa3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfa3
	jal ra, csr_bad_impl
	li a1, 0xfa4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfa4
	jal ra, csr_bad_impl
	li a1, 0xfa5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfa5
	jal ra, csr_bad_impl
	li a1, 0xfa6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfa6
	jal ra, csr_bad_impl
	li a1, 0xfa7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfa7
	jal ra, csr_bad_impl
	li a1, 0xfa8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfa8
	jal ra, csr_bad_impl
	li a1, 0xfa9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfa9
	jal ra, csr_bad_impl
	li a1, 0xfaa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfaa
	jal ra, csr_bad_impl
	li a1, 0xfab
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfab
	jal ra, csr_bad_impl
	li a1, 0xfac
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfac
	jal ra, csr_bad_impl
	li a1, 0xfad
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfad
	jal ra, csr_bad_impl
	li a1, 0xfae
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfae
	jal ra, csr_bad_impl
	li a1, 0xfaf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfaf
	jal ra, csr_bad_impl
	li a1, 0xfb0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfb0
	jal ra, csr_bad_impl
	li a1, 0xfb1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfb1
	jal ra, csr_bad_impl
	li a1, 0xfb2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfb2
	jal ra, csr_bad_impl
	li a1, 0xfb3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfb3
	jal ra, csr_bad_impl
	li a1, 0xfb4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfb4
	jal ra, csr_bad_impl
	li a1, 0xfb5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfb5
	jal ra, csr_bad_impl
	li a1, 0xfb6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfb6
	jal ra, csr_bad_impl
	li a1, 0xfb7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfb7
	jal ra, csr_bad_impl
	li a1, 0xfb8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfb8
	jal ra, csr_bad_impl
	li a1, 0xfb9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfb9
	jal ra, csr_bad_impl
	li a1, 0xfba
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfba
	jal ra, csr_bad_impl
	li a1, 0xfbb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfbb
	jal ra, csr_bad_impl
	li a1, 0xfbc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfbc
	jal ra, csr_bad_impl
	li a1, 0xfbd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfbd
	jal ra, csr_bad_impl
	li a1, 0xfbe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfbe
	jal ra, csr_bad_impl
	li a1, 0xfbf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfbf
	jal ra, csr_bad_impl
	li a1, 0xfc0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfc0
	jal ra, csr_bad_impl
	li a1, 0xfc1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfc1
	jal ra, csr_bad_impl
	li a1, 0xfc2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfc2
	jal ra, csr_bad_impl
	li a1, 0xfc3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfc3
	jal ra, csr_bad_impl
	li a1, 0xfc4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfc4
	jal ra, csr_bad_impl
	li a1, 0xfc5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfc5
	jal ra, csr_bad_impl
	li a1, 0xfc6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfc6
	jal ra, csr_bad_impl
	li a1, 0xfc7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfc7
	jal ra, csr_bad_impl
	li a1, 0xfc8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfc8
	jal ra, csr_bad_impl
	li a1, 0xfc9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfc9
	jal ra, csr_bad_impl
	li a1, 0xfca
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfca
	jal ra, csr_bad_impl
	li a1, 0xfcb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfcb
	jal ra, csr_bad_impl
	li a1, 0xfcc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfcc
	jal ra, csr_bad_impl
	li a1, 0xfcd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfcd
	jal ra, csr_bad_impl
	li a1, 0xfce
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfce
	jal ra, csr_bad_impl
	li a1, 0xfcf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfcf
	jal ra, csr_bad_impl
	li a1, 0xfd0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfd0
	jal ra, csr_bad_impl
	li a1, 0xfd1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfd1
	jal ra, csr_bad_impl
	li a1, 0xfd2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfd2
	jal ra, csr_bad_impl
	li a1, 0xfd3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfd3
	jal ra, csr_bad_impl
	li a1, 0xfd4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfd4
	jal ra, csr_bad_impl
	li a1, 0xfd5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfd5
	jal ra, csr_bad_impl
	li a1, 0xfd6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfd6
	jal ra, csr_bad_impl
	li a1, 0xfd7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfd7
	jal ra, csr_bad_impl
	li a1, 0xfd8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfd8
	jal ra, csr_bad_impl
	li a1, 0xfd9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfd9
	jal ra, csr_bad_impl
	li a1, 0xfda
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfda
	jal ra, csr_bad_impl
	li a1, 0xfdb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfdb
	jal ra, csr_bad_impl
	li a1, 0xfdc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfdc
	jal ra, csr_bad_impl
	li a1, 0xfdd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfdd
	jal ra, csr_bad_impl
	li a1, 0xfde
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfde
	jal ra, csr_bad_impl
	li a1, 0xfdf
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfdf
	jal ra, csr_bad_impl
	li a1, 0xfe0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfe0
	jal ra, csr_bad_impl
	li a1, 0xfe1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfe1
	jal ra, csr_bad_impl
	li a1, 0xfe2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfe2
	jal ra, csr_bad_impl
	li a1, 0xfe3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfe3
	jal ra, csr_bad_impl
	li a1, 0xfe4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfe4
	jal ra, csr_bad_impl
	li a1, 0xfe5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfe5
	jal ra, csr_bad_impl
	li a1, 0xfe6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfe6
	jal ra, csr_bad_impl
	li a1, 0xfe7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfe7
	jal ra, csr_bad_impl
	li a1, 0xfe8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfe8
	jal ra, csr_bad_impl
	li a1, 0xfe9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfe9
	jal ra, csr_bad_impl
	li a1, 0xfea
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfea
	jal ra, csr_bad_impl
	li a1, 0xfeb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfeb
	jal ra, csr_bad_impl
	li a1, 0xfec
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfec
	jal ra, csr_bad_impl
	li a1, 0xfed
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfed
	jal ra, csr_bad_impl
	li a1, 0xfee
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfee
	jal ra, csr_bad_impl
	li a1, 0xfef
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfef
	jal ra, csr_bad_impl
	li a1, 0xff0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xff0
	jal ra, csr_bad_impl
	li a1, 0xff1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xff1
	jal ra, csr_bad_impl
	li a1, 0xff2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xff2
	jal ra, csr_bad_impl
	li a1, 0xff3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xff3
	jal ra, csr_bad_impl
	li a1, 0xff4
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xff4
	jal ra, csr_bad_impl
	li a1, 0xff5
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xff5
	jal ra, csr_bad_impl
	li a1, 0xff6
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xff6
	jal ra, csr_bad_impl
	li a1, 0xff7
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xff7
	jal ra, csr_bad_impl
	li a1, 0xff8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xff8
	jal ra, csr_bad_impl
	li a1, 0xff9
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xff9
	jal ra, csr_bad_impl
	li a1, 0xffa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xffa
	jal ra, csr_bad_impl
	li a1, 0xffb
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xffb
	jal ra, csr_bad_impl
	li a1, 0xffc
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xffc
	jal ra, csr_bad_impl
	li a1, 0xffd
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xffd
	jal ra, csr_bad_impl
	li a1, 0xffe
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xffe
	jal ra, csr_bad_impl
	li a1, 0xfff
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrr t0, 0xfff
	jal ra, csr_bad_impl
	lw ra, 0(sp)
	addi sp, sp, 4
	ret
.globl user_mode_check
user_mode_check:	la t1, glb_expect_illegal_insn
	# cycle
	li a1, 0xc00
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc00,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc00,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc00,0x0
	j csr_user_unauth
	csrrs x13, 0xc00,0x0
	li x12, 0x00000000
	csrrs x13, 0xc00,0x0
	li x12, 0x00000000
	csrrs x13, 0xc00,0x0
	li x12, 0x00000000
	csrrc x13, 0xc00,0x0
	li x12, 0x00000000
	csrrc x13, 0xc00,0x0
	li x12, 0x00000000
	csrrc x13, 0xc00,0x0
	li x12, 0x00000000
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc00, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc00, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc00, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xc00, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc00, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc00, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc00, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc00, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc00, 0b00000
	li x12, 0x00000000
	# instret
	li a1, 0xc02
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc02,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc02,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc02,0x0
	j csr_user_unauth
	csrrs x13, 0xc02,0x0
	li x12, 0x00000000
	csrrs x13, 0xc02,0x0
	li x12, 0x00000000
	csrrs x13, 0xc02,0x0
	li x12, 0x00000000
	csrrc x13, 0xc02,0x0
	li x12, 0x00000000
	csrrc x13, 0xc02,0x0
	li x12, 0x00000000
	csrrc x13, 0xc02,0x0
	li x12, 0x00000000
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc02, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc02, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc02, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xc02, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc02, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc02, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc02, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc02, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc02, 0b00000
	li x12, 0x00000000
	# cycleh
	li a1, 0xc80
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc80,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc80,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc80,0x0
	j csr_user_unauth
	csrrs x13, 0xc80,0x0
	li x12, 0x00000000
	csrrs x13, 0xc80,0x0
	li x12, 0x00000000
	csrrs x13, 0xc80,0x0
	li x12, 0x00000000
	csrrc x13, 0xc80,0x0
	li x12, 0x00000000
	csrrc x13, 0xc80,0x0
	li x12, 0x00000000
	csrrc x13, 0xc80,0x0
	li x12, 0x00000000
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc80, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc80, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc80, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xc80, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc80, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc80, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc80, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc80, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc80, 0b00000
	li x12, 0x00000000
	# instreth
	li a1, 0xc82
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc82,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc82,0x0
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xc82,0x0
	j csr_user_unauth
	csrrs x13, 0xc82,0x0
	li x12, 0x00000000
	csrrs x13, 0xc82,0x0
	li x12, 0x00000000
	csrrs x13, 0xc82,0x0
	li x12, 0x00000000
	csrrc x13, 0xc82,0x0
	li x12, 0x00000000
	csrrc x13, 0xc82,0x0
	li x12, 0x00000000
	csrrc x13, 0xc82,0x0
	li x12, 0x00000000
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc82, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc82, 0b00000
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xc82, 0b00000
	j csr_user_unauth
	csrrsi x13, 0xc82, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc82, 0b00000
	li x12, 0x00000000
	csrrsi x13, 0xc82, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc82, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc82, 0b00000
	li x12, 0x00000000
	csrrci x13, 0xc82, 0b00000
	li x12, 0x00000000
	# mcycle
	li a1, 0xb00
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb00, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb00, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb00, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb00, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb00, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb00, 0b00101
	j csr_user_unauth
	# mcycleh
	li a1, 0xb80
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb80, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb80, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb80, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb80, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb80, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb80, 0b00101
	j csr_user_unauth
	# minstret
	li a1, 0xb02
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb02, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb02, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb02, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb02, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb02, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb02, 0b00101
	j csr_user_unauth
	# minstreth
	li a1, 0xb82
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb82, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb82, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb82, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb82, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb82, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb82, 0b00101
	j csr_user_unauth
	# mhpmcounter3
	li a1, 0xb03
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb03, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb03, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb03, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb03, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb03, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb03, 0b00101
	j csr_user_unauth
	# mhpmcounter4
	li a1, 0xb04
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb04, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb04, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb04, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb04, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb04, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb04, 0b00101
	j csr_user_unauth
	# mhpmcounter5
	li a1, 0xb05
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb05, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb05, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb05, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb05, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb05, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb05, 0b00101
	j csr_user_unauth
	# mhpmcounter6
	li a1, 0xb06
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb06, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb06, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb06, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb06, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb06, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb06, 0b00101
	j csr_user_unauth
	# mhpmcounter7
	li a1, 0xb07
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb07, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb07, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb07, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb07, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb07, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb07, 0b00101
	j csr_user_unauth
	# mhpmcounter8
	li a1, 0xb08
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb08, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb08, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb08, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb08, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb08, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb08, 0b00101
	j csr_user_unauth
	# mhpmcounter9
	li a1, 0xb09
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb09, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb09, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb09, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb09, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb09, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb09, 0b00101
	j csr_user_unauth
	# mhpmcounter10
	li a1, 0xb0a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb0a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb0a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb0a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb0a, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb0a, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb0a, 0b00101
	j csr_user_unauth
	# mhpmcounter11
	li a1, 0xb0b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb0b, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb0b, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb0b, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb0b, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb0b, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb0b, 0b00101
	j csr_user_unauth
	# mhpmcounter12
	li a1, 0xb0c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb0c, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb0c, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb0c, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb0c, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb0c, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb0c, 0b00101
	j csr_user_unauth
	# mhpmcounter3h
	li a1, 0xb83
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb83, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb83, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb83, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb83, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb83, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb83, 0b00101
	j csr_user_unauth
	# mhpmcounter4h
	li a1, 0xb84
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb84, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb84, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb84, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb84, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb84, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb84, 0b00101
	j csr_user_unauth
	# mhpmcounter5h
	li a1, 0xb85
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb85, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb85, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb85, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb85, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb85, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb85, 0b00101
	j csr_user_unauth
	# mhpmcounter6h
	li a1, 0xb86
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb86, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb86, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb86, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb86, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb86, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb86, 0b00101
	j csr_user_unauth
	# mhpmcounter7h
	li a1, 0xb87
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb87, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb87, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb87, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb87, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb87, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb87, 0b00101
	j csr_user_unauth
	# mhpmcounter8h
	li a1, 0xb88
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb88, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb88, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb88, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb88, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb88, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb88, 0b00101
	j csr_user_unauth
	# mhpmcounter9h
	li a1, 0xb89
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb89, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb89, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb89, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb89, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb89, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb89, 0b00101
	j csr_user_unauth
	# mhpmcounter10h
	li a1, 0xb8a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb8a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb8a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb8a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb8a, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb8a, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb8a, 0b00101
	j csr_user_unauth
	# mhpmcounter11h
	li a1, 0xb8b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb8b, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb8b, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb8b, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb8b, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb8b, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb8b, 0b00101
	j csr_user_unauth
	# mhpmcounter12h
	li a1, 0xb8c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xb8c, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xb8c, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xb8c, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xb8c, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xb8c, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xb8c, 0b00101
	j csr_user_unauth
	# mstatus
	li a1, 0x300
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x300, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x300, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x300, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x300, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x300, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x300, 0b00101
	j csr_user_unauth
	# misa
	li a1, 0x301
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x301, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x301, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x301, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x301, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x301, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x301, 0b00101
	j csr_user_unauth
	# mie
	li a1, 0x304
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x304, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x304, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x304, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x304, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x304, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x304, 0b00101
	j csr_user_unauth
	# mtvec
	li a1, 0x305
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x305, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x305, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x305, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x305, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x305, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x305, 0b00101
	j csr_user_unauth
	# mcounteren
	li a1, 0x306
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x306, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x306, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x306, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x306, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x306, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x306, 0b00101
	j csr_user_unauth
	# mstatush
	li a1, 0x310
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x310, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x310, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x310, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x310, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x310, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x310, 0b00101
	j csr_user_unauth
	# menvcfg
	li a1, 0x30a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x30a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x30a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x30a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x30a, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x30a, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x30a, 0b00101
	j csr_user_unauth
	# menvcfgh
	li a1, 0x31a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x31a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x31a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x31a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x31a, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x31a, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x31a, 0b00101
	j csr_user_unauth
	# mcountinhibit
	li a1, 0x320
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x320, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x320, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x320, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x320, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x320, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x320, 0b00101
	j csr_user_unauth
	# mhpmevent3
	li a1, 0x323
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x323, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x323, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x323, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x323, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x323, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x323, 0b00101
	j csr_user_unauth
	# mhpmevent4
	li a1, 0x324
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x324, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x324, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x324, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x324, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x324, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x324, 0b00101
	j csr_user_unauth
	# mhpmevent5
	li a1, 0x325
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x325, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x325, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x325, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x325, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x325, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x325, 0b00101
	j csr_user_unauth
	# mhpmevent6
	li a1, 0x326
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x326, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x326, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x326, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x326, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x326, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x326, 0b00101
	j csr_user_unauth
	# mhpmevent7
	li a1, 0x327
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x327, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x327, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x327, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x327, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x327, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x327, 0b00101
	j csr_user_unauth
	# mhpmevent8
	li a1, 0x328
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x328, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x328, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x328, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x328, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x328, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x328, 0b00101
	j csr_user_unauth
	# mhpmevent9
	li a1, 0x329
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x329, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x329, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x329, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x329, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x329, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x329, 0b00101
	j csr_user_unauth
	# mhpmevent10
	li a1, 0x32a
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x32a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x32a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x32a, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x32a, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x32a, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x32a, 0b00101
	j csr_user_unauth
	# mhpmevent11
	li a1, 0x32b
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x32b, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x32b, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x32b, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x32b, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x32b, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x32b, 0b00101
	j csr_user_unauth
	# mhpmevent12
	li a1, 0x32c
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x32c, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x32c, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x32c, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x32c, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x32c, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x32c, 0b00101
	j csr_user_unauth
	# mscratch
	li a1, 0x340
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x340, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x340, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x340, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x340, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x340, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x340, 0b00101
	j csr_user_unauth
	# mepc
	li a1, 0x341
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x341, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x341, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x341, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x341, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x341, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x341, 0b00101
	j csr_user_unauth
	# mcause
	li a1, 0x342
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x342, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x342, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x342, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x342, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x342, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x342, 0b00101
	j csr_user_unauth
	# mtval
	li a1, 0x343
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x343, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x343, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x343, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x343, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x343, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x343, 0b00101
	j csr_user_unauth
	# mip
	li a1, 0x344
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x344, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x344, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x344, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x344, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x344, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x344, 0b00101
	j csr_user_unauth
	# tselect
	li a1, 0x7a0
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x7a0, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x7a0, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x7a0, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x7a0, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x7a0, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x7a0, 0b00101
	j csr_user_unauth
	# tdata1
	li a1, 0x7a1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x7a1, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x7a1, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x7a1, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x7a1, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x7a1, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x7a1, 0b00101
	j csr_user_unauth
	# tdata2
	li a1, 0x7a2
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x7a2, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x7a2, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x7a2, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x7a2, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x7a2, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x7a2, 0b00101
	j csr_user_unauth
	# tdata3
	li a1, 0x7a3
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x7a3, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x7a3, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x7a3, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x7a3, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x7a3, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x7a3, 0b00101
	j csr_user_unauth
	# mcontext
	li a1, 0x7a8
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x7a8, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x7a8, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x7a8, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x7a8, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x7a8, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x7a8, 0b00101
	j csr_user_unauth
	# scontext
	li a1, 0x7aa
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x7aa, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x7aa, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x7aa, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x7aa, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x7aa, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x7aa, 0b00101
	j csr_user_unauth
	# secureseed
	li a1, 0x7c1
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0x7c1, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0x7c1, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0x7c1, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0x7c1, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0x7c1, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0x7c1, 0b00101
	j csr_user_unauth
	# mvendorid
	li a1, 0xf11
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf11, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xf11, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xf11, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf11, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xf11, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xf11, 0b00101
	j csr_user_unauth
	# marchid
	li a1, 0xf12
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf12, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xf12, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xf12, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf12, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xf12, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xf12, 0b00101
	j csr_user_unauth
	# mimpid
	li a1, 0xf13
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf13, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xf13, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xf13, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf13, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xf13, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xf13, 0b00101
	j csr_user_unauth
	# mhartid
	li a1, 0xf14
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf14, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xf14, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xf14, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf14, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xf14, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xf14, 0b00101
	j csr_user_unauth
	# mconfigptr
	li a1, 0xf15
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrw x13, 0xf15, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrs x13, 0xf15, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrc x13, 0xf15, x12
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrwi x13, 0xf15, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrsi x13, 0xf15, 0b00101
	j csr_user_unauth
	lw t0, 0(t1)
	addi t0, t0, 1
	sw t0, 0(t1)
	csrrci x13, 0xf15, 0b00101
	j csr_user_unauth
	ret
