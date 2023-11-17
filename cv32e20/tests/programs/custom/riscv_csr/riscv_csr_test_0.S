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
	li x12, 0x25637a51
	csrrw x13, 0x305, x12
	li x12, 0x5a5a5a01
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x305, x12
	li x12, 0x25637a01
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x305, x12
	li x12, 0xa5e7ff01
	bne x12, x13, csr_mismatch
	li x12, 0xf3ef7afa
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
	li x12, 0x4a99c790
	csrrc x13, 0x305, x12
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x305, 0b00101
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x305, 0b11010
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x305, 0b00000
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x305, 0b00101
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x305, 0b11010
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x305, 0b00101
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrci x13, 0x305, 0b00101
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrci x13, 0x305, 0b11010
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
	csrrci x13, 0x305, 0b00000
	li x12, 0x00000001
	bne x12, x13, csr_mismatch
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
	li x12, 0x2b38c1bc
	csrrw x13, 0x341, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x341, x12
	li x12, 0x2b38c1bc
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x341, x12
	li x12, 0xafbde5bc
	bne x12, x13, csr_mismatch
	li x12, 0xd31e5b8c
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
	li x12, 0x43b2d88b
	csrrc x13, 0x341, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x341, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x341, 0b11010
	li x12, 0x00000004
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x341, 0b00000
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x341, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x341, 0b11010
	li x12, 0x00000004
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x341, 0b00111
	li x12, 0x0000001e
	bne x12, x13, csr_mismatch
	csrrci x13, 0x341, 0b00101
	li x12, 0x0000001e
	bne x12, x13, csr_mismatch
	csrrci x13, 0x341, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0x341, 0b01000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	# mstatus
	# 	CSR marked SKIP_ME: Imperas model does not have U bit set to 1
	# mcause
	li a1, 0x342
	li x12, 0xa5a5a5a5
	csrrw x13, 0x342, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x342, x12
	li x12, 0x80000005
	bne x12, x13, csr_mismatch
	li x12, 0x9ab05af2
	csrrw x13, 0x342, x12
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x342, x12
	li x12, 0x80000012
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x342, x12
	li x12, 0x80000017
	bne x12, x13, csr_mismatch
	li x12, 0x810a96ee
	csrrs x13, 0x342, x12
	li x12, 0x8000001f
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrc x13, 0x342, x12
	li x12, 0x8000001f
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrc x13, 0x342, x12
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	li x12, 0x0d0aec20
	csrrc x13, 0x342, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x342, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x342, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x342, 0b11001
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x342, 0b00101
	li x12, 0x00000019
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x342, 0b11010
	li x12, 0x0000001d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x342, 0b10010
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0x342, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0x342, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0x342, 0b10111
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	ret
.globl machine_mode_check
machine_mode_check:	la t1, glb_expect_illegal_insn
	# cycle
	# 	CSR marked SKIP_ME: Confriming all User mode accesses are bugged.
	# instret
	# 	CSR marked SKIP_ME: Confriming all User mode accesses are bugged.
	# cycleh
	# 	CSR marked SKIP_ME: Confriming all User mode accesses are bugged.
	# instreth
	# 	CSR marked SKIP_ME: Confriming all User mode accesses are bugged.
	# mcycle
	li a1, 0xb00
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb00, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb00, x12
	li x12, 0xa5a5a5a5
	li x12, 0xe94b1461
	csrrw x13, 0xb00, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb00, x12
	li x12, 0xe94b1461
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb00, x12
	li x12, 0xedefb5e5
	li x12, 0x051ad334
	csrrs x13, 0xb00, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb00, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb00, x12
	li x12, 0x5a5a5a5a
	li x12, 0x618e1a4e
	csrrc x13, 0xb00, x12
	li x12, 0x00000000
	csrrwi x13, 0xb00, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb00, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb00, 0b10011
	li x12, 0x0000001a
	csrrsi x13, 0xb00, 0b00101
	li x12, 0x00000013
	csrrsi x13, 0xb00, 0b11010
	li x12, 0x00000017
	csrrsi x13, 0xb00, 0b00010
	li x12, 0x0000001f
	csrrci x13, 0xb00, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb00, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb00, 0b01110
	li x12, 0x00000000
	# mcycleh
	li a1, 0xb80
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb80, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb80, x12
	li x12, 0xa5a5a5a5
	li x12, 0xf75849cd
	csrrw x13, 0xb80, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb80, x12
	li x12, 0xf75849cd
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb80, x12
	li x12, 0xf7fdeded
	li x12, 0xd890d6df
	csrrs x13, 0xb80, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb80, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb80, x12
	li x12, 0x5a5a5a5a
	li x12, 0x27a89cf3
	csrrc x13, 0xb80, x12
	li x12, 0x00000000
	csrrwi x13, 0xb80, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb80, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb80, 0b00101
	li x12, 0x0000001a
	csrrsi x13, 0xb80, 0b00101
	li x12, 0x00000005
	csrrsi x13, 0xb80, 0b11010
	li x12, 0x00000005
	csrrsi x13, 0xb80, 0b11100
	li x12, 0x0000001f
	csrrci x13, 0xb80, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb80, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb80, 0b10001
	li x12, 0x00000000
	# minstret
	li a1, 0xb02
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb02, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb02, x12
	li x12, 0xa5a5a5a5
	li x12, 0xb6d6a2ce
	csrrw x13, 0xb02, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb02, x12
	li x12, 0xb6d6a2ce
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb02, x12
	li x12, 0xb7f7a7ef
	li x12, 0xa03e1393
	csrrs x13, 0xb02, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb02, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb02, x12
	li x12, 0x5a5a5a5a
	li x12, 0x0fc9ef5c
	csrrc x13, 0xb02, x12
	li x12, 0x00000000
	csrrwi x13, 0xb02, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb02, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb02, 0b00000
	li x12, 0x0000001a
	csrrsi x13, 0xb02, 0b00101
	li x12, 0x00000000
	csrrsi x13, 0xb02, 0b11010
	li x12, 0x00000005
	csrrsi x13, 0xb02, 0b11010
	li x12, 0x0000001f
	csrrci x13, 0xb02, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb02, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb02, 0b00001
	li x12, 0x00000000
	# minstreth
	li a1, 0xb82
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb82, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb82, x12
	li x12, 0xa5a5a5a5
	li x12, 0xf573a1e4
	csrrw x13, 0xb82, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb82, x12
	li x12, 0xf573a1e4
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb82, x12
	li x12, 0xf5f7a5e5
	li x12, 0xf1a72aa6
	csrrs x13, 0xb82, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb82, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb82, x12
	li x12, 0x5a5a5a5a
	li x12, 0x48890bf9
	csrrc x13, 0xb82, x12
	li x12, 0x00000000
	csrrwi x13, 0xb82, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb82, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb82, 0b11101
	li x12, 0x0000001a
	csrrsi x13, 0xb82, 0b00101
	li x12, 0x0000001d
	csrrsi x13, 0xb82, 0b11010
	li x12, 0x0000001d
	csrrsi x13, 0xb82, 0b00010
	li x12, 0x0000001f
	csrrci x13, 0xb82, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb82, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb82, 0b10000
	li x12, 0x00000000
	# mhpmcounter3
	li a1, 0xb03
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb03, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb03, x12
	li x12, 0xa5a5a5a5
	li x12, 0x73cc0b79
	csrrw x13, 0xb03, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb03, x12
	li x12, 0x73cc0b79
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb03, x12
	li x12, 0xf7edaffd
	li x12, 0xa21ceaa6
	csrrs x13, 0xb03, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb03, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb03, x12
	li x12, 0x5a5a5a5a
	li x12, 0xb97b16c9
	csrrc x13, 0xb03, x12
	li x12, 0x00000000
	csrrwi x13, 0xb03, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb03, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb03, 0b01110
	li x12, 0x0000001a
	csrrsi x13, 0xb03, 0b00101
	li x12, 0x0000000e
	csrrsi x13, 0xb03, 0b11010
	li x12, 0x0000000f
	csrrsi x13, 0xb03, 0b01101
	li x12, 0x0000001f
	csrrci x13, 0xb03, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb03, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb03, 0b00001
	li x12, 0x00000000
	# mhpmcounter4
	# 	CSR marked SKIP_ME: Seeing a value in this counter at first read.
	# mhpmcounter5
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter6
	li a1, 0xb06
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb06, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb06, x12
	li x12, 0xa5a5a5a5
	li x12, 0xbc66d0c3
	csrrw x13, 0xb06, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb06, x12
	li x12, 0xbc66d0c3
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb06, x12
	li x12, 0xbde7f5e7
	li x12, 0x2dc8a587
	csrrs x13, 0xb06, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb06, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb06, x12
	li x12, 0x5a5a5a5a
	li x12, 0x1e0a7fbd
	csrrc x13, 0xb06, x12
	li x12, 0x00000000
	csrrwi x13, 0xb06, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb06, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb06, 0b00011
	li x12, 0x0000001a
	csrrsi x13, 0xb06, 0b00101
	li x12, 0x00000003
	csrrsi x13, 0xb06, 0b11010
	li x12, 0x00000007
	csrrsi x13, 0xb06, 0b11010
	li x12, 0x0000001f
	csrrci x13, 0xb06, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb06, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb06, 0b01100
	li x12, 0x00000000
	# mhpmcounter7
	li a1, 0xb07
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb07, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb07, x12
	li x12, 0xa5a5a5a5
	li x12, 0x89bf7ab6
	csrrw x13, 0xb07, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb07, x12
	li x12, 0x89bf7ab6
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb07, x12
	li x12, 0xadbfffb7
	li x12, 0x801408eb
	csrrs x13, 0xb07, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb07, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb07, x12
	li x12, 0x5a5a5a5a
	li x12, 0x0f75beb0
	csrrc x13, 0xb07, x12
	li x12, 0x00000000
	csrrwi x13, 0xb07, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb07, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb07, 0b01011
	li x12, 0x0000001a
	csrrsi x13, 0xb07, 0b00101
	li x12, 0x0000000b
	csrrsi x13, 0xb07, 0b11010
	li x12, 0x0000000f
	csrrsi x13, 0xb07, 0b00010
	li x12, 0x0000001f
	csrrci x13, 0xb07, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb07, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb07, 0b10101
	li x12, 0x00000000
	# mhpmcounter8
	# 	CSR marked SKIP_ME: Seeing a value in this counter at first read.
	# mhpmcounter9
	# 	CSR marked SKIP_ME: Seeing a value in this counter at first read.
	# mhpmcounter10
	li a1, 0xb0a
	li x12, 0xa5a5a5a5
	csrrw x13, 0xb0a, x12
	li x12, 0x00000000
	li x12, 0x5a5a5a5a
	csrrw x13, 0xb0a, x12
	li x12, 0xa5a5a5a5
	li x12, 0x09c026ac
	csrrw x13, 0xb0a, x12
	li x12, 0x5a5a5a5a
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb0a, x12
	li x12, 0x09c026ac
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb0a, x12
	li x12, 0xade5a7ad
	li x12, 0x71b321db
	csrrs x13, 0xb0a, x12
	li x12, 0xffffffff
	li x12, 0xa5a5a5a5
	csrrc x13, 0xb0a, x12
	li x12, 0xffffffff
	li x12, 0x5a5a5a5a
	csrrc x13, 0xb0a, x12
	li x12, 0x5a5a5a5a
	li x12, 0x4c12303a
	csrrc x13, 0xb0a, x12
	li x12, 0x00000000
	csrrwi x13, 0xb0a, 0b00101
	li x12, 0x00000000
	csrrwi x13, 0xb0a, 0b11010
	li x12, 0x00000005
	csrrwi x13, 0xb0a, 0b10110
	li x12, 0x0000001a
	csrrsi x13, 0xb0a, 0b00101
	li x12, 0x00000016
	csrrsi x13, 0xb0a, 0b11010
	li x12, 0x00000017
	csrrsi x13, 0xb0a, 0b11011
	li x12, 0x0000001f
	csrrci x13, 0xb0a, 0b00101
	li x12, 0x0000001f
	csrrci x13, 0xb0a, 0b11010
	li x12, 0x0000001a
	csrrci x13, 0xb0a, 0b11101
	li x12, 0x00000000
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
	li x12, 0x72a96862
	csrrw x13, 0xb0b, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb0b, x12
	li x12, 0x72a96862
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb0b, x12
	li x12, 0xf7adede7
	bne x12, x13, csr_mismatch
	li x12, 0xbcc1ae22
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
	li x12, 0x20e55da9
	csrrc x13, 0xb0b, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb0b, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb0b, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb0b, 0b11101
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb0b, 0b00101
	li x12, 0x0000001d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb0b, 0b11010
	li x12, 0x0000001d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb0b, 0b10101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb0b, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb0b, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb0b, 0b11001
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
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
	li x12, 0xb496922e
	csrrw x13, 0xb0c, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb0c, x12
	li x12, 0xb496922e
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb0c, x12
	li x12, 0xb5b7b7af
	bne x12, x13, csr_mismatch
	li x12, 0xc828ca2d
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
	li x12, 0x84b7ad3b
	csrrc x13, 0xb0c, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb0c, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb0c, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb0c, 0b11101
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb0c, 0b00101
	li x12, 0x0000001d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb0c, 0b11010
	li x12, 0x0000001d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb0c, 0b01111
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb0c, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb0c, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb0c, 0b01100
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
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
	li x12, 0x0be9b6e9
	csrrw x13, 0xb83, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb83, x12
	li x12, 0x000000e9
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb83, x12
	li x12, 0x000000ed
	bne x12, x13, csr_mismatch
	li x12, 0x203c63e9
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
	li x12, 0xff4f377e
	csrrc x13, 0xb83, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb83, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb83, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb83, 0b01101
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb83, 0b00101
	li x12, 0x0000000d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb83, 0b11010
	li x12, 0x0000000d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb83, 0b00000
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
	li x12, 0x04eecec6
	csrrw x13, 0xb84, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb84, x12
	li x12, 0x000000c6
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb84, x12
	li x12, 0x000000e7
	bne x12, x13, csr_mismatch
	li x12, 0x9dc1a39c
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
	li x12, 0xb734b0f4
	csrrc x13, 0xb84, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb84, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb84, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb84, 0b00100
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb84, 0b00101
	li x12, 0x00000004
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb84, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb84, 0b10101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb84, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb84, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb84, 0b01001
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
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
	li x12, 0x9ddac7c3
	csrrw x13, 0xb85, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb85, x12
	li x12, 0x000000c3
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb85, x12
	li x12, 0x000000e7
	bne x12, x13, csr_mismatch
	li x12, 0x08bae00f
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
	li x12, 0xbf008f8d
	csrrc x13, 0xb85, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb85, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb85, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb85, 0b01011
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb85, 0b00101
	li x12, 0x0000000b
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb85, 0b11010
	li x12, 0x0000000f
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb85, 0b01001
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb85, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb85, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb85, 0b10101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	# mhpmcounter6h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
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
	li x12, 0x582f09d9
	csrrw x13, 0xb87, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb87, x12
	li x12, 0x000000d9
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb87, x12
	li x12, 0x000000fd
	bne x12, x13, csr_mismatch
	li x12, 0x305b010e
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
	li x12, 0x3330952b
	csrrc x13, 0xb87, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb87, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb87, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb87, 0b10101
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb87, 0b00101
	li x12, 0x00000015
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb87, 0b11010
	li x12, 0x00000015
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb87, 0b00111
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb87, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb87, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb87, 0b11100
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	# mhpmcounter8h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter9h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
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
	li x12, 0x1ee0fe42
	csrrw x13, 0xb8a, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb8a, x12
	li x12, 0x00000042
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb8a, x12
	li x12, 0x000000e7
	bne x12, x13, csr_mismatch
	li x12, 0x094e25c1
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
	li x12, 0xe0732fc3
	csrrc x13, 0xb8a, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8a, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8a, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8a, 0b00000
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8a, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8a, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8a, 0b01011
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8a, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8a, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8a, 0b11111
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
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
	li x12, 0x09e8cd51
	csrrw x13, 0xb8b, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb8b, x12
	li x12, 0x00000051
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb8b, x12
	li x12, 0x000000f5
	bne x12, x13, csr_mismatch
	li x12, 0x4c6be11c
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
	li x12, 0xc9fae0fe
	csrrc x13, 0xb8b, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8b, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8b, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8b, 0b01110
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8b, 0b00101
	li x12, 0x0000000e
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8b, 0b11010
	li x12, 0x0000000f
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8b, 0b00010
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8b, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8b, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8b, 0b00100
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
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
	li x12, 0x8b55ac40
	csrrw x13, 0xb8c, x12
	li x12, 0x0000005a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0xb8c, x12
	li x12, 0x00000040
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0xb8c, x12
	li x12, 0x000000e5
	bne x12, x13, csr_mismatch
	li x12, 0x95a73a60
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
	li x12, 0xb54aaaf2
	csrrc x13, 0xb8c, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8c, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8c, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0xb8c, 0b10110
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8c, 0b00101
	li x12, 0x00000016
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8c, 0b11010
	li x12, 0x00000017
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xb8c, 0b11001
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8c, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8c, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0xb8c, 0b10010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
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
	li x12, 0xc89641df
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
	li x12, 0xfb9f3ab5
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
	li x12, 0x3a4745ff
	csrrc x13, 0x301, x12
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x301, 0b00101
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x301, 0b11010
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x301, 0b11110
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x301, 0b00101
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x301, 0b11010
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x301, 0b10000
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrci x13, 0x301, 0b00101
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrci x13, 0x301, 0b11010
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	csrrci x13, 0x301, 0b10101
	li x12, 0x40101104
	bne x12, x13, csr_mismatch
	# mie
	# 	CSR marked SKIP_ME: Imperas checker has bit 31 writeable
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
	li a1, 0x340
	li x12, 0xa5a5a5a5
	csrrw x13, 0x340, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrw x13, 0x340, x12
	li x12, 0xa5a5a5a5
	bne x12, x13, csr_mismatch
	li x12, 0x31b5583f
	csrrw x13, 0x340, x12
	li x12, 0x5a5a5a5a
	bne x12, x13, csr_mismatch
	li x12, 0xa5a5a5a5
	csrrs x13, 0x340, x12
	li x12, 0x31b5583f
	bne x12, x13, csr_mismatch
	li x12, 0x5a5a5a5a
	csrrs x13, 0x340, x12
	li x12, 0xb5b5fdbf
	bne x12, x13, csr_mismatch
	li x12, 0x527fdc57
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
	li x12, 0xe94717ee
	csrrc x13, 0x340, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x340, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x340, 0b11010
	li x12, 0x00000005
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x340, 0b11101
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x340, 0b00101
	li x12, 0x0000001d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x340, 0b11010
	li x12, 0x0000001d
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x340, 0b00001
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0x340, 0b00101
	li x12, 0x0000001f
	bne x12, x13, csr_mismatch
	csrrci x13, 0x340, 0b11010
	li x12, 0x0000001a
	bne x12, x13, csr_mismatch
	csrrci x13, 0x340, 0b11000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	# mtval
	# 	CSR marked SKIP_ME: Imperas does not have this CSR writeable
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
	li x12, 0x7401c630
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
	li x12, 0x29353dc2
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
	li x12, 0xb733367c
	csrrc x13, 0x344, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x344, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x344, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x344, 0b11001
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x344, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x344, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x344, 0b00001
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x344, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x344, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x344, 0b01001
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
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
	li x12, 0x38aacc01
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
	li x12, 0xd30dcd4d
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
	li x12, 0xb4de8098
	csrrc x13, 0x7a0, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a0, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a0, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a0, 0b01001
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a0, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a0, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a0, 0b11110
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a0, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a0, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a0, 0b01000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	# tdata1
	# 	CSR marked SKIP_ME: DUT hardcodes U-mode to 1, Imperas has it as  0
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
	li x12, 0xe08ed554
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
	li x12, 0x124a3db9
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
	li x12, 0xa1bb4967
	csrrc x13, 0x7a2, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a2, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a2, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a2, 0b01010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a2, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a2, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a2, 0b10111
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a2, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a2, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a2, 0b01001
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
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
	li x12, 0xfeb1c265
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
	li x12, 0xbe1289f5
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
	li x12, 0xda8a192f
	csrrc x13, 0x7a3, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a3, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a3, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a3, 0b10111
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
	csrrci x13, 0x7a3, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
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
	li x12, 0x03e2f931
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
	li x12, 0x234a14cc
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
	li x12, 0x7b63b591
	csrrc x13, 0x7a8, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a8, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a8, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7a8, 0b01010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a8, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a8, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7a8, 0b11011
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a8, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a8, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7a8, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
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
	li x12, 0xd5f4d0ba
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
	li x12, 0x6e2f9787
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
	li x12, 0x35635ca6
	csrrc x13, 0x7aa, x12
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7aa, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7aa, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrwi x13, 0x7aa, 0b10000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7aa, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7aa, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0x7aa, 0b11101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7aa, 0b00101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7aa, 0b11010
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0x7aa, 0b01101
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
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
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf11,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf11,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf11,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf11,0x0
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf11,0x0
	li x12, 0x00000000
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
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf11, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf11, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf11, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf11, 0b00000
	li x12, 0x00000000
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf11, 0b00000
	li x12, 0x00000000
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
	li x12, 0x00000016
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf12,0x0
	li x12, 0x00000016
	bne x12, x13, csr_mismatch
	csrrs x13, 0xf12,0x0
	li x12, 0x00000016
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf12,0x0
	li x12, 0x00000016
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf12,0x0
	li x12, 0x00000016
	bne x12, x13, csr_mismatch
	csrrc x13, 0xf12,0x0
	li x12, 0x00000016
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
	li x12, 0x00000016
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf12, 0b00000
	li x12, 0x00000016
	bne x12, x13, csr_mismatch
	csrrsi x13, 0xf12, 0b00000
	li x12, 0x00000016
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf12, 0b00000
	li x12, 0x00000016
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf12, 0b00000
	li x12, 0x00000016
	bne x12, x13, csr_mismatch
	csrrci x13, 0xf12, 0b00000
	li x12, 0x00000016
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
	ret
.globl user_mode_check
user_mode_check:	la t1, glb_expect_illegal_insn
	# cycle
	# 	CSR marked SKIP_ME: Confriming all User mode accesses are bugged.
	# instret
	# 	CSR marked SKIP_ME: Confriming all User mode accesses are bugged.
	# cycleh
	# 	CSR marked SKIP_ME: Confriming all User mode accesses are bugged.
	# instreth
	# 	CSR marked SKIP_ME: Confriming all User mode accesses are bugged.
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
	# 	CSR marked SKIP_ME: Seeing a value in this counter at first read.
	# mhpmcounter5
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
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
	# 	CSR marked SKIP_ME: Seeing a value in this counter at first read.
	# mhpmcounter9
	# 	CSR marked SKIP_ME: Seeing a value in this counter at first read.
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
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
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
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter9h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
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
	# 	CSR marked SKIP_ME: Imperas model does not have U bit set to 1
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
	# 	CSR marked SKIP_ME: Imperas checker has bit 31 writeable
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
	# 	CSR marked SKIP_ME: Imperas does not have this CSR writeable
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
	# 	CSR marked SKIP_ME: DUT hardcodes U-mode to 1, Imperas has it as  0
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
	ret
