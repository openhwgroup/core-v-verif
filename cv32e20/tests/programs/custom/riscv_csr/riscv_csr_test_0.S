.macro init
.endm
.section .text.init
.globl _start
.option norvc
_start:
	# mcycle
	# 	CSR marked volatile, skipping it.
	# mcycleh
	li x1, 0xa5a5a5a5
	csrrw x8, 0xb80, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0xb80, x1
	li x1, 0xa5a5a5a5
	bne x1, x8, csr_fail
	li x1, 0x256e07d5
	csrrw x8, 0xb80, x1
	li x1, 0x5a5a5a5a
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0xb80, x1
	li x1, 0x256e07d5
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0xb80, x1
	li x1, 0xa5efa7f5
	bne x1, x8, csr_fail
	li x1, 0x5da6b6f7
	csrrs x8, 0xb80, x1
	li x1, 0xffffffff
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0xb80, x1
	li x1, 0xffffffff
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0xb80, x1
	li x1, 0x5a5a5a5a
	bne x1, x8, csr_fail
	li x1, 0x04ef025c
	csrrc x8, 0xb80, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0xb80, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0xb80, 0b11010
	li x1, 0x00000005
	bne x1, x8, csr_fail
	csrrwi x8, 0xb80, 0b11100
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrsi x8, 0xb80, 0b00101
	li x1, 0x0000001c
	bne x1, x8, csr_fail
	csrrsi x8, 0xb80, 0b11010
	li x1, 0x0000001d
	bne x1, x8, csr_fail
	csrrsi x8, 0xb80, 0b00001
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrci x8, 0xb80, 0b00101
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrci x8, 0xb80, 0b11010
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrci x8, 0xb80, 0b11101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	# minstret
	# 	CSR marked volatile, skipping it.
	# minstreth
	li x1, 0xa5a5a5a5
	csrrw x8, 0xb82, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0xb82, x1
	li x1, 0xa5a5a5a5
	bne x1, x8, csr_fail
	li x1, 0x8958c647
	csrrw x8, 0xb82, x1
	li x1, 0x5a5a5a5a
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0xb82, x1
	li x1, 0x8958c647
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0xb82, x1
	li x1, 0xadfde7e7
	bne x1, x8, csr_fail
	li x1, 0x54dcfbc4
	csrrs x8, 0xb82, x1
	li x1, 0xffffffff
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0xb82, x1
	li x1, 0xffffffff
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0xb82, x1
	li x1, 0x5a5a5a5a
	bne x1, x8, csr_fail
	li x1, 0xc7bd3da7
	csrrc x8, 0xb82, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0xb82, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0xb82, 0b11010
	li x1, 0x00000005
	bne x1, x8, csr_fail
	csrrwi x8, 0xb82, 0b01100
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrsi x8, 0xb82, 0b00101
	li x1, 0x0000000c
	bne x1, x8, csr_fail
	csrrsi x8, 0xb82, 0b11010
	li x1, 0x0000000d
	bne x1, x8, csr_fail
	csrrsi x8, 0xb82, 0b01011
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrci x8, 0xb82, 0b00101
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrci x8, 0xb82, 0b11010
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrci x8, 0xb82, 0b01011
	li x1, 0x00000000
	bne x1, x8, csr_fail
	# mhpmcounter3
	li x1, 0xa5a5a5a5
	csrrw x8, 0xb03, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0xb03, x1
	li x1, 0xa5a5a5a5
	bne x1, x8, csr_fail
	li x1, 0x3c731a14
	csrrw x8, 0xb03, x1
	li x1, 0x5a5a5a5a
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0xb03, x1
	li x1, 0x3c731a14
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0xb03, x1
	li x1, 0xbdf7bfb5
	bne x1, x8, csr_fail
	li x1, 0x99ceb44c
	csrrs x8, 0xb03, x1
	li x1, 0xffffffff
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0xb03, x1
	li x1, 0xffffffff
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0xb03, x1
	li x1, 0x5a5a5a5a
	bne x1, x8, csr_fail
	li x1, 0xc9a40f55
	csrrc x8, 0xb03, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0xb03, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0xb03, 0b11010
	li x1, 0x00000005
	bne x1, x8, csr_fail
	csrrwi x8, 0xb03, 0b11010
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrsi x8, 0xb03, 0b00101
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrsi x8, 0xb03, 0b11010
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrsi x8, 0xb03, 0b01001
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrci x8, 0xb03, 0b00101
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrci x8, 0xb03, 0b11010
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrci x8, 0xb03, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	# mhpmcounter4
	# 	CSR marked SKIP_ME: Seeing a value in this counter at first read.
	# mhpmcounter5
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter6
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter7
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter8
	# 	CSR marked SKIP_ME: Seeing a value in this counter at first read.
	# mhpmcounter9
	# 	CSR marked SKIP_ME: Seeing a value in this counter at first read.
	# mhpmcounter10
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter11
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter12
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter3h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter4h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter5h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter6h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter7h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter8h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter9h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter10h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter11h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mhpmcounter12h
	# 	CSR marked SKIP_ME: Performance counters not currently implemented
	# mstatus
	# 	CSR marked SKIP_ME: Need to update fields.
	# misa
	li x1, 0xa5a5a5a5
	csrrw x8, 0x301, x1
	li x1, 0x40101104
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0x301, x1
	li x1, 0x40101104
	bne x1, x8, csr_fail
	li x1, 0xf758c4fb
	csrrw x8, 0x301, x1
	li x1, 0x40101104
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0x301, x1
	li x1, 0x40101104
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0x301, x1
	li x1, 0x40101104
	bne x1, x8, csr_fail
	li x1, 0x488ecbe9
	csrrs x8, 0x301, x1
	li x1, 0x40101104
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0x301, x1
	li x1, 0x40101104
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0x301, x1
	li x1, 0x40101104
	bne x1, x8, csr_fail
	li x1, 0xd9e842ec
	csrrc x8, 0x301, x1
	li x1, 0x40101104
	bne x1, x8, csr_fail
	csrrwi x8, 0x301, 0b00101
	li x1, 0x40101104
	bne x1, x8, csr_fail
	csrrwi x8, 0x301, 0b11010
	li x1, 0x40101104
	bne x1, x8, csr_fail
	csrrwi x8, 0x301, 0b00000
	li x1, 0x40101104
	bne x1, x8, csr_fail
	csrrsi x8, 0x301, 0b00101
	li x1, 0x40101104
	bne x1, x8, csr_fail
	csrrsi x8, 0x301, 0b11010
	li x1, 0x40101104
	bne x1, x8, csr_fail
	csrrsi x8, 0x301, 0b10110
	li x1, 0x40101104
	bne x1, x8, csr_fail
	csrrci x8, 0x301, 0b00101
	li x1, 0x40101104
	bne x1, x8, csr_fail
	csrrci x8, 0x301, 0b11010
	li x1, 0x40101104
	bne x1, x8, csr_fail
	csrrci x8, 0x301, 0b11011
	li x1, 0x40101104
	bne x1, x8, csr_fail
	# mie
	# 	CSR marked SKIP_ME: Imperas checker has bit 31 writeable
	# mtvec
	li x1, 0xa5a5a5a5
	csrrw x8, 0x305, x1
	li x1, 0x00000001
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0x305, x1
	li x1, 0xa5a5a501
	bne x1, x8, csr_fail
	li x1, 0x2d6b054d
	csrrw x8, 0x305, x1
	li x1, 0x5a5a5a01
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0x305, x1
	li x1, 0x2d6b0501
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0x305, x1
	li x1, 0xadefa501
	bne x1, x8, csr_fail
	li x1, 0x16e3c638
	csrrs x8, 0x305, x1
	li x1, 0xffffff01
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0x305, x1
	li x1, 0xffffff01
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0x305, x1
	li x1, 0x5a5a5a01
	bne x1, x8, csr_fail
	li x1, 0x3e78d8b4
	csrrc x8, 0x305, x1
	li x1, 0x00000001
	bne x1, x8, csr_fail
	csrrwi x8, 0x305, 0b00101
	li x1, 0x00000001
	bne x1, x8, csr_fail
	csrrwi x8, 0x305, 0b11010
	li x1, 0x00000001
	bne x1, x8, csr_fail
	csrrwi x8, 0x305, 0b10111
	li x1, 0x00000001
	bne x1, x8, csr_fail
	csrrsi x8, 0x305, 0b00101
	li x1, 0x00000001
	bne x1, x8, csr_fail
	csrrsi x8, 0x305, 0b11010
	li x1, 0x00000001
	bne x1, x8, csr_fail
	csrrsi x8, 0x305, 0b11110
	li x1, 0x00000001
	bne x1, x8, csr_fail
	csrrci x8, 0x305, 0b00101
	li x1, 0x00000001
	bne x1, x8, csr_fail
	csrrci x8, 0x305, 0b11010
	li x1, 0x00000001
	bne x1, x8, csr_fail
	csrrci x8, 0x305, 0b00100
	li x1, 0x00000001
	bne x1, x8, csr_fail
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
	li x1, 0xa5a5a5a5
	csrrw x8, 0x340, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0x340, x1
	li x1, 0xa5a5a5a5
	bne x1, x8, csr_fail
	li x1, 0xc6a43397
	csrrw x8, 0x340, x1
	li x1, 0x5a5a5a5a
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0x340, x1
	li x1, 0xc6a43397
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0x340, x1
	li x1, 0xe7a5b7b7
	bne x1, x8, csr_fail
	li x1, 0x6e28ffc9
	csrrs x8, 0x340, x1
	li x1, 0xffffffff
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0x340, x1
	li x1, 0xffffffff
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0x340, x1
	li x1, 0x5a5a5a5a
	bne x1, x8, csr_fail
	li x1, 0x1e770bd4
	csrrc x8, 0x340, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x340, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x340, 0b11010
	li x1, 0x00000005
	bne x1, x8, csr_fail
	csrrwi x8, 0x340, 0b10101
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrsi x8, 0x340, 0b00101
	li x1, 0x00000015
	bne x1, x8, csr_fail
	csrrsi x8, 0x340, 0b11010
	li x1, 0x00000015
	bne x1, x8, csr_fail
	csrrsi x8, 0x340, 0b10000
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrci x8, 0x340, 0b00101
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrci x8, 0x340, 0b11010
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrci x8, 0x340, 0b11111
	li x1, 0x00000000
	bne x1, x8, csr_fail
	# mepc
	li x1, 0xa5a5a5a5
	csrrw x8, 0x341, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0x341, x1
	li x1, 0xa5a5a5a4
	bne x1, x8, csr_fail
	li x1, 0xc76a3903
	csrrw x8, 0x341, x1
	li x1, 0x5a5a5a5a
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0x341, x1
	li x1, 0xc76a3902
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0x341, x1
	li x1, 0xe7efbda6
	bne x1, x8, csr_fail
	li x1, 0x4d7099b1
	csrrs x8, 0x341, x1
	li x1, 0xfffffffe
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0x341, x1
	li x1, 0xfffffffe
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0x341, x1
	li x1, 0x5a5a5a5a
	bne x1, x8, csr_fail
	li x1, 0x729d12a0
	csrrc x8, 0x341, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x341, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x341, 0b11010
	li x1, 0x00000004
	bne x1, x8, csr_fail
	csrrwi x8, 0x341, 0b11001
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrsi x8, 0x341, 0b00101
	li x1, 0x00000018
	bne x1, x8, csr_fail
	csrrsi x8, 0x341, 0b11010
	li x1, 0x0000001c
	bne x1, x8, csr_fail
	csrrsi x8, 0x341, 0b10011
	li x1, 0x0000001e
	bne x1, x8, csr_fail
	csrrci x8, 0x341, 0b00101
	li x1, 0x0000001e
	bne x1, x8, csr_fail
	csrrci x8, 0x341, 0b11010
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrci x8, 0x341, 0b10100
	li x1, 0x00000000
	bne x1, x8, csr_fail
	# mcause
	li x1, 0xa5a5a5a5
	csrrw x8, 0x342, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0x342, x1
	li x1, 0x80000005
	bne x1, x8, csr_fail
	li x1, 0xa53f1880
	csrrw x8, 0x342, x1
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0x342, x1
	li x1, 0x80000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0x342, x1
	li x1, 0x80000005
	bne x1, x8, csr_fail
	li x1, 0x801cf28c
	csrrs x8, 0x342, x1
	li x1, 0x8000001f
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0x342, x1
	li x1, 0x8000001f
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0x342, x1
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	li x1, 0xae0fd78c
	csrrc x8, 0x342, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x342, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x342, 0b11010
	li x1, 0x00000005
	bne x1, x8, csr_fail
	csrrwi x8, 0x342, 0b01001
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrsi x8, 0x342, 0b00101
	li x1, 0x00000009
	bne x1, x8, csr_fail
	csrrsi x8, 0x342, 0b11010
	li x1, 0x0000000d
	bne x1, x8, csr_fail
	csrrsi x8, 0x342, 0b00010
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrci x8, 0x342, 0b00101
	li x1, 0x0000001f
	bne x1, x8, csr_fail
	csrrci x8, 0x342, 0b11010
	li x1, 0x0000001a
	bne x1, x8, csr_fail
	csrrci x8, 0x342, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	# mtval
	# 	CSR marked SKIP_ME: Imperas does not have this CSR writeable
	# mip
	li x1, 0xa5a5a5a5
	csrrw x8, 0x344, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0x344, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x1e423d77
	csrrw x8, 0x344, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0x344, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0x344, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x149600b6
	csrrs x8, 0x344, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0x344, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0x344, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x90ecc372
	csrrc x8, 0x344, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x344, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x344, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x344, 0b11110
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x344, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x344, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x344, 0b01100
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x344, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x344, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x344, 0b01101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	# tselect
	li x1, 0xa5a5a5a5
	csrrw x8, 0x7a0, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0x7a0, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x75a3899a
	csrrw x8, 0x7a0, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0x7a0, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0x7a0, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x7575a3aa
	csrrs x8, 0x7a0, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0x7a0, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0x7a0, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xf240c44c
	csrrc x8, 0x7a0, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7a0, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7a0, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7a0, 0b00010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7a0, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7a0, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7a0, 0b00111
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7a0, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7a0, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7a0, 0b11101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	# tdata1
	# 	CSR marked SKIP_ME: DUT hardcodes U-mode to 1, Imperas has it as  0
	# tdata2
	li x1, 0xa5a5a5a5
	csrrw x8, 0x7a2, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0x7a2, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x6e8de241
	csrrw x8, 0x7a2, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0x7a2, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0x7a2, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x2601ce20
	csrrs x8, 0x7a2, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0x7a2, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0x7a2, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x6b32195b
	csrrc x8, 0x7a2, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7a2, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7a2, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7a2, 0b11000
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7a2, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7a2, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7a2, 0b10111
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7a2, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7a2, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7a2, 0b00111
	li x1, 0x00000000
	bne x1, x8, csr_fail
	# tdata3
	li x1, 0xa5a5a5a5
	csrrw x8, 0x7a3, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0x7a3, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa4bbf412
	csrrw x8, 0x7a3, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0x7a3, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0x7a3, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x3bffb6c2
	csrrs x8, 0x7a3, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0x7a3, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0x7a3, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x454ce887
	csrrc x8, 0x7a3, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7a3, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7a3, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7a3, 0b00001
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7a3, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7a3, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7a3, 0b00000
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7a3, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7a3, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7a3, 0b00110
	li x1, 0x00000000
	bne x1, x8, csr_fail
	# mcontext
	li x1, 0xa5a5a5a5
	csrrw x8, 0x7a8, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0x7a8, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xda6ebd2a
	csrrw x8, 0x7a8, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0x7a8, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0x7a8, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5f0283c5
	csrrs x8, 0x7a8, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0x7a8, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0x7a8, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x2bb994dc
	csrrc x8, 0x7a8, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7a8, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7a8, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7a8, 0b11000
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7a8, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7a8, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7a8, 0b10000
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7a8, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7a8, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7a8, 0b01100
	li x1, 0x00000000
	bne x1, x8, csr_fail
	# scontext
	li x1, 0xa5a5a5a5
	csrrw x8, 0x7aa, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrw x8, 0x7aa, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xf45f599c
	csrrw x8, 0x7aa, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrs x8, 0x7aa, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrs x8, 0x7aa, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xf9f307a2
	csrrs x8, 0x7aa, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0xa5a5a5a5
	csrrc x8, 0x7aa, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x5a5a5a5a
	csrrc x8, 0x7aa, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	li x1, 0x7eb0434a
	csrrc x8, 0x7aa, x1
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7aa, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7aa, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrwi x8, 0x7aa, 0b00010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7aa, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7aa, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrsi x8, 0x7aa, 0b00100
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7aa, 0b00101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7aa, 0b11010
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrrci x8, 0x7aa, 0b11101
	li x1, 0x00000000
	bne x1, x8, csr_fail
	csrr x8, 1962
	li x1, 0x00000000
	bne x1, x8, csr_fail
csr_pass:
	li x1, 123456789
	li x2, 0x20000000
	sw x1, 0(x2)
	j csr_pass
csr_fail:
	li x1, 1
	li x2, 0x20000000
	sw x1, 0(x2)
	sw x1, 4(x2)
	sw x8, 8(x2)
	j csr_fail
