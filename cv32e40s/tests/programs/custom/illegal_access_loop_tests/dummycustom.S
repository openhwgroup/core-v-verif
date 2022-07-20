.global illegal_custom
.global ill_instr
.global illegal_full
.global u_sw_irq_handler

illegal_full:
	addi sp,sp,-48
	sw ra, 0(sp)
	sw s0, 4(sp)
	sw s1, 8(sp)
	sw s2, 12(sp)
	sw s3, 16(sp)
	sw s4, 20(sp)
	sw s5, 24(sp)
	sw s6, 28(sp)
	sw s7, 32(sp)
	sw s8, 36(sp)
	sw s9, 40(sp)
	sw s10, 44(sp)
	sw s11, 48(sp)
	li s2, 0
	j illegal_custom



u_sw_irq_handler:

	addi s2, s2, 1

	csrrw 	t0, mepc, x0
	addi t0, t0, 4
	csrrw   x0, mepc, t0 // increment to the next 
	mret


end_handler_ret:
	addi a0, s2, 0 // load the increment to return value
	// return stack and load to c
	lw ra, 0(sp)
	lw s0, 4(sp)
	lw s1, 8(sp)
	lw s2, 12(sp)
	lw s3, 16(sp)
	lw s4, 20(sp)
	lw s5, 24(sp)
	lw s6, 28(sp)
	lw s7, 32(sp)
	lw s8, 36(sp)
	lw s9, 40(sp)
	lw s10, 44(sp)
	lw s11, 48(sp)
	addi sp,sp,48
	jalr x0, 0(ra)



illegal_custom: // puts the core in usermode.

	// Zero "mstatus" to set MPP=umode
	li	t0, 0x1800
	csrrc   x0, mstatus, t0 // clear the mstatus (mpp -> User mode).
	la t0, ill_instr //this will pouint to the label below.
	csrrw   x0, mepc, t0

	mret // call the mret to execute mode change.


ill_instr: // csr privilege loop test

.word(0xcc000073)
.word(0xcc0000f3)
.word(0xcc000173)
.word(0xcc0001f3)
.word(0xcc000273)
.word(0xcc0002f3)
.word(0xcc000373)
j end_handler_ret
