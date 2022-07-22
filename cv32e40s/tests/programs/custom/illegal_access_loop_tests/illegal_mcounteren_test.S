.global mco_custom
.global mco_instr
.global mco_loop
.global u_sw_irq_handler

mco_loop:
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
	j mco_custom



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



mco_custom: // puts the core in usermode.

	// Zero "mstatus" to set MPP=umode
	li	t0, 0x1800
	csrrc   x0, mstatus, t0 // clear the mstatus (mpp -> User mode).
	la t0, mco_instr //this will pouint to the label below.
	csrrw   x0, mepc, t0

	mret // call the mret to execute mode change.


mco_instr: // csr privilege loop test

// Start of generated code
csrrs  t0, 0xc00, x0 
csrrs  t0, 0xc01, x0 
csrrs  t0, 0xc02, x0 
csrrs  t0, 0xc03, x0 
csrrs  t0, 0xc04, x0 
csrrs  t0, 0xc05, x0 
csrrs  t0, 0xc06, x0 
csrrs  t0, 0xc07, x0 
csrrs  t0, 0xc08, x0 
csrrs  t0, 0xc09, x0 
csrrs  t0, 0xc0a, x0 
csrrs  t0, 0xc0b, x0 
csrrs  t0, 0xc0c, x0 
csrrs  t0, 0xc0d, x0 
csrrs  t0, 0xc0e, x0 
csrrs  t0, 0xc0f, x0 
csrrs  t0, 0xc10, x0 
csrrs  t0, 0xc11, x0 
csrrs  t0, 0xc12, x0 
csrrs  t0, 0xc13, x0 
csrrs  t0, 0xc14, x0 
csrrs  t0, 0xc15, x0 
csrrs  t0, 0xc16, x0 
csrrs  t0, 0xc17, x0 
csrrs  t0, 0xc18, x0 
csrrs  t0, 0xc19, x0 
csrrs  t0, 0xc1a, x0 
csrrs  t0, 0xc1b, x0 
csrrs  t0, 0xc1c, x0 
csrrs  t0, 0xc1d, x0 
csrrs  t0, 0xc1e, x0 
csrrs  t0, 0xc1f, x0 
j end_handler_ret

//end of generated code