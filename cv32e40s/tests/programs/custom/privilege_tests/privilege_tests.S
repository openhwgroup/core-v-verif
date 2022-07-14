.section .text


// imported variable
.global reg_input

// Functions
.global change_exec_mode
.global setup_pmp
.global set_u_mode


change_exec_mode:
	// setup the return adress to stack.
	addi	sp, sp, -4
	// store the ra to the stack pointer.
	sw	ra, 0(sp)

	// Zero "mstatus" to set MPP=umode
	li	t0, 0x1800
	csrrc   x0, mstatus, t0 // clear the mstatus (mpp -> User mode).
	csrrs   x0, mstatus, a0 // set the incoming bits to the mpp.

	// set mepc to point to ecall
	la t0, set_ecall //this will pouint to the label below.
	csrrw   x0, mepc, t0

	mret // call the mret to execute mode change.

set_ecall:
	ecall // cause an exception

	// return to main
	lw	ra, 0(sp)
	addi	sp, sp, 4
	jalr	x0, 0(ra)


// Probably don't need this. Quick pmp hack to allow user supreme pmp access.
// void setup_pmp(void)

setup_pmp:
	// Set pmp addr to 0xFFFF_FFFF
	li	t0, 0xFFFFFFFF
	csrrw	x0, pmpaddr0, t0

	// Set pmp region TOR and read/write/execute
	li	t0, ((1 << 3) + (7 << 0))
	csrrw	x0, pmpcfg0, t0

	// Return to caller
	jalr	x0, 0(ra)

set_u_mode: // puts the core in usermode.
	// setup the return adress to stack.
	addi	sp, sp, -4
	// store the ra to the stack pointer.
	sw	ra, 0(sp)

	// Zero "mstatus" to set MPP=umode
	li	t0, 0x1800
	csrrc   x0, mstatus, t0 // clear the mstatus (mpp -> User mode).
	la t0, empty_symb 
	csrrw   x0, mepc, t0
	lw	ra, 0(sp)
	addi	sp, sp, 4
	mret // call the mret to execute mode change.

empty_symb:
	ret
