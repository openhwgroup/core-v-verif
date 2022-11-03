
.section .text


// imported variable
.global reg_input

// Functions
.global setup_pmp
.global set_u_mode


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
	// Zero "mstatus" to set MPP=umode
	li	t0, 0x1800
	csrrc   x0, mstatus, t0 // clear the mstatus (mpp -> User mode).
	csrrw 	x0, mepc, ra
	mret