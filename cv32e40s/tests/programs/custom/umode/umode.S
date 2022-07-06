.section .text


// Functions
.global myfunc
.global run_in_umode
.global setup_pmp
.global handler_set_mmode

// Flags
.global gbl_request_mmode


utext_start:

// int myfunc(void)
myfunc:
	// Set return value to 42
	addi	a0, x0, 42

	// Return to caller
	jalr	x0, 0(ra)

utext_end:


// void run_in_umode(int (*funptr)(void))
run_in_umode:
	// Save "ra" to stack
	addi	sp, sp, -4
	sw	ra, 0(sp) // store ra into memory location sp+0

	// Zero "mstatus" to set MPP=umode (note: shouldve bitcleared)
	addi	t0, x0, 0
	csrrw   x0, mstatus, t0
	// Set "mepc" to the func ptr in arg 0
	csrrw	x0, mepc, a0
	// Set link register
	la	ra, run_in_umode_cont
	// call "funptr" with mret
	mret
run_in_umode_cont:

	// Request trap handler to return to mmode
	la	t0, gbl_request_mmode
	li	t1, 1
	sw	t1, 0(t0)
	ecall

	// Restore "ra" from stack
	lw	ra, 0(sp)
	addi	sp, sp, 4

	// Return to caller
	jalr	x0, 0(ra)


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

