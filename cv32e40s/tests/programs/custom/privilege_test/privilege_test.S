/*
** Copyright 2022 OpenHW Group
**
** SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
** Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
** with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
**                                        https://solderpad.org/licenses/SHL-2.1/
** Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
** an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
** specific language governing permissions and limitations under the License.
*******************************************************************************
**
** Assembly functions to help the tests in the privilege_tests.c source file.
**
*******************************************************************************
*/


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