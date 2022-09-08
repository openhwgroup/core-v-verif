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
** This will run the generated mhpcounteren instructions when called from the 'illegal_access_loop_tests.c'
**
*******************************************************************************
*/

.global mco_custom
.global mco_instr
.global mco_loop
.global u_sw_irq_handler
.global Check_mcounteren
// Immediate for the trap handler to check to make sure its not looping in infinitely
#include "mcounteren_priv_gen_test.h"


mco_loop: // function called from the .c test code. 
	addi sp,sp,-52
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
	li s3, ILLEGALLY_GENERATED_INSN // load reference value to sanity-check max exceptions
	j mco_custom

exception_max_traps: // if trap count exceeds 'ILLEGALLY_GENERATED_INSN' break and return 0 instead
	li s2, 0
	j end_handler_ret


Check_mcounteren: // read and return the mcounteren value 
	add a0, x0, x0
	csrr a0, mcounteren
	ret	

end_handler_ret:
	addi a0, s2, 0 // load the trap handler return value
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
	addi sp,sp,52
	ret

u_sw_irq_handler:

	addi s2, s2, 1 // increments every trap
	bgt s2, s3, exception_max_traps // check if trap counter has exceeded number of illegal instructions
	// csrrw 	t0, mepc, x0
	addi s4, s4, 4 // increment s4 which holds the pc value (saves a cssrw per loop)
	csrrw   x0, mepc, s4 // increment to the next execution 
	mret


mco_custom: // puts the core in usermode.
	li	t0, 0x1800
	csrrc   x0, mstatus, t0 // clear the mstatus (mpp -> User mode).
	la t0, mco_instr // load mco_instr to the mepc
	la s4, mco_instr // load mco to the s4 register for optimization in the trap handler
	csrrw   x0, mepc, t0
	mret // call the mret to execute mode change.


mco_instr: // start of mcounteren loop test

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

// end of generated code