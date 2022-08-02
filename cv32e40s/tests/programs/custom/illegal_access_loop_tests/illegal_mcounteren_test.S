/*
**
** Copyright 2022 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
** https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
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

mco_loop:
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
	j mco_custom


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




mco_custom: // puts the core in usermode.
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