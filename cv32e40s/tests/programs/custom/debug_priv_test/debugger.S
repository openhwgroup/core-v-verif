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
** Assembly debug code which executes different test-cases based on global variables acting as flags.
**
*******************************************************************************
*/

#include "corev_uvmt.h"

.section .debugger, "ax" 
// Global debugger_start symbol
.global _debugger_start 
// Written by main code to set test case in assembly debug code
.global glb_debug_status 
// Written by main code to set test case in assembly debug code
.global glb_expect_ebreaku_exc
// Written by main code to set test case in assembly debug code
.global glb_setmprv_test
// Written by main code to set test case in assembly debug code
.global glb_check_prv_test
// Written by main code to set test case in assembly debug code
.global glb_check_prv_test_2
// Written by main code to set test case in assembly debug code
.global glb_unsupported_mode_test
// Written by main code to set test case in assembly debug code
.global glb_ebreaku_one_test
// Written by main code to set test case in assembly debug code
.global	glb_check_previous_prv_test
// Written by assembly debug code. Asserts test case failure
.global glb_unsupported_check_failed
// Written by assembly debug code. Asserts test case failure
.global glb_ebreaku_one_check
// Written by assembly debug code. Contains dcsr register value
.global glb_check_prv_test_val
// Written by assembly debug code. Contains dcsr register value
.global glb_dcsr_register

// dcsr.ebreaku bit
#define EBREAKU_BIT		0x1000 

/* 
Starts executing when 'DEBUG_REQ_CONTROL_REG = debug_req_control.bits' is set in 'debug_priv_test.c'. 
Checks and executes a number of different flags associated with different test-cases and debug_mode behavior.
*/
_debugger_start:
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

	la t0, glb_setmprv_test
	lw t0, 0(t0)
	bnez t0, MPRV_test

	la t0, glb_check_prv_test
	lw t0, 0(t0)
	bnez t0, Check_prv_test

	la t0, glb_check_prv_test_2
	lw t0, 0(t0)
	bnez t0, Check_prv_test_2

	la t0, glb_unsupported_mode_test
	lw t0, 0(t0)
	bnez t0, Check_unsupported_modes

	la t0, glb_ebreaku_one_test
	lw t0, 0(t0)
	bnez t0, Set_ebreaku_bit

	la t0, glb_expect_ebreaku_exc
	lw t0, 0(t0)
	bnez t0, Successfull_user_mode

	la t0, glb_check_previous_prv_test
	lw t0, 0(t0)
	bnez t0, Check_previous_privilege_test

	j end_debugger


end_debugger:
	// sets the glb_debug_status value high to signal 'debug_priv_test.c' that the debugger is finished executing.
	la t2, glb_debug_status
	lb t1, 0(t2)
	addi t1, t1, 1
	sb t1, 0(t2)
	
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
    dret



/*
Transition out of D-mode (dret) into U-mode, while mstatus.mprv=1, ensure that when execution continues outside D-mode that mstatus.mprv=0.
*/
MPRV_test:
	li t0, 0x3
	csrrc x0, dcsr, t0 // load U-mode into dcsr.prv register. 
	li t0, 1
	slli t0, t0, 17
	csrrs x0, mstatus, t0 // set MPRV=1
	j end_debugger


/* 
Transition out of D-mode, ensure that executions starts in the same privilege mode as was indicated in dcsr.prv (dcsr.prv=M and dcsr.prv=U).
*/
Check_prv_test:
	la t0, glb_check_prv_test_val
	csrrs t1, dcsr, x0 
	sw t1, 0(t0)
	j end_debugger


/* 
Transition out of D-mode, ensure that executions starts in the same privilege mode as was indicated in dcsr.prv (dcsr.prv=M and dcsr.prv=U).
*/
Check_prv_test_2:
	li t0, 0x3
	csrrc x0, dcsr, t0 // load U-mode into dcsr.prv register. 

	la t0, glb_check_prv_test_val
	csrrs t1, dcsr, x0 
	sw t1, 0(t0)
	j end_debugger



/*
Write unsupported modes to dcsr.prv, ensure the value read back is unchanged from the previous value.
*/
Check_unsupported_modes: // TODO: sim this test again.
	li t0, 0x3
	csrrs x0, dcsr, t0 // preload supported M-mode to get a reference

	// Check S-mode
	li t1, 0x1
	csrrs t2, dcsr, x0	
	and t2, t2, t1  
	csrrw x0, dcsr, t1

	csrrs t2, dcsr, x0	
	and t2, t2, t0
	bne t2, t0, Unsupported_check_failed

	// Check R-mode 
	li t1, 0x2
	csrrs t2, dcsr, x0	
	and t2, t2, t1  
	csrrw x0, dcsr, t1

	csrrs t2, dcsr, x0	
	and t2, t2, t0
	bne t2, t0, Unsupported_check_failed

	j end_debugger


/*
Write unsupported modes to dcsr.prv, ensure the value read back is unchanged from the previous value.
*/
Unsupported_check_failed: // if unsupported mode is written to dcsr.prv go here 
	la t0, glb_unsupported_check_failed
	li t1, 1
	sw t1, 0(t0)
	j end_debugger



/*
Have dcsr.ebreaku=1, be in U-mode, execute ebreak, ensure debug entry happens instead of "normal" ebreak behavior.
*/
Set_ebreaku_bit:
	li t0, EBREAKU_BIT
	csrrs x0, dcsr, t0
	j end_debugger



/*
Have dcsr.ebreaku=1, be in U-mode, execute ebreak, ensure debug entry happens instead of "normal" ebreak behavior.
*/
Successfull_user_mode:
	la t0, glb_ebreaku_one_check
	li t1, 1
	sw t1, 0(t0)	
	j end_debugger



/*
Transition into D-mode from M-mode and U-mode, ensure dcsr.prv contains the privilege mode that was running before D-mode.
*/
Check_previous_privilege_test:
	la t0, glb_dcsr_register
	csrrs t1, dcsr, x0
	sw t1, 0(t0)
	j end_debugger
