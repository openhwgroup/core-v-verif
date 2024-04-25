
/*
**
** Copyright 2020 OpenHW Group
** 
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
** 
**     https://solderpad.org/licenses/
** 
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
** 
*******************************************************************************
** Debugger code
*******************************************************************************
*/

.section .debugger, "ax"
.global _debugger_start
.global glb_debug_status
.global glb_hart_status
.global glb_expect_debug_entry
.global glb_step_info
.global glb_previous_dpc
.global glb_step_count
.global glb_irq_timeout
.global glb_mcycle_start
.global glb_mcycle_end
.global glb_minstret_start
.global glb_minstret_end
.global __debugger_stack_start
.global _debugger_fail
.global _debugger_end
.set test_ret_val, 0x20000000
.set test_fail, 0x1
        
_debugger_start:        
        // Debugger Stack
        csrw dscratch, a0       // dscratch0
        la a0, __debugger_stack_start
        //sw t0, 0(a0)
        csrw 0x7b3, t0      	// dscratch1
        sw t1, 4(a0)
        sw t2, 8(a0)
        sw a1, 12(a0)
        sw a2, 16(a0)
        sw t3, 20(a0)
        // Check if expecting debug entry
        la a1, glb_expect_debug_entry
        lw t1, 0(a1)
        beq x0,t1,_debugger_fail

        // Read lower 32 bits of mcycle and minstret
        // and store in globals for check at exit
        csrr t1, mcycle
        csrr t2, minstret
        la a1, glb_mcycle_start
        sw t1, 0(a1)
        la a1, glb_minstret_start
        sw t2, 0(a1)
 
        // Determine Test to execute in debugger code based on glb_hart_status
        la a2, glb_hart_status
        lw t2, 0(a2)

	// ebreak test will loop in debugger code over several iterations
	//  and will increment the global status each time
	li t0,5
	beq t2,t0,_debugger_ebreak // Test 5

	// For all other tests,
	// Set debug status = hart status
  la a1, glb_debug_status
	sw t2, 0(a1)

    li t0,10
	beq t2,t0,_debugger_ebreak_entry    // Test 10

	li t0,12
	beq t2,t0,_debugger_ecall_exception    // Test 12

  li t0,14
  beq t2,t0, _debugger_ebreak_entry // Test 14

  li t0, 19
  beq t2, t0, _debugger_irq

  li t0, 20
  beq t2, t0, _debugger_req_and_irq

  li t0, 25
  beq t2, t0, _debugger_hwloop

_debugger_req_and_irq:
    // Debug was requested at the same cycle as irq
    // Check dpc to see that pc is not at irq handler
    // IRQ used was 30, so addr would be 30*4=120, 0x78
    csrr t0, dpc
    li t1, 0x78
    beq t0, t1, _debugger_fail
    j _debugger_end

_debugger_irq:
    // Assert irq
    li a1, 0x15000000
    li t0, 0x40000000
    sw t0, 0(a1)
    li a1, 0x15000004
    li t0, 2
    sw t0, 0(a1)

    li t1, 1000
// Wait for 1000 cycles, then timeout
_irq_wait_loop:
    la a1, glb_expect_irq_entry
    lw t0, 0(a1);
    beq t1, x0, _irq_loop_end
    addi t1, t1, -1
    bne t0, x0, _irq_wait_loop
_irq_loop_end:
    la a1, glb_irq_timeout
    sw t1, 0(a1) 
    j _debugger_end

_debugger_ecall_exception:
	ecall // exception

_debugger_ebreak_entry:
    la a1, glb_debug_status
	li   t1, 4<<28 | 1<<6 | 3<<0 | 1<<15
	csrr t2,dcsr
	bne  t1,t2,_debugger_fail
        csrr a1,dpc
        addi a1,a1,4 # uncompressed ebreak used to enter debug here
        csrw dpc,a1
        //sw t1, 0(a1)
        j  _debugger_end

_debugger_ebreak:
    li t0, 4<<28 | 3<<6 | 3<<0
    csrr t1, dcsr
    bne t0, t1, _debugger_fail 
        // Increment glb_debug_status
        la a1, glb_debug_status
        lw t1, 0(a1)
        addi t1,t1,1
        sw t1, 0(a1)
	// Repeat executing debug code until debug status = hart_status + 3
	addi t0, t2, 3
	beq  t1, t0, _debugger_end
    // Execute non-compressed ebreak for iteration 2
    addi t0, t2, 2
    beq t1, t0, _uncompressed_ebreak
	// Debugger Un-Stack and call debugger code from start using ebreak
    csrr t0, 0x7b3
	lw   t1, 4(a0)
        lw   t2, 8(a0)
        lw   a1, 12(a0)
        lw   a2, 16(a0)
        csrr a0, dscratch
        ebreak
_uncompressed_ebreak:
	// Debugger Un-Stack and call debugger code from start using ebreak
    csrr t0, 0x7b3
	lw   t1, 4(a0)
        lw   t2, 8(a0)
        lw   a1, 12(a0)
        lw   a2, 16(a0)
        csrr a0, dscratch
        .4byte 0x00100073 # ebreak

_debugger_hwloop:
    lw t3, 0(a0)
    cv.bneimm t3, 0, replace_ebreak
    li t3, 1        // To avoid to endlessly re-execute HWloop due to ebreak inside HWloop
    sw t3, 0(a0)

    li a1, 0x15000000
    li t3, 0x40000000
    sw t3, 0(a1)
    li a1, 0x15000004
    li t3, 3
    sw t3, 0(a1)

    li t1, 0

    .balign 4

    cv.starti 0, startZ_7_1
    cv.endi 0, endZ_7_1
    cv.counti 0, 10

    .option norvc

startZ_7_1:
    addi t1, t1, 1
    addi t1, t1, 1
    addi t1, t1, 1
to_replace:
    ebreak
    addi t1, t1, 1
endZ_7_1:

    .option rvc

    li t2, 50
    bne t1, t2, _debugger_fail
    j  _debugger_end

replace_ebreak:
    li t2, 0x00130313   // put back addi t1, t1, 1 in place of ebreak
    la a1, to_replace
    sw t2, 0(a1)

    li t1, 3

    j to_replace

_debugger_end:
    // Check counter values. They should have increased while in debug
    // regardless of stopcount bit in csr
    csrr t1, mcycle
    la a1, glb_mcycle_start
    lw t2, 0(a1)
    sub t1, t1, t2
    beq t1, x0, _debugger_fail

    csrr t1, minstret
    la a1, glb_minstret_start
    lw t2, 0(a1)
    sub t1, t1, t2
    beq t1, x0, _debugger_fail

    // If single stepping, do not clear
    la a1, glb_hart_status
    lw t0, 0(a1)
    li t1, 18
    beq t0, t1, _debugger_end_continue

    // Clear debug entry expectation flag
    la a1, glb_expect_debug_entry
    sw x0, 0(a1)
_debugger_end_continue:
        // Debugger Un-Stack
        //lw t0, 0(a0)
        la a0, __debugger_stack_start
        csrr t0, 0x7b3
        lw   t1, 4(a0)
        lw   t2, 8(a0)
        lw   a1, 12(a0)
        lw   a2, 16(a0)
        lw   t3, 20(a0)
        csrr a0, dscratch
        dret
_debugger_fail: //Test Failed
        li a0, test_ret_val
        li t0, test_fail
        sw t0, 0(a0)
	nop
        nop
        nop
        nop
        
