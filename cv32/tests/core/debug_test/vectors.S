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
** 
*******************************************************************************
*/

.section .vectors, "ax"
.option norvc
.global glb_illegal_insn_status
.global glb_ebreak_status
.global glb_expect_illegal_insn
.global glb_expect_ebreak_handler
.set test_ret_val, 0x20000000
.set test_fail, 0x1
        
vector_table:
	j sw_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j verification_irq_handler

/* this is fixed to 0x8000, used for PULP_SECURE=0. We redirect this entry to the
new vector table (which is at mtvec) */
/* .section .legacy_irq, "ax" */
/*	j vector_table */
/*	j __no_irq_handler */
/*	j __no_irq_handler */
/*	j __no_irq_handler */

.section .text.vecs
/* exception handling */
__no_irq_handler:
	la a0, no_exception_handler_msg
	jal ra, puts
	j __no_irq_handler


sw_irq_handler:
        addi sp,sp,-44
        sw t0, 0(sp)
        sw t1, 4(sp)
        sw a0, 8(sp)
        sw a1, 12(sp)
        sw a2, 16(sp)
        sw a3, 20(sp)
        sw a4, 24(sp)
        sw a5, 28(sp)
        sw a6, 32(sp)
        sw a7, 36(sp)
        sw ra, 40(sp)
	csrr t0, mcause
	slli t0, t0, 1  /* shift off the high bit */
	srli t0, t0, 1
	li t1, 2
	beq t0, t1, handle_illegal_insn
	li t1, 11
	beq t0, t1, handle_ecall
	li t1, 3
	beq t0, t1, handle_ebreak
	j handle_unknown

handle_ecall:
	la a0, ecall_msg
	jal ra, puts
	j end_handler

handle_ebreak:
	la a0, ebreak_msg
	jal ra, puts
        // Check if expecting ebreak handler
        la a0, glb_expect_ebreak_handler 
        lw t0, 0(a0)
        bne t0, x0, cont_handle_ebreak
        // Not expecting ebreak, assert test failed
        li a0, test_ret_val
        li t0, 1
        sw t0, 0(a0)
	j end_handler
cont_handle_ebreak:
        //increment hart status     
        sw x0, 0(a0)
        la a0, glb_ebreak_status  
        lw t0, 0(a0)
        addi t0,t0,1
        sw t0, 0(a0)
	j end_handler

handle_illegal_insn:
	la a0, illegal_insn_msg
	jal ra, puts
        // Check if expecting illegal instruction
        la a0, glb_expect_illegal_insn 
        lw t0, 0(a0)
        bne t0, x0, cont_illegal_insn 
        li a0, test_ret_val
        li t0, 1
        sw t0, 0(a0)            //Test Failed
	j end_handler
cont_illegal_insn:
        //increment hart status     
        sw x0, 0(a0)
        la a0, glb_illegal_insn_status  
        lw t0, 0(a0)
        addi t0,t0,1
        sw t0, 0(a0)
	j end_handler


        
handle_unknown:
	la a0, unknown_msg
	jal ra, puts
	j end_handler

end_handler:
	csrr a0, mepc
	lb t0, 0(a0)
	li t1,0x3
	and t0,t0,t1
	addi a0, a0, 2
	bne t0,t1,end_handler_cont
	addi a0, a0, 2
end_handler_cont:
	csrw mepc, a0
        lw t0, 0(sp)
        lw t1, 4(sp)
        lw a0, 8(sp)
        lw a1, 12(sp)
        lw a2, 16(sp)
        lw a3, 20(sp)
        lw a4, 24(sp)
        lw a5, 28(sp)
        lw a6, 32(sp)
        lw a7, 36(sp)
        lw ra, 40(sp)
        addi sp,sp,44
	mret
/* this interrupt can be generated for verification purposes, random or when the PC is equal to a given value*/
verification_irq_handler:
	mret

.section .rodata
illegal_insn_msg:
	.string "illegal instruction exception handler entered\n"
ecall_msg:
	.string "ecall exception handler entered\n"
ebreak_msg:
	.string "ebreak exception handler entered\n"
unknown_msg:
	.string "unknown exception handler entered\n"
no_exception_handler_msg:
	.string "no exception handler installed\n"
