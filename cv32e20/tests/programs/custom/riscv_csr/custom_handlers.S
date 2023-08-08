/*
**
** Copyright 2023 Cadence
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
** This file contains a modified version of the u_sw_irq_handler
** found in bsp/handler.S.  The u_sw_irq_handler in that file is designated as
** a weak symbol while this one is not, so the one in this file should override
** it.
**
** This version of u_sw_irq_handler calls different functions to handle
** the illegal instruction exception (used for CSR access checking) and
** the ebreak excetpion (used to transition to Machine mode from User mode.)
**
** This file also contains functions used by the C program to change privilege
** levels during the CSR test.
**
*******************************************************************************
*/
/* Exception codes */
#define EXCEPTION_ILLEGAL_INSN 2
#define EXCEPTION_BREAKPOINT 3
#define EXCEPTION_ECALL_M 11


.section .text.handlers
.global __no_irq_handler
.global u_sw_irq_handler
.global csr_mismatch
.global csr_user_unauth
.global csr_bad_impl
.global csr_unexpected_int
.global switch_to_user_mode
.global switch_to_machine_mode


u_sw_irq_handler:
        /* While we are still using puts in handlers, save all caller saved
           regs.  Eventually, some of these saves could be deferred.  */
        addi sp,sp,-64
        sw ra, 0(sp)
        sw a0, 4(sp)
        sw a1, 8(sp)
        sw a2, 12(sp)
        sw a3, 16(sp)
        sw a4, 20(sp)
        sw a5, 24(sp)
        sw a6, 28(sp)
        sw a7, 32(sp)
        sw t0, 36(sp)
        sw t1, 40(sp)
        sw t2, 44(sp)
        sw t3, 48(sp)
        sw t4, 52(sp)
        sw t5, 56(sp)
        sw t6, 60(sp)
        csrr t0, mcause
        li t1, EXCEPTION_ILLEGAL_INSN
        beq t0, t1, handle_illegal_csr
        li t1, EXCEPTION_ECALL_M
        beq t0, t1, handle_ecall
        li t1, EXCEPTION_BREAKPOINT
        beq t0, t1, handle_ebreak
        j handle_unknown

handle_illegal_csr:
	/*Load glb_expect_illegal_insn flag value.*/
 	la t1, glb_expect_illegal_insn
 	lw t0, 0(t1)
	/*Decrement glb_expect_illegal_insn value*/
 	addi t0, t0, -1
	/*Store decremented value*/
 	sw t0, 0(t1)
	/*If decremented value is negative, flag as illegal*/
 	blt t0, x0, csr_unexpected_illegal_inst
	/*else, increment mepc by 8 to skip next instruction (we know there's no 2 byte instructions)*/
 	csrrsi t0, mepc, 0
 	addi t0, t0, 0x8
 	csrrw t0, mepc, t0
end_handler_ret:
 	lw ra, 0(sp)
 	lw a0, 4(sp)
 	lw a1, 8(sp)
 	lw a2, 12(sp)
 	lw a3, 16(sp)
 	lw a4, 20(sp)
 	lw a5, 24(sp)
 	lw a6, 28(sp)
 	lw a7, 32(sp)
 	lw t0, 36(sp)
 	lw t1, 40(sp)
 	lw t2, 44(sp)
 	lw t3, 48(sp)
 	lw t4, 52(sp)
 	lw t5, 56(sp)
 	lw t6, 60(sp)
 	addi sp,sp,64
 	mret

handle_unknown:
        la a0, unknown_msg
        jal ra, puts
        /* We don't know what interrupt/exception is being handled, so don't
           increment mepc.  */
        j end_handler_ret

end_handler_incr_mepc:
        csrr t0, mepc
        lb t1, 0(t0)
        li a0, 0x3
        and t1, t1, a0
        /* Increment mepc by 2 or 4 depending on whether the instruction at mepc
           is compressed or not.  */
        bne t1, a0, end_handler_incr_mepc2
        addi t0, t0, 2
end_handler_incr_mepc2:
        addi t0, t0, 2
        csrw mepc, t0
	j end_handler_ret


/* This is unchanged from bsp/handlers.S
 * The handle_syscall function is in bsp/syscalls.c
 */
handle_ecall:
        jal ra, handle_syscall
        j end_handler_incr_mepc

/* This handler returns control to main code stream with the
 * processor still in machine mode. This allows the test to
 * confirm that user mode accesses didn't effect the machine
 * mode CSR's.
 */
handle_ebreak:

	/*Load mstatus*/
        csrr t0, mstatus
	/*OR in  Previous Privilege level to "MACHINE" ie 2'b11*/
	li t1, 0x1800
	or t0, t0, t1
	/*Write modified mstatus*/
        csrrw t0, mstatus, t1
        j end_handler_incr_mepc

/* This function is intended to be called in Machine Mode to
 * transfer to User mode.  It should cause unexpected illegal
 * instrution exceptions if called in any other mode.
 */
switch_to_user_mode:
	/*Set Previous Privilige level to "USER" ie 2'b00*/
        csrwi mstatus, 0
	/*Write the return address into the mepc*/
        csrrw x0, mepc, ra
	/*Return with 'mret' rather than ret instruction*/
        mret

switch_to_machine_mode:
	/*Force execution of the ebreak handler*/
	ebreak
        ret

/* Error reporting code.
 * Each of tehse labels does a printf of a different message,
 * then jumps to a failure loop.
 */
csr_mismatch:
	la a0, csr_mismatch_msg
	jal ra, printf
	j csr_fail_loop

csr_user_unauth:
	la a0, csr_user_unauth_msg
	jal ra, printf
	j csr_fail_loop

csr_bad_impl:
	addi sp, sp,-8
	sw ra, 0(sp)
	sw t1, 4(sp)
	la a0, csr_bad_impl_msg
	jal ra, printf
	la a0, glb_fail_count
	lw a1, 0(a0)
	addi a1, a1, 1
	sw a1, 0(a0)
	lw ra, 0(sp)
	lw t1, 4(sp)
	addi sp, sp, 8
	ret

csr_unexpected_int:
	la a0, csr_unexpected_int_msg
	jal ra, printf
	j csr_fail_loop

csr_unexpected_illegal_inst:
	la a0, csr_unexpected_illegal_inst_msg
	jal ra, printf
	j csr_fail_loop

csr_fail_loop:
        jal test_fail
	j csr_fail_loop

/* Error messages.  Pointers to these should go into a0(x10) before calling printf
 * Assumptions are that data is loaded into registers as follows:
 *   a1(x11): CSR Address
 *   a2(x12): Expected Data
 *   a3(x13): Actual Data
 */
.section .rodata
unknown_msg:
        .string "CV32E20 BSP: unknown exception handler entered\n"
csr_mismatch_msg:
	.string "ERROR: Mismatch on CSR 0x%03x Expected 0x%08x Actual 0x%08x\n"
csr_user_unauth_msg:
	.string "ERROR: Access to CSR 0x%03x did NOT cause an exception, but was expected to.\n"
csr_bad_impl_msg:
	.string "ERROR: Access to unimplemented CSR address 0x%03x did NOT cause an exception, but was expected to.\n"
csr_unexpected_int_msg:
	.string "ERROR: Unexpected exception while accessing CSR 0x%03x\n"
csr_unexpected_illegal_inst_msg:
	.string "ERROR: Unexpected illegal instruction while accessing CSR 0x%03x\n"

