/* Copyright (c) 2023  Silicon Laboratories Inc.
 * This copyrighted material is made available to anyone wishing to use,
 * modify, copy, or redistribute it subject to the terms and conditions
 * of the FreeBSD License.   This program is distributed in the hope that
 * it will be useful, but WITHOUT ANY WARRANTY expressed or implied,
 * including the implied warranties of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE.  A copy of this license is available at
 * http://www.opensource.org/licenses.
 */

/* This is a copy of crt0 from the BSP folder but without  setting the vector address*/

/* Make sure the vector table gets linked into the binary.  */
.global vector_table

/* Make sure the NMI handler gets linked into the binary. */
.global nmi_handler

/* Entry point for bare metal programs */
.section .text.start
.global _start
.type _start, @function

_start:
/* initialize global pointer */
.option push
.option norelax
1:auipc gp, %pcrel_hi(__global_pointer$)
  addi  gp, gp, %pcrel_lo(1b)

/* initialize vector table pointer */
1:auipc a0, %pcrel_hi(__jvt_base$)
  addi  a0, a0, %pcrel_lo(1b)
  csrw  jvt, a0
.option pop

/* initialize stack pointer */
  la sp, __stack_end

/* clear the bss segment */
  la a0, _edata
  la a2, _end
  sub a2, a2, a0
  li a1, 0
  call memset

/* new-style constructors and destructors */
  la a0, __libc_fini_array
  call atexit
  call __libc_init_array

/* call main */
// Initialize these variables to 0. Cannot use argc or argv
// since the stack is not initialized
  li a0, 0
  li a1, 0
  li a2, 0

  call main
  tail exit

.size  _start, .-_start


.global _init
.type   _init, @function
.global _fini
.type   _fini, @function
_init:
_fini:
 /* These don't have to do anything since we use init_array/fini_array. Prevent
    missing symbol error */
  ret
.size  _init, .-_init
.size _fini, .-_fini
