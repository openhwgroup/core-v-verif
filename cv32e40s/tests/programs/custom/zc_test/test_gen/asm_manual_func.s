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
** Assembly functions to help the tests in the zc_tests.c source file.
**
*******************************************************************************
*/

// _GEN END OF HEADER GEN_

// Funtions
enable_all_irq:
  //set all fields of mie, hardwired are ignored (WARL)
  li	t0, 0xFFFFFFFF
	 csrrw x0, mie, t0

  li	t0, 0x00000008
	 csrrs x0, mstatus, t0

  jalr	x0, 0(ra)

trigger_irq:
  // trigger irq
  li  t0, 0x00800140
  la  t1, glb_irq_line
  lw  t2, 0(t1)
  la  t1, glb_irq_delay
  lw  t3, 0(t1)
  sw  t2, 0(t0)
  sw  t3, 4(t0)

  //return to caller
  jalr	x0, 0(ra)

  /*
  ** The rest of this file consist of generated functions that work in the following manner:
  ** interrupt_push_pop:
  **    input value determines which rlist to test (case statement)
  **    jump to interrupt trigger routine
  **      - sets an interrupt to hit the atomic part of the following instruction,
  **      - set up from C test by global variables
  **    run push instruction to test
  **    jump to interrupt trigger routine
  **    run pop instruction to test
  **
  ** interrupt_popret/popretz
  **    input value determines which rlist to test (case statement)
  **    load ra with the address for thenext instruction after the popret
  **      to enable the popret to return to the program
  **    make a push to keep the stack pointer valid after the function call
  **    jump to interrupt trigger routine
  **    run popret/z instruction to test
  **
  ** interrupt mvsa
  **    input value determines which sreg combination to test (case statement)
  **    populate registers with random data
  **    jump to interrupt trigger routine
  **    run mvsa01 instruction to test
  **
  **
  ** interrupt mvsa
  **    input value determines which sreg combination to test (case statement)
  **    populate registers with random data
  **    jump to interrupt trigger routine
  **    run mva01s instruction to test
  **
  */
