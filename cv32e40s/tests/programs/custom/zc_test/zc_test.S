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

.section .data
glb_irq_line:
  .word 0
glb_irq_delay:
  .word 0
stored_ra:
  .word 0

.section .text

.global glb_irq_line
.global glb_irq_delay

// Functions
.global enable_all_irq

//Generated Functions
.global interrupt_push_pop
.global interrupt_popret
.global interrupt_popretz
.global interrupt_mvsa
.global interrupt_mvas


//instruction tags
.global push_0
.global pop_0
.global push_1
.global pop_1
.global push_2
.global pop_2
.global push_3
.global pop_3
.global push_4
.global pop_4
.global push_5
.global pop_5
.global push_6
.global pop_6
.global push_7
.global pop_7
.global push_8
.global pop_8
.global push_9
.global pop_9
.global push_10
.global pop_10
.global push_11
.global pop_11
.global popret_0
.global popret_1
.global popret_2
.global popret_3
.global popret_4
.global popret_5
.global popret_6
.global popret_7
.global popret_8
.global popret_9
.global popret_10
.global popret_11
.global popretz_0
.global popretz_1
.global popretz_2
.global popretz_3
.global popretz_4
.global popretz_5
.global popretz_6
.global popretz_7
.global popretz_8
.global popretz_9
.global popretz_10
.global popretz_11
.global mvsa_0
.global mvsa_1
.global mvsa_2
.global mvsa_3
.global mvsa_4
.global mvsa_5
.global mvsa_6
.global mvsa_7
.global mvsa_8
.global mvsa_9
.global mvsa_10
.global mvsa_11
.global mvsa_12
.global mvsa_13
.global mvsa_14
.global mvsa_15
.global mvas_0
.global mvas_1
.global mvas_2
.global mvas_3
.global mvas_4
.global mvas_5
.global mvas_6
.global mvas_7
.global mvas_8
.global mvas_9
.global mvas_10
.global mvas_11
.global mvas_12
.global mvas_13
.global mvas_14
.global mvas_15

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


//Generated Functions
interrupt_push_pop:
  la t0, stored_ra
  sw ra, 0(t0)


  pp_case_4:
    li t1, 4
    bne a0, t1, pp_case_5
    jal ra, trigger_irq
  push_0:
    cm.push {ra}, -64
    nop
    nop

    jal ra, trigger_irq
  pop_0:
    cm.pop {ra}, 64
    nop
    nop
    j pp_case_end



  pp_case_5:
    li t1, 5
    bne a0, t1, pp_case_6
    jal ra, trigger_irq
  push_1:
    cm.push {ra, s0}, -64
    nop
    nop

    jal ra, trigger_irq
  pop_1:
    cm.pop {ra, s0}, 64
    nop
    nop
    j pp_case_end



  pp_case_6:
    li t1, 6
    bne a0, t1, pp_case_7
    jal ra, trigger_irq
  push_2:
    cm.push {ra, s0-s1}, -64
    nop
    nop

    jal ra, trigger_irq
  pop_2:
    cm.pop {ra, s0-s1}, 64
    nop
    nop
    j pp_case_end



  pp_case_7:
    li t1, 7
    bne a0, t1, pp_case_8
    jal ra, trigger_irq
  push_3:
    cm.push {ra, s0-s2}, -64
    nop
    nop

    jal ra, trigger_irq
  pop_3:
    cm.pop {ra, s0-s2}, 64
    nop
    nop
    j pp_case_end



  pp_case_8:
    li t1, 8
    bne a0, t1, pp_case_9
    jal ra, trigger_irq
  push_4:
    cm.push {ra, s0-s3}, -64
    nop
    nop

    jal ra, trigger_irq
  pop_4:
    cm.pop {ra, s0-s3}, 64
    nop
    nop
    j pp_case_end



  pp_case_9:
    li t1, 9
    bne a0, t1, pp_case_10
    jal ra, trigger_irq
  push_5:
    cm.push {ra, s0-s4}, -64
    nop
    nop

    jal ra, trigger_irq
  pop_5:
    cm.pop {ra, s0-s4}, 64
    nop
    nop
    j pp_case_end



  pp_case_10:
    li t1, 10
    bne a0, t1, pp_case_11
    jal ra, trigger_irq
  push_6:
    cm.push {ra, s0-s5}, -64
    nop
    nop

    jal ra, trigger_irq
  pop_6:
    cm.pop {ra, s0-s5}, 64
    nop
    nop
    j pp_case_end



  pp_case_11:
    li t1, 11
    bne a0, t1, pp_case_12
    jal ra, trigger_irq
  push_7:
    cm.push {ra, s0-s6}, -64
    nop
    nop

    jal ra, trigger_irq
  pop_7:
    cm.pop {ra, s0-s6}, 64
    nop
    nop
    j pp_case_end



  pp_case_12:
    li t1, 12
    bne a0, t1, pp_case_13
    jal ra, trigger_irq
  push_8:
    cm.push {ra, s0-s7}, -64
    nop
    nop

    jal ra, trigger_irq
  pop_8:
    cm.pop {ra, s0-s7}, 64
    nop
    nop
    j pp_case_end



  pp_case_13:
    li t1, 13
    bne a0, t1, pp_case_14
    jal ra, trigger_irq
  push_9:
    cm.push {ra, s0-s8}, -64
    nop
    nop

    jal ra, trigger_irq
  pop_9:
    cm.pop {ra, s0-s8}, 64
    nop
    nop
    j pp_case_end



  pp_case_14:
    li t1, 14
    bne a0, t1, pp_case_15
    jal ra, trigger_irq
  push_10:
    cm.push {ra, s0-s9}, -64
    nop
    nop

    jal ra, trigger_irq
  pop_10:
    cm.pop {ra, s0-s9}, 64
    nop
    nop
    j pp_case_end



  pp_case_15:
    li t1, 15
    bne a0, t1, pp_case_end
    jal ra, trigger_irq
  push_11:
    cm.push {ra, s0-s11}, -64
    nop
    nop

    jal ra, trigger_irq
  pop_11:
    cm.pop {ra, s0-s11}, 64
    nop
    nop
    j pp_case_end



  pp_case_end:
  //return to caller
  la t0, stored_ra
  lw ra, 0(t0)
  jalr	x0, 0(ra)



interrupt_popret:
  la t0, stored_ra
  sw ra, 0(t0)


  pr_case_4:
    li t1, 4
    bne a0, t1, pr_case_5
    la ra, popret_0_ret
    cm.push {ra}, -64
    jal ra, trigger_irq
  popret_0:
    cm.popret {ra}, 64
  popret_0_ret:
    nop
    nop
    j pr_case_end



  pr_case_5:
    li t1, 5
    bne a0, t1, pr_case_6
    la ra, popret_1_ret
    cm.push {ra, s0}, -64
    jal ra, trigger_irq
  popret_1:
    cm.popret {ra, s0}, 64
  popret_1_ret:
    nop
    nop
    j pr_case_end



  pr_case_6:
    li t1, 6
    bne a0, t1, pr_case_7
    la ra, popret_2_ret
    cm.push {ra, s0-s1}, -64
    jal ra, trigger_irq
  popret_2:
    cm.popret {ra, s0-s1}, 64
  popret_2_ret:
    nop
    nop
    j pr_case_end



  pr_case_7:
    li t1, 7
    bne a0, t1, pr_case_8
    la ra, popret_3_ret
    cm.push {ra, s0-s2}, -64
    jal ra, trigger_irq
  popret_3:
    cm.popret {ra, s0-s2}, 64
  popret_3_ret:
    nop
    nop
    j pr_case_end



  pr_case_8:
    li t1, 8
    bne a0, t1, pr_case_9
    la ra, popret_4_ret
    cm.push {ra, s0-s3}, -64
    jal ra, trigger_irq
  popret_4:
    cm.popret {ra, s0-s3}, 64
  popret_4_ret:
    nop
    nop
    j pr_case_end



  pr_case_9:
    li t1, 9
    bne a0, t1, pr_case_10
    la ra, popret_5_ret
    cm.push {ra, s0-s4}, -64
    jal ra, trigger_irq
  popret_5:
    cm.popret {ra, s0-s4}, 64
  popret_5_ret:
    nop
    nop
    j pr_case_end



  pr_case_10:
    li t1, 10
    bne a0, t1, pr_case_11
    la ra, popret_6_ret
    cm.push {ra, s0-s5}, -64
    jal ra, trigger_irq
  popret_6:
    cm.popret {ra, s0-s5}, 64
  popret_6_ret:
    nop
    nop
    j pr_case_end



  pr_case_11:
    li t1, 11
    bne a0, t1, pr_case_12
    la ra, popret_7_ret
    cm.push {ra, s0-s6}, -64
    jal ra, trigger_irq
  popret_7:
    cm.popret {ra, s0-s6}, 64
  popret_7_ret:
    nop
    nop
    j pr_case_end



  pr_case_12:
    li t1, 12
    bne a0, t1, pr_case_13
    la ra, popret_8_ret
    cm.push {ra, s0-s7}, -64
    jal ra, trigger_irq
  popret_8:
    cm.popret {ra, s0-s7}, 64
  popret_8_ret:
    nop
    nop
    j pr_case_end



  pr_case_13:
    li t1, 13
    bne a0, t1, pr_case_14
    la ra, popret_9_ret
    cm.push {ra, s0-s8}, -64
    jal ra, trigger_irq
  popret_9:
    cm.popret {ra, s0-s8}, 64
  popret_9_ret:
    nop
    nop
    j pr_case_end



  pr_case_14:
    li t1, 14
    bne a0, t1, pr_case_15
    la ra, popret_10_ret
    cm.push {ra, s0-s9}, -64
    jal ra, trigger_irq
  popret_10:
    cm.popret {ra, s0-s9}, 64
  popret_10_ret:
    nop
    nop
    j pr_case_end



  pr_case_15:
    li t1, 15
    bne a0, t1, pr_case_end
    la ra, popret_11_ret
    cm.push {ra, s0-s11}, -64
    jal ra, trigger_irq
  popret_11:
    cm.popret {ra, s0-s11}, 64
  popret_11_ret:
    nop
    nop
    j pr_case_end



  pr_case_end:
  //return to caller
  la t0, stored_ra
  lw ra, 0(t0)
  jalr	x0, 0(ra)
interrupt_popretz:
  la t0, stored_ra
  sw ra, 0(t0)


  prz_case_4:
    li t1, 4
    bne a0, t1, prz_case_5
    la ra, popretz_0_ret
    cm.push {ra}, -64
    jal ra, trigger_irq
  popretz_0:
    cm.popretz {ra}, 64
  popretz_0_ret:
    nop
    nop
    j prz_case_end



  prz_case_5:
    li t1, 5
    bne a0, t1, prz_case_6
    la ra, popretz_1_ret
    cm.push {ra, s0}, -64
    jal ra, trigger_irq
  popretz_1:
    cm.popretz {ra, s0}, 64
  popretz_1_ret:
    nop
    nop
    j prz_case_end



  prz_case_6:
    li t1, 6
    bne a0, t1, prz_case_7
    la ra, popretz_2_ret
    cm.push {ra, s0-s1}, -64
    jal ra, trigger_irq
  popretz_2:
    cm.popretz {ra, s0-s1}, 64
  popretz_2_ret:
    nop
    nop
    j prz_case_end



  prz_case_7:
    li t1, 7
    bne a0, t1, prz_case_8
    la ra, popretz_3_ret
    cm.push {ra, s0-s2}, -64
    jal ra, trigger_irq
  popretz_3:
    cm.popretz {ra, s0-s2}, 64
  popretz_3_ret:
    nop
    nop
    j prz_case_end



  prz_case_8:
    li t1, 8
    bne a0, t1, prz_case_9
    la ra, popretz_4_ret
    cm.push {ra, s0-s3}, -64
    jal ra, trigger_irq
  popretz_4:
    cm.popretz {ra, s0-s3}, 64
  popretz_4_ret:
    nop
    nop
    j prz_case_end



  prz_case_9:
    li t1, 9
    bne a0, t1, prz_case_10
    la ra, popretz_5_ret
    cm.push {ra, s0-s4}, -64
    jal ra, trigger_irq
  popretz_5:
    cm.popretz {ra, s0-s4}, 64
  popretz_5_ret:
    nop
    nop
    j prz_case_end



  prz_case_10:
    li t1, 10
    bne a0, t1, prz_case_11
    la ra, popretz_6_ret
    cm.push {ra, s0-s5}, -64
    jal ra, trigger_irq
  popretz_6:
    cm.popretz {ra, s0-s5}, 64
  popretz_6_ret:
    nop
    nop
    j prz_case_end



  prz_case_11:
    li t1, 11
    bne a0, t1, prz_case_12
    la ra, popretz_7_ret
    cm.push {ra, s0-s6}, -64
    jal ra, trigger_irq
  popretz_7:
    cm.popretz {ra, s0-s6}, 64
  popretz_7_ret:
    nop
    nop
    j prz_case_end



  prz_case_12:
    li t1, 12
    bne a0, t1, prz_case_13
    la ra, popretz_8_ret
    cm.push {ra, s0-s7}, -64
    jal ra, trigger_irq
  popretz_8:
    cm.popretz {ra, s0-s7}, 64
  popretz_8_ret:
    nop
    nop
    j prz_case_end



  prz_case_13:
    li t1, 13
    bne a0, t1, prz_case_14
    la ra, popretz_9_ret
    cm.push {ra, s0-s8}, -64
    jal ra, trigger_irq
  popretz_9:
    cm.popretz {ra, s0-s8}, 64
  popretz_9_ret:
    nop
    nop
    j prz_case_end



  prz_case_14:
    li t1, 14
    bne a0, t1, prz_case_15
    la ra, popretz_10_ret
    cm.push {ra, s0-s9}, -64
    jal ra, trigger_irq
  popretz_10:
    cm.popretz {ra, s0-s9}, 64
  popretz_10_ret:
    nop
    nop
    j prz_case_end



  prz_case_15:
    li t1, 15
    bne a0, t1, prz_case_end
    la ra, popretz_11_ret
    cm.push {ra, s0-s11}, -64
    jal ra, trigger_irq
  popretz_11:
    cm.popretz {ra, s0-s11}, 64
  popretz_11_ret:
    nop
    nop
    j prz_case_end



  prz_case_end:
  //return to caller
  la t0, stored_ra
  lw ra, 0(t0)
  jalr	x0, 0(ra)
interrupt_mvsa:
  la t0, stored_ra
  sw ra, 0(t0)


  sa_case_0:
    li t1, 0
    bne a0, t1, sa_case_1
    mv s2, a2
    mv s6, a3
    jal ra, trigger_irq
  mvsa_0:
    cm.mvsa01 s2, s6
    nop
    nop
    j sa_case_end



  sa_case_1:
    li t1, 1
    bne a0, t1, sa_case_2
    mv s2, a2
    mv s3, a3
    jal ra, trigger_irq
  mvsa_1:
    cm.mvsa01 s2, s3
    nop
    nop
    j sa_case_end



  sa_case_2:
    li t1, 2
    bne a0, t1, sa_case_3
    mv s2, a2
    mv s1, a3
    jal ra, trigger_irq
  mvsa_2:
    cm.mvsa01 s2, s1
    nop
    nop
    j sa_case_end



  sa_case_3:
    li t1, 3
    bne a0, t1, sa_case_4
    mv s2, a2
    mv s0, a3
    jal ra, trigger_irq
  mvsa_3:
    cm.mvsa01 s2, s0
    nop
    nop
    j sa_case_end



  sa_case_4:
    li t1, 4
    bne a0, t1, sa_case_5
    mv s4, a2
    mv s6, a3
    jal ra, trigger_irq
  mvsa_4:
    cm.mvsa01 s4, s6
    nop
    nop
    j sa_case_end



  sa_case_5:
    li t1, 5
    bne a0, t1, sa_case_6
    mv s4, a2
    mv s3, a3
    jal ra, trigger_irq
  mvsa_5:
    cm.mvsa01 s4, s3
    nop
    nop
    j sa_case_end



  sa_case_6:
    li t1, 6
    bne a0, t1, sa_case_7
    mv s4, a2
    mv s1, a3
    jal ra, trigger_irq
  mvsa_6:
    cm.mvsa01 s4, s1
    nop
    nop
    j sa_case_end



  sa_case_7:
    li t1, 7
    bne a0, t1, sa_case_8
    mv s4, a2
    mv s0, a3
    jal ra, trigger_irq
  mvsa_7:
    cm.mvsa01 s4, s0
    nop
    nop
    j sa_case_end



  sa_case_8:
    li t1, 8
    bne a0, t1, sa_case_9
    mv s5, a2
    mv s6, a3
    jal ra, trigger_irq
  mvsa_8:
    cm.mvsa01 s5, s6
    nop
    nop
    j sa_case_end



  sa_case_9:
    li t1, 9
    bne a0, t1, sa_case_10
    mv s5, a2
    mv s3, a3
    jal ra, trigger_irq
  mvsa_9:
    cm.mvsa01 s5, s3
    nop
    nop
    j sa_case_end



  sa_case_10:
    li t1, 10
    bne a0, t1, sa_case_11
    mv s5, a2
    mv s1, a3
    jal ra, trigger_irq
  mvsa_10:
    cm.mvsa01 s5, s1
    nop
    nop
    j sa_case_end



  sa_case_11:
    li t1, 11
    bne a0, t1, sa_case_12
    mv s5, a2
    mv s0, a3
    jal ra, trigger_irq
  mvsa_11:
    cm.mvsa01 s5, s0
    nop
    nop
    j sa_case_end



  sa_case_12:
    li t1, 12
    bne a0, t1, sa_case_13
    mv s7, a2
    mv s6, a3
    jal ra, trigger_irq
  mvsa_12:
    cm.mvsa01 s7, s6
    nop
    nop
    j sa_case_end



  sa_case_13:
    li t1, 13
    bne a0, t1, sa_case_14
    mv s7, a2
    mv s3, a3
    jal ra, trigger_irq
  mvsa_13:
    cm.mvsa01 s7, s3
    nop
    nop
    j sa_case_end



  sa_case_14:
    li t1, 14
    bne a0, t1, sa_case_15
    mv s7, a2
    mv s1, a3
    jal ra, trigger_irq
  mvsa_14:
    cm.mvsa01 s7, s1
    nop
    nop
    j sa_case_end



  sa_case_15:
    li t1, 15
    bne a0, t1, sa_case_end
    mv s7, a2
    mv s0, a3
    jal ra, trigger_irq
  mvsa_15:
    cm.mvsa01 s7, s0
    nop
    nop
    j sa_case_end



  sa_case_end:
  //return to caller
  la t0, stored_ra
  lw ra, 0(t0)
  jalr	x0, 0(ra)



interrupt_mvas:
  la t0, stored_ra
  sw ra, 0(t0)


  as_case_0:
    li t1, 0
    bne a0, t1, as_case_1
    mv s2, a2
    mv s6, a3
    jal ra, trigger_irq
  mvas_0:
    cm.mva01s s2, s6
    nop
    nop
    j as_case_end



  as_case_1:
    li t1, 1
    bne a0, t1, as_case_2
    mv s2, a2
    mv s3, a3
    jal ra, trigger_irq
  mvas_1:
    cm.mva01s s2, s3
    nop
    nop
    j as_case_end



  as_case_2:
    li t1, 2
    bne a0, t1, as_case_3
    mv s2, a2
    mv s1, a3
    jal ra, trigger_irq
  mvas_2:
    cm.mva01s s2, s1
    nop
    nop
    j as_case_end



  as_case_3:
    li t1, 3
    bne a0, t1, as_case_4
    mv s2, a2
    mv s0, a3
    jal ra, trigger_irq
  mvas_3:
    cm.mva01s s2, s0
    nop
    nop
    j as_case_end



  as_case_4:
    li t1, 4
    bne a0, t1, as_case_5
    mv s4, a2
    mv s6, a3
    jal ra, trigger_irq
  mvas_4:
    cm.mva01s s4, s6
    nop
    nop
    j as_case_end



  as_case_5:
    li t1, 5
    bne a0, t1, as_case_6
    mv s4, a2
    mv s3, a3
    jal ra, trigger_irq
  mvas_5:
    cm.mva01s s4, s3
    nop
    nop
    j as_case_end



  as_case_6:
    li t1, 6
    bne a0, t1, as_case_7
    mv s4, a2
    mv s1, a3
    jal ra, trigger_irq
  mvas_6:
    cm.mva01s s4, s1
    nop
    nop
    j as_case_end



  as_case_7:
    li t1, 7
    bne a0, t1, as_case_8
    mv s4, a2
    mv s0, a3
    jal ra, trigger_irq
  mvas_7:
    cm.mva01s s4, s0
    nop
    nop
    j as_case_end



  as_case_8:
    li t1, 8
    bne a0, t1, as_case_9
    mv s5, a2
    mv s6, a3
    jal ra, trigger_irq
  mvas_8:
    cm.mva01s s5, s6
    nop
    nop
    j as_case_end



  as_case_9:
    li t1, 9
    bne a0, t1, as_case_10
    mv s5, a2
    mv s3, a3
    jal ra, trigger_irq
  mvas_9:
    cm.mva01s s5, s3
    nop
    nop
    j as_case_end



  as_case_10:
    li t1, 10
    bne a0, t1, as_case_11
    mv s5, a2
    mv s1, a3
    jal ra, trigger_irq
  mvas_10:
    cm.mva01s s5, s1
    nop
    nop
    j as_case_end



  as_case_11:
    li t1, 11
    bne a0, t1, as_case_12
    mv s5, a2
    mv s0, a3
    jal ra, trigger_irq
  mvas_11:
    cm.mva01s s5, s0
    nop
    nop
    j as_case_end



  as_case_12:
    li t1, 12
    bne a0, t1, as_case_13
    mv s7, a2
    mv s6, a3
    jal ra, trigger_irq
  mvas_12:
    cm.mva01s s7, s6
    nop
    nop
    j as_case_end



  as_case_13:
    li t1, 13
    bne a0, t1, as_case_14
    mv s7, a2
    mv s3, a3
    jal ra, trigger_irq
  mvas_13:
    cm.mva01s s7, s3
    nop
    nop
    j as_case_end



  as_case_14:
    li t1, 14
    bne a0, t1, as_case_15
    mv s7, a2
    mv s1, a3
    jal ra, trigger_irq
  mvas_14:
    cm.mva01s s7, s1
    nop
    nop
    j as_case_end



  as_case_15:
    li t1, 15
    bne a0, t1, as_case_end
    mv s7, a2
    mv s0, a3
    jal ra, trigger_irq
  mvas_15:
    cm.mva01s s7, s0
    nop
    nop
    j as_case_end



  as_case_end:
  //return to caller
  la t0, stored_ra
  lw ra, 0(t0)
  jalr	x0, 0(ra)



