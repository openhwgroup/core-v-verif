#Copyright 202[x] Silicon Labs, Inc.
  
#This file, and derivatives thereof are licensed under the
#Solderpad License, Version 2.0 (the "License");
#Use of this file means you agree to the terms and conditions
#of the license and are in full compliance with the License.
#You may obtain a copy of the License at
#  
#    https://solderpad.org/licenses/SHL-2.0/
#  
#Unless required by applicable law or agreed to in writing, software
#and hardware implementations thereof
#distributed under the License is distributed on an "AS IS" BASIS,
#WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
#See the License for the specific language governing permissions and
#limitations under the License.

.section .single_step_code_sect, "ax"
.set test_ret_val, 0x20000000
.set test_fail, 0x1

.global glb_step_info
.global glb_expect_debug_entry
.global _single_step


_single_step:        
        addi sp,sp,-30
        sw t0, 0(sp)
        sw t1, 4(sp)
        sw a0, 8(sp)
        sw a1, 12(sp)
        sw a2, 16(sp)
        sw ra, 20(sp)

    // Expect debug
    la a1, glb_expect_debug_entry        
    li t0, 1
    sw t0, 0(a1)

    // Set step cause to 1 - enable single stepping
    la a1, glb_step_info
    li t0, 1
    sw t0, 0(a1)
  
    // Set t0 to 0
    li t0, 0
     
    // Enter debug mode to execute cause=1 
    c.ebreak

    // To check if debug code increments DPC correctly,
    // Load up t0 in first instruction after ebreak
    li t0, 1
    beq t0, x0, _single_step_fail
   
    // Simple instructions 
    nop
    nop
    nop

    // Simple Hardware Loop
    li x15, 0
    li x17, 0
    li x18, 0
    li x19, 0

    .balign 4

    cv.starti 0, startO_1
    cv.endi 0, endO_1
    cv.counti 0, 10
startO_1:
    .option norvc
    addi x17, x17, 1
    addi x18, x18, 2
    addi x19, x19, 3
endO_1:
    .option rvc

    // Compare with expected result
    li x20, 10
    beq x20, x17, test1_1
    c.addi x15, 0x1
test1_1:
    li x20, 20
    beq x20, x18, test1_2
    c.addi x15, 0x1
test1_2:
    li x20, 30
    beq x20, x19, test1_3
    c.addi x15, 0x1
test1_3:

    bne x15, x0, _single_step_fail

    // Simple instructions 
    nop
    nop
    nop

    // Nested Hardware Loops with setup instructions
    li x15, 0
    li x17, 0
    li x18, 0
    li x19, 0
    li x20, 0
    li x21, 0
    li x22, -1

    .balign 4

    cv.setupi 1, 5, endO_2
startO_2:
    cv.setupi 0, 5, endZ_2
    .option norvc
startZ_2:
    addi x17, x17, 1
    addi x18, x18, 2
    mulh x19, x18, x22
endZ_2:
    addi x20, x20, 4
    addi x21, x21, 5
endO_2:
    .option rvc

    // Compare with expected result
    li x22, 25
    beq x22, x17, test2_1
    c.addi x15, 0x1
test2_1:
    li x22, 50
    beq x22, x18, test2_2
    c.addi x15, 0x1
test2_2:
    li x22, -1
    beq x22, x19, test2_3
    c.addi x15, 0x1
test2_3:
    li x22, 20
    beq x22, x20, test2_4
    c.addi x15, 0x1
test2_4:
    li x22, 25
    beq x22, x21, test2_5
    c.addi x15, 0x1
test2_5:

    bne x15, x0, _single_step_fail

    // Simple instructions 
    nop
    nop
    nop

    // Nested Hardware Loops with start/end/count instructions
    li x15, 0
    li x17, 0
    li x18, 0
    li x19, 0
    li x20, 0
    li x21, 0

    li x4, 3
    li x5, 4
1:	auipc x6, %pcrel_hi(endO_3)
	  addi  x6, x6, %pcrel_lo(1b)
2:	auipc x7, %pcrel_hi(startO_3)
	  addi  x7, x7, %pcrel_lo(2b)
3:	auipc x8, %pcrel_hi(endZ_3)
	  addi  x8, x8, %pcrel_lo(3b)
4:	auipc x9, %pcrel_hi(startZ_3)
	  addi  x9, x9, %pcrel_lo(4b)

    .balign 4

    cv.count 1, x4
    cv.end 1, x6
    cv.start 1, x7
    cv.end 0, x8
    cv.start 0, x9
    cv.count 0, x5
startO_3:
    .option norvc
startZ_3:
    addi x17, x17, 5
    addi x18, x18, 6
    fdiv.s x19, x18, x17
endZ_3:
    cv.count 0, x5
    addi x20, x20, 8
endO_3:

    .option rvc

    // Compare with expected result
    li x21, 60
    beq x21, x17, test3_1
    c.addi x15, 0x1
test3_1:
    li x21, 72
    beq x21, x18, test3_2
    c.addi x15, 0x1
test3_2:
    li x21, 75
//  beq x21, x19, test3_3
//  c.addi x15, 0x1
test3_3:
    li x21, 24
    beq x21, x20, test3_4
    c.addi x15, 0x1
test3_4:

    bne x15, x0, _single_step_fail

    // Simple instructions 
    nop
    nop
    nop

    // Cause 2, disable single stepping
    la a1, glb_step_info
    li t0, 2
    sw t0, 0(a1)
    nop
    nop
    j _single_step_done

_single_step_fail:
    li a0, test_ret_val
    li t0, test_fail
    sw t0, 0(a0)
    // Turn off single step
    la a1, glb_step_info
    li t0, 2
    sw t0, 0(a1)
 
    j _single_step_done

_single_step_done:	
        lw t0, 0(sp)
        lw t1, 4(sp)
        lw a0, 8(sp)
        lw a1, 12(sp)
        lw a2, 16(sp)
        lw ra, 20(sp)
        addi sp,sp,30
	ret
