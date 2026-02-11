#
# Copyright (C) EM Microelectronic US Inc.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
# either express or implied.
#
# See the License for the specific language governing permissions and
# limitations under the License.
#
.globl _start
.globl main
.globl exit
.section .text
.global test_results
test_results:
	.word 123456789
#tests some vectorial/SIMD instructions. NOTE: value of register x15 at the end of the test is the error count
main:
# enable interrupts
    li        t0, (0x1 << 3)
    csrs      mstatus, t0
# main test
    li x0, 0xf21ee7dc
    li x1, 0x80000000
    li x3, 0xccda4374
    li x4, 0x0
    li x5, 0xf4cb539d
    li x6, 0x80000000
    li x7, 0x3
    li x8, 0xfdef1f09
    li x9, 0x80000000
    li x10, 0x4
    li x11, 0xf58fad61
    li x12, 0xfb6606db
    li x13, 0x0
    li x14, 0x0
    li x15, 0x0
    li x16, 0x0
    li x17, 0xf61163af
    li x18, 0x0
    li x19, 0x0
    li x20, 0xc552e854
    li x21, 0xc553e854
    li x22, 0xf3ae47cd
    li x23, 0x0
    li x24, 0x0
    li x25, 0x80000000
    li x26, 0xaad8efdc
    li x27, 0xffa38c28
    li x28, 0xf915a8c7
    li x29, 0x9
    li x30, 0x5
    li x31, 0x5912efde
    li x4, 0x40001104
#tests1-6 test the cv.extract.h instruction. values loaded in and compared to are expected output values
#cv.extract.h is of the form "cv.extract.h rD, rs1, rs2". rD[31:16] = rs1[31:16] >> rs2[31:16], rD[15:0] = rs1[15:0] >> rs2[15:0]
test1:
    li x17, 0x6e83fe1d
    cv.extract.h x19, x17, 0x1
    li x20, 0x00006e83
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0xe0e0ed49
    cv.extract.h x19, x17, 0x0
    li x20, 0xffffed49
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0x13f8c76b
    cv.extract.h x19, x17, 0x0
    li x20, 0xffffc76b
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0x54b60c72
    cv.extract.h x19, x17, 0x1
    li x20, 0x000054b6
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0x7c9f4803
    cv.extract.h x19, x17, 0x1
    li x20, 0x00007c9f
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0x932d8211
    cv.extract.h x19, x17, 0x0
    li x20, 0xffff8211
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the cv.or.extract.b instruction. values loaded in and compared to are expected output values
#cv.extract.b is of the form "cv.extract.b rD, rs1, rs2". rD[31:16] = rs1[31:16] >> rs2[15:0], rD[15:0] = rs1[15:0] >> rs2[15:0]
test7:
    li x17, 0x82c18db2
    cv.extract.b x19, x17, 0x3
    li x20, 0xffffff82
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0x39596713
    cv.extract.b x19, x17, 0x2
    li x20, 0x00000059
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0x7c5c722a
    cv.extract.b x19, x17, 0x1
    li x20, 0x00000072
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0xb2ca6873
    cv.extract.b x19, x17, 0x1
    li x20, 0x00000068
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0x79683a4d
    cv.extract.b x19, x17, 0x0
    li x20, 0x0000004d
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0x47d6b3f0
    cv.extract.b x19, x17, 0x2
    li x20, 0xffffffd6
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the cv.extractu.h instruction. values loaded in and compared to are expected output values
#cv.extractu.h is of the form "cv.extractu.h rD, rs1, Imm6". rD[31:16] = rs1[31:16] >> Imm6, rD[15:0] = rs1[15:0] >> Imm6
test13:
    li x17, 0x8726dc40
    cv.extractu.h x19, x17, 0x0
    li x20, 0x0000dc40
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0xe65f22ef
    cv.extractu.h x19, x17, 0x0
    li x20, 0x000022ef
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0xec24072b
    cv.extractu.h x19, x17, 0x0
    li x20, 0x0000072b
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0xd4565ca5
    cv.extractu.h x19, x17, 0x1
    li x20, 0x0000d456
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x2c7607a3
    cv.extractu.h x19, x17, 0x1
    li x20, 0x00002c76
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0x8f9afbc2
    cv.extractu.h x19, x17, 0x1
    li x20, 0x00008f9a
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the cv.extractu.b instruction. values loaded in and compared to are expected output values
#cv.extractu.b is of the form "cv.extractu.b rD, rs1, rs2". rD[31:24] = rs1[31:24] >> rs2[31:24],
#rD[23:16] = rs1[23:16] >> rs2[23:16], rD[15:8] = rs1[15:8] >> rs2[15:8], rD[7:0] = rs1[7:0] >> rs2[7:0]
test19:
    li x17, 0x91395f1e
    cv.extractu.b x19, x17, 0x3
    li x20, 0x00000091
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0xee565b86
    cv.extractu.b x19, x17, 0x1
    li x20, 0x0000005b
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0x7eed2f26
    cv.extractu.b x19, x17, 0x0
    li x20, 0x00000026
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0x7220a83e
    cv.extractu.b x19, x17, 0x2
    li x20, 0x00000020
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0xacc718a1
    cv.extractu.b x19, x17, 0x2
    li x20, 0x000000c7
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0xffddaaa6
    cv.extractu.b x19, x17, 0x3
    li x20, 0x000000ff
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the cv.insert.h instruction. values loaded in and compared to are expected output values
#cv.insert.h is of the form "cv.insert.h rD, rs1, rs2". rD[31:24] = rs1[31:24] >> rs2[7:0],
#rD[23:16] = rs1[23:16] >> rs2[7:0], rD[15:8] = rs1[15:8] >> rs2[7:0], rD[7:0] = rs1[7:0] >> rs2[7:0]
test25:
    li x19, 0x626ef04f
    li x17, 0x8ac2523d
    cv.insert.h x19, x17, 0x1
    li x20, 0x523df04f
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x19, 0x88fbb7a1
    li x17, 0xd08380a0
    cv.insert.h x19, x17, 0x1
    li x20, 0x80a0b7a1
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x19, 0xbfbacff4
    li x17, 0xdc33ba16
    cv.insert.h x19, x17, 0x1
    li x20, 0xba16cff4
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x19, 0x990fc831
    li x17, 0x600419c0
    cv.insert.h x19, x17, 0x0
    li x20, 0x990f19c0
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x19, 0x044da5f9
    li x17, 0x2cddf91e
    cv.insert.h x19, x17, 0x0
    li x20, 0x044df91e
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x19, 0x5a626f2a
    li x17, 0xe571bb0d
    cv.insert.h x19, x17, 0x0
    li x20, 0x5a62bb0d
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the cv.insert.b instruction. values loaded in and compared to are expected output values
#cv.insert.b is of the form "cv.insert.b rD, rs1, Imm6". rD[31:24] = rs1[31:24] >> Imm6,
#rD[23:16] = rs1[23:16] >> Imm6, rD[15:8] = rs1[15:8] >> Imm6, rD[7:0] = rs1[7:0] >> Imm6
test31:
    li x19, 0xe67cfd8a
    li x17, 0xb589205f
    cv.insert.b x19, x17, 0x1
    li x20, 0xe67c5f8a
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x19, 0xef58b0a8
    li x17, 0x161409d6
    cv.insert.b x19, x17, 0x3
    li x20, 0xd658b0a8
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x19, 0x1d06993b
    li x17, 0xfde810b0
    cv.insert.b x19, x17, 0x0
    li x20, 0x1d0699b0
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x19, 0xc536517f
    li x17, 0x8ffba9b9
    cv.insert.b x19, x17, 0x2
    li x20, 0xc5b9517f
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x19, 0xda47d50c
    li x17, 0x8b13650e
    cv.insert.b x19, x17, 0x3
    li x20, 0x0e47d50c
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x19, 0x4724b9d9
    li x17, 0x8fdfaefe
    cv.insert.b x19, x17, 0x2
    li x20, 0x47feb9d9
    beq x20, x19, exit_check
    c.addi x15, 0x1
exit_check:
    lw x18, test_results /* report result */
    beq x15, x0, exit
    li x18, 1
exit:
    li x17, 0x20000000
    sw x18,0(x17)
    wfi
