// Copyright 2020 EM Microelectronic US Inc.
// Copyright 2020 OpenHW Group
// Copyright 2023 Dolphin Design
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0
//
// Description : PULP Hardware Loops instructions test
//

.globl _start
.globl main
.globl exit
.section .text
.global test_results
test_results:
	.word 123456789
#tests hardware loops instructions. NOTE: value of register x15 at the end of the test is the error count
main:
# enable interrupts
    li        t0, (0x1 << 3)
    csrs      mstatus, t0
# main test
    li x0, 0xf21ee7dc
    li x1, 0x80000000
//  li x3, 0xccda4374
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

#test1 hardware loops programmed using immediates starti, endi and counti instructions
test1:
    li x17, 0
    li x18, 0

    .balign 4

    cv.starti 1, startO_1
    cv.endi 1, endO_1
    cv.counti 1, 10
    cv.starti 0, startZ_1
    cv.endi 0, endZ_1
startO_1:
    cv.counti 0, 10

    .option norvc

startZ_1:
    addi x17, x17, 1
    addi x17, x17, 1
    addi x17, x17, 1
endZ_1:
    addi x18, x18, 1
    addi x18, x18, 1
endO_1:

    .option rvc

    li x20, 300
    beq x20, x17, test1_1
    c.addi x15, 0x1
test1_1:
    li x21, 20
    beq x21, x18, test2
    c.addi x15, 0x1

#test2 hardware loops programmed using registers start, end and count instructions
test2:
    li x17, 0
    li x18, 0

    li x5, 10
1:	auipc x6, %pcrel_hi(endO_2)
	  addi  x6, x6, %pcrel_lo(1b)
2:	auipc x7, %pcrel_hi(startO_2)
	  addi  x7, x7, %pcrel_lo(2b)
3:	auipc x8, %pcrel_hi(endZ_2)
	  addi  x8, x8, %pcrel_lo(3b)
4:	auipc x9, %pcrel_hi(startZ_2)
	  addi  x9, x9, %pcrel_lo(4b)

    .balign 4

    cv.start 1, x7
    cv.end 1, x6
    cv.count 1, x5
    cv.start 0, x9
    cv.end 0, x8
startO_2:
    cv.count 0, x5

    .option norvc

startZ_2:
    addi x17, x17, 1
    addi x17, x17, 1
    addi x17, x17, 1
endZ_2:
    addi x18, x18, 2
    addi x18, x18, 2
endO_2:

    .option rvc

    li x20, 300
    beq x20, x17, test2_1
    c.addi x15, 0x1
test2_1:
    li x21, 40
    beq x21, x18, test3
    c.addi x15, 0x1

#test3 hardware loops programmed using immediates setupi instruction
test3:
    li x17, 0
    li x18, 0

    .balign 4

    cv.setupi 1, 10, endO_3
startO_3:
    cv.setupi 0, 10, endZ_3

    .option norvc

startZ_3:
    addi x17, x17, 1
    addi x17, x17, 1
    addi x17, x17, 1
endZ_3:
    addi x18, x18, 2
    addi x18, x18, 2
endO_3:

    .option rvc

    li x20, 300
    beq x20, x17, test3_1
    c.addi x15, 0x1
test3_1:
    li x21, 40
    beq x21, x18, test4
    c.addi x15, 0x1

#test4 hardware loops programmed using immediates setup instruction
test4:
    li x17, 0
    li x18, 0

    li x5, 10

    .balign 4

    cv.setup 1, x5, endO_4
startO_4:
    cv.setup 0, x5, endZ_4

    .option norvc

startZ_4:
    addi x17, x17, 1
    addi x17, x17, 1
    addi x17, x17, 1
endZ_4:
    addi x18, x18, 2
    addi x18, x18, 2
endO_4:

    .option rvc

    li x20, 300
    beq x20, x17, test4_1
    c.addi x15, 0x1
test4_1:
    li x21, 40
    beq x21, x18, test5
    c.addi x15, 0x1

#test5 hardware read checks
test5:

    li x5, 0x12345678
    li x6, 0x9abcdef0
    li x7, 0x55555555
    li x8, 0xaaaaaaaa
    li x9, 0xffffffff
    li x10, 0x5afc6257

    cv.start 0, x5
    cv.end 0, x6
    cv.count 0, x7

    cv.start 1, x8
    cv.end 1, x9
    cv.count 1, x10

    csrr x20, 0xCC0
    andi x5, x5, -4
    beq x20, x5, test5_1
    c.addi x15, 0x1
test5_1:
    csrr x20, 0xCC1
    andi x6, x6, -4
    beq x20, x6, test5_2
    c.addi x15, 0x1
test5_2:
    csrr x20, 0xCC2
    beq x20, x7, test5_3
    c.addi x15, 0x1
test5_3:
    csrr x20, 0xCC4
    c.andi x8, -4
    beq x20, x8, test5_4
    c.addi x15, 0x1
test5_4:
    csrr x20, 0xCC5
    c.andi x9, -4
    beq x20, x9, test5_5
    c.addi x15, 0x1
test5_5:
    csrr x20, 0xCC6
    beq x20, x10, test6
    c.addi x15, 0x1

#test6 hardware write checks
test6:

    csrwi 0xCC1, 0x5
    csrwi 0xCC0, 0x6
    csrwi 0xCC2, 0x7
    csrwi 0xCC5, 0x8
    csrwi 0xCC4, 0x9
    csrwi 0xCC6, 0xa

#if 0
    // Not trapping CSRW
    li x5, 0x5
    li x6, 0x6
    li x7, 0x7
    li x8, 0x8
    li x9, 0x9
    li x10, 0xa
#else
    // Trapping CSRW
    li x5, 0x9abcdef0
    li x6, 0x12345678
    li x7, 0x55555555
    li x8, 0xffffffff
    li x9, 0xaaaaaaaa
    li x10, 0x5afc6257
#endif

    csrr x20, 0xCC0
    andi x6, x6, -4
    beq x20, x6, test6_1
    c.addi x15, 0x1
test6_1:
    csrr x20, 0xCC1
    andi x5, x5, -4
    beq x20, x5, test6_2
    c.addi x15, 0x1
test6_2:
    csrr x20, 0xCC2
    beq x20, x7, test6_3
    c.addi x15, 0x1
test6_3:
    csrr x20, 0xCC4
    c.andi x9, -4
    beq x20, x9, test6_4
    c.addi x15, 0x1
test6_4:
    csrr x20, 0xCC5
    c.andi x8, -4
    beq x20, x8, test6_5
    c.addi x15, 0x1
test6_5:
    csrr x20, 0xCC6
    beq x20, x10, test7
    c.addi x15, 0x1


# test7 CSR read accesses during HWloop (same as test1 but with CSR reads to misa)

test7:
    li x5, 0
    li x6, 0
    li x7, 0
    li x8, 0
    li x17, 0
    li x18, 0

    .balign 4

    cv.starti 1, startO_7
    cv.endi 1, endO_7
    cv.counti 1, 10
    cv.starti 0, startZ_7
    cv.endi 0, endZ_7
startO_7:
    cv.counti 0, 10
    csrrw x5, 0x301, x0 # misa

    .option norvc

startZ_7:
    addi x17, x17, 1
    csrrw x5, 0x301, x0 # misa
    addi x17, x17, 1
    addi x17, x17, 1
    csrrw x6, 0x301, x0 # misa
endZ_7:
    addi x18, x18, 1
    csrrw x7, 0x301, x0 # misa
    addi x18, x18, 1
    csrrw x8, 0x301, x0 # misa
endO_7:

    .option rvc

    li x20, 300
    beq x20, x17, test7_1
    c.addi x15, 0x1
test7_1:
    li x21, 20
    beq x21, x18, exit_check
    c.addi x15, 0x1

exit_check:
    lw x18, test_results /* report result */
    beq x15, x0, exit
    li x18, 1
exit:
    li x17, 0x20000000
    sw x18,0(x17)
    wfi
