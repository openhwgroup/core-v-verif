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
#tests1-6 test the cv.cmpge.h instruction. values loaded in and compared to are expected output values
#cv.cmpge.h is of the form "cv.cmpge.h rD, rs1, rs2".
test1:
    li x17, 0x5d04e2ac
    li x18, 0x8fdfd1f9
    cv.cmpge.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test2
    c.addi x15, 0x1
test2:
    li x17, 0xed38536c
    li x18, 0xf10b7400
    cv.cmpge.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test3
    c.addi x15, 0x1
test3:
    li x17, 0xaec58c96
    li x18, 0xcc367abe
    cv.cmpge.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test4
    c.addi x15, 0x1
test4:
    li x17, 0xfa41584b
    li x18, 0x799ae39e
    cv.cmpge.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test5
    c.addi x15, 0x1
test5:
    li x17, 0xb50d78e7
    li x18, 0xb50d280e
    cv.cmpge.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test6
    c.addi x15, 0x1
test6:
    li x17, 0x6a946ccc
    li x18, 0x5b5c65f7
    cv.cmpge.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test7
    c.addi x15, 0x1
#tests7-12 test the cv.cmpge.sc.h instruction. values loaded in and compared to are expected output values
#cv.cmpge.sc.h is of the form "cv.cmpge.sc.h rD, rs1, rs2".
test7:
    li x17, 0xe65f6c5d
    li x18, 0x76a8c85c
    cv.cmpge.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test8
    c.addi x15, 0x1
test8:
    li x17, 0x395338f8
    li x18, 0xd385fd25
    cv.cmpge.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test9
    c.addi x15, 0x1
test9:
    li x17, 0x05ac90ed
    li x18, 0x9a887b36
    cv.cmpge.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test10
    c.addi x15, 0x1
test10:
    li x17, 0x65530174
    li x18, 0x82014c03
    cv.cmpge.sc.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test11
    c.addi x15, 0x1
test11:
    li x17, 0x91e84198
    li x18, 0xa37791e8
    cv.cmpge.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test12
    c.addi x15, 0x1
test12:
    li x17, 0xfafd58b0
    li x18, 0xfe134f98
    cv.cmpge.sc.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test13
    c.addi x15, 0x1
#tests13-18 test the cv.cmpge.sci.h instruction. values loaded in and compared to are expected output values
#cv.cmpge.sci.h is of the form "cv.cmpge.sci.h rD, rs1, Imm6".
test13:
    li x17, 0xd1c14ae8
    cv.cmpge.sci.h x19, x17, 0xa
    li x20, 0x0000ffff
    beq x20, x19, test14
    c.addi x15, 0x1
test14:
    li x17, 0xb153bb98
    cv.cmpge.sci.h x19, x17, 0x0
    li x20, 0x00000000
    beq x20, x19, test15
    c.addi x15, 0x1
test15:
    li x17, 0x802c4c59
    cv.cmpge.sci.h x19, x17, 0x3
    li x20, 0x0000ffff
    beq x20, x19, test16
    c.addi x15, 0x1
test16:
    li x17, 0x36c40b3e
    cv.cmpge.sci.h x19, x17, 0x5
    li x20, 0xffffffff
    beq x20, x19, test17
    c.addi x15, 0x1
test17:
    li x17, 0x6732bf8b
    cv.cmpge.sci.h x19, x17, 0xf
    li x20, 0xffff0000
    beq x20, x19, test18
    c.addi x15, 0x1
test18:
    li x17, 0x5c4f0002
    cv.cmpge.sci.h x19, x17, 0x2
    li x20, 0xffffffff
    beq x20, x19, test19
    c.addi x15, 0x1
#tests19-24 test the cv.cmpge.b instruction. values loaded in and compared to are expected output values
#cv.cmpge.b is of the form "cv.cmpge.b rD, rs1, rs2".
test19:
    li x17, 0x0237e535
    li x18, 0xb1b6109e
    cv.cmpge.b x19, x17, x18
    li x20, 0xffff00ff
    beq x20, x19, test20
    c.addi x15, 0x1
test20:
    li x17, 0xb498bfa6
    li x18, 0x21464685
    cv.cmpge.b x19, x17, x18
    li x20, 0x000000ff
    beq x20, x19, test21
    c.addi x15, 0x1
test21:
    li x17, 0x5685debb
    li x18, 0xd08564dd
    cv.cmpge.b x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test22
    c.addi x15, 0x1
test22:
    li x17, 0xf976f74a
    li x18, 0x5b0a5851
    cv.cmpge.b x19, x17, x18
    li x20, 0x00ff0000
    beq x20, x19, test23
    c.addi x15, 0x1
test23:
    li x17, 0x862d1de4
    li x18, 0xf6dbbb7f
    cv.cmpge.b x19, x17, x18
    li x20, 0x00ffff00
    beq x20, x19, test24
    c.addi x15, 0x1
test24:
    li x17, 0x10cf603d
    li x18, 0xd60cbf90
    cv.cmpge.b x19, x17, x18
    li x20, 0xff00ffff
    beq x20, x19, test25
    c.addi x15, 0x1
#tests25-30 test the cv.cmpge.sc.b instruction. values loaded in and compared to are expected output values
#cv.cmpge.sc.b is of the form "cv.cmpge.sc.b rD, rs1, rs2".
test25:
    li x17, 0x12a1418e
    li x18, 0x14377da7
    cv.cmpge.sc.b x19, x17, x18
    li x20, 0xff00ff00
    beq x20, x19, test26
    c.addi x15, 0x1
test26:
    li x17, 0x2f51b27f
    li x18, 0x75a5668a
    cv.cmpge.sc.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test27
    c.addi x15, 0x1
test27:
    li x17, 0x11ba732f
    li x18, 0x8a8aa473
    cv.cmpge.sc.b x19, x17, x18
    li x20, 0x0000ff00
    beq x20, x19, test28
    c.addi x15, 0x1
test28:
    li x17, 0x8b9b83df
    li x18, 0x50eb2209
    cv.cmpge.sc.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test29
    c.addi x15, 0x1
test29:
    li x17, 0xc953927f
    li x18, 0xd1a482f0
    cv.cmpge.sc.b x19, x17, x18
    li x20, 0x00ff00ff
    beq x20, x19, test30
    c.addi x15, 0x1
test30:
    li x17, 0x8c3d1013
    li x18, 0x0e77cd20
    cv.cmpge.sc.b x19, x17, x18
    li x20, 0x00ff0000
    beq x20, x19, test31
    c.addi x15, 0x1
#tests31-36 test the cv.cmpge.sci.b instruction. values loaded in and compared to are expected output values
#cv.cmpge.sci.b is of the form "cv.cmpge.sci.b rD, rs1, Imm6".
test31:
    li x17, 0x36c82041
    cv.cmpge.sci.b x19, x17, 0x9
    li x20, 0xff00ffff
    beq x20, x19, test32
    c.addi x15, 0x1
test32:
    li x17, 0xa3fdbe1d
    cv.cmpge.sci.b x19, x17, 0x5
    li x20, 0x000000ff
    beq x20, x19, test33
    c.addi x15, 0x1
test33:
    li x17, 0xa5fc0eae
    cv.cmpge.sci.b x19, x17, 0xe
    li x20, 0x0000ff00
    beq x20, x19, test34
    c.addi x15, 0x1
test34:
    li x17, 0x2f051a47
    cv.cmpge.sci.b x19, x17, 0x6
    li x20, 0xff00ffff
    beq x20, x19, test35
    c.addi x15, 0x1
test35:
    li x17, 0x6a9ea4f7
    cv.cmpge.sci.b x19, x17, 0xb
    li x20, 0xff000000
    beq x20, x19, test36
    c.addi x15, 0x1
test36:
    li x17, 0x082e6381
    cv.cmpge.sci.b x19, x17, 0x8
    li x20, 0xffffff00
    beq x20, x19, test37
    c.addi x15, 0x1
#tests37-42 test the cv.cmplt.h instruction. values loaded in and compared to are expected output values
#cv.cmplt.h is of the form "cv.cmplt.h rD, rs1, rs2".
test37:
    li x17, 0x209aee74
    li x18, 0xe74c4470
    cv.cmplt.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test38
    c.addi x15, 0x1
test38:
    li x17, 0x7c57f474
    li x18, 0xb0fbf474
    cv.cmplt.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test39
    c.addi x15, 0x1
test39:
    li x17, 0xc7bb3f49
    li x18, 0x151a4688
    cv.cmplt.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test40
    c.addi x15, 0x1
test40:
    li x17, 0x4aee84bc
    li x18, 0x2cb52f31
    cv.cmplt.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test41
    c.addi x15, 0x1
test41:
    li x17, 0x20d120b7
    li x18, 0x970a3f72
    cv.cmplt.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test42
    c.addi x15, 0x1
test42:
    li x17, 0x55de301a
    li x18, 0x37335977
    cv.cmplt.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test43
    c.addi x15, 0x1
#tests43-48 test the cv.cmplt.sc.h instruction. values loaded in and compared to are expected output values
#cv.cmplt.sc.h is of the form "cv.cmplt.sc.h rD, rs1, rs2".
test43:
    li x17, 0x02fea8b4
    li x18, 0x8c836759
    cv.cmplt.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test44
    c.addi x15, 0x1
test44:
    li x17, 0xa0121a95
    li x18, 0xd8d276f2
    cv.cmplt.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test45
    c.addi x15, 0x1
test45:
    li x17, 0xf57828b3
    li x18, 0xf0e5eabc
    cv.cmplt.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test46
    c.addi x15, 0x1
test46:
    li x17, 0xcd8c70c0
    li x18, 0x180d6dd0
    cv.cmplt.sc.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test47
    c.addi x15, 0x1
test47:
    li x17, 0x566494d3
    li x18, 0x56a15664
    cv.cmplt.sc.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test48
    c.addi x15, 0x1
test48:
    li x17, 0xf59e6750
    li x18, 0x55608171
    cv.cmplt.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test49
    c.addi x15, 0x1
#tests49-54 test the cv.cmplt.sci.h instruction. values loaded in and compared to are expected output values
#cv.cmplt.sci.h is of the form "cv.cmplt.sci.h rD, rs1, Imm6".
test49:
    li x17, 0xe3bb71e0
    cv.cmplt.sci.h x19, x17, 0x1
    li x20, 0xffff0000
    beq x20, x19, test50
    c.addi x15, 0x1
test50:
    li x17, 0x18bd3d5e
    cv.cmplt.sci.h x19, x17, 0x5
    li x20, 0x00000000
    beq x20, x19, test51
    c.addi x15, 0x1
test51:
    li x17, 0xb5dba974
    cv.cmplt.sci.h x19, x17, 0xe
    li x20, 0xffffffff
    beq x20, x19, test52
    c.addi x15, 0x1
test52:
    li x17, 0xfe1f5fea
    cv.cmplt.sci.h x19, x17, 0x0
    li x20, 0xffff0000
    beq x20, x19, test53
    c.addi x15, 0x1
test53:
    li x17, 0xb617000f
    cv.cmplt.sci.h x19, x17, 0xf
    li x20, 0xffff0000
    beq x20, x19, test54
    c.addi x15, 0x1
test54:
    li x17, 0xcd1c3b5d
    cv.cmplt.sci.h x19, x17, 0xb
    li x20, 0xffff0000
    beq x20, x19, test55
    c.addi x15, 0x1
#tests55-60 test the cv.cmplt.b instruction. values loaded in and compared to are expected output values
#cv.cmplt.b is of the form "cv.cmplt.b rD, rs1, rs2".
test55:
    li x17, 0x55860b34
    li x18, 0x9e62710f
    cv.cmplt.b x19, x17, x18
    li x20, 0x00ffff00
    beq x20, x19, test56
    c.addi x15, 0x1
test56:
    li x17, 0x25816a9b
    li x18, 0x389e40a6
    cv.cmplt.b x19, x17, x18
    li x20, 0xffff00ff
    beq x20, x19, test57
    c.addi x15, 0x1
test57:
    li x17, 0x7f116e8d
    li x18, 0x035e6e6a
    cv.cmplt.b x19, x17, x18
    li x20, 0x00ff00ff
    beq x20, x19, test58
    c.addi x15, 0x1
test58:
    li x17, 0x8607692a
    li x18, 0x02bb9691
    cv.cmplt.b x19, x17, x18
    li x20, 0xff000000
    beq x20, x19, test59
    c.addi x15, 0x1
test59:
    li x17, 0x0274fd96
    li x18, 0x3b1a5796
    cv.cmplt.b x19, x17, x18
    li x20, 0xff00ff00
    beq x20, x19, test60
    c.addi x15, 0x1
test60:
    li x17, 0xc7b81e1d
    li x18, 0xbb90c083
    cv.cmplt.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test61
    c.addi x15, 0x1
#tests61-66 test the cv.cmplt.sc.b instruction. values loaded in and compared to are expected output values
#cv.cmplt.sc.b is of the form "cv.cmplt.sc.b rD, rs1, rs2".
test61:
    li x17, 0x9b21bee4
    li x18, 0x6a840351
    cv.cmplt.sc.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test62
    c.addi x15, 0x1
test62:
    li x17, 0xbe78d503
    li x18, 0xf566036f
    cv.cmplt.sc.b x19, x17, x18
    li x20, 0xff00ffff
    beq x20, x19, test63
    c.addi x15, 0x1
test63:
    li x17, 0x1df6174c
    li x18, 0xcd4e480f
    cv.cmplt.sc.b x19, x17, x18
    li x20, 0x00ff0000
    beq x20, x19, test64
    c.addi x15, 0x1
test64:
    li x17, 0xc7f92f5c
    li x18, 0x2dc395c7
    cv.cmplt.sc.b x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test65
    c.addi x15, 0x1
test65:
    li x17, 0xd09a1ad6
    li x18, 0x154996f7
    cv.cmplt.sc.b x19, x17, x18
    li x20, 0xffff00ff
    beq x20, x19, test66
    c.addi x15, 0x1
test66:
    li x17, 0x9780e2e1
    li x18, 0x7c942c83
    cv.cmplt.sc.b x19, x17, x18
    li x20, 0x00ff0000
    beq x20, x19, test67
    c.addi x15, 0x1
#tests67-72 test the cv.cmplt.sci.b instruction. values loaded in and compared to are expected output values
#cv.cmplt.sci.b is of the form "cv.cmplt.sci.b rD, rs1, Imm6".
test67:
    li x17, 0x66984600
    cv.cmplt.sci.b x19, x17, 0x0
    li x20, 0x00ff0000
    beq x20, x19, test68
    c.addi x15, 0x1
test68:
    li x17, 0x29ba7f23
    cv.cmplt.sci.b x19, x17, 0x3
    li x20, 0x00ff0000
    beq x20, x19, test69
    c.addi x15, 0x1
test69:
    li x17, 0x93ab8222
    cv.cmplt.sci.b x19, x17, 0xa
    li x20, 0xffffff00
    beq x20, x19, test70
    c.addi x15, 0x1
test70:
    li x17, 0x6576ff07
    cv.cmplt.sci.b x19, x17, 0x8
    li x20, 0x0000ffff
    beq x20, x19, test71
    c.addi x15, 0x1
test71:
    li x17, 0xb6702fc3
    cv.cmplt.sci.b x19, x17, 0x7
    li x20, 0xff0000ff
    beq x20, x19, test72
    c.addi x15, 0x1
test72:
    li x17, 0x2ff37bf7
    cv.cmplt.sci.b x19, x17, 0xf
    li x20, 0x00ff00ff
    beq x20, x19, test73
    c.addi x15, 0x1
#tests73-78 test the cv.cmple.h instruction. values loaded in and compared to are expected output values
#cv.cmple.h is of the form "cv.cmple.h rD, rs1, rs2".
test73:
    li x17, 0x003bfd58
    li x18, 0x640e2058
    cv.cmple.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test74
    c.addi x15, 0x1
test74:
    li x17, 0x6d220310
    li x18, 0xf6e052f6
    cv.cmple.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test75
    c.addi x15, 0x1
test75:
    li x17, 0x8e1319b6
    li x18, 0x1009037d
    cv.cmple.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test76
    c.addi x15, 0x1
test76:
    li x17, 0x67cd3e5b
    li x18, 0x9a11e8d0
    cv.cmple.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test77
    c.addi x15, 0x1
test77:
    li x17, 0x87ef53ca
    li x18, 0x87efda70
    cv.cmple.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test78
    c.addi x15, 0x1
test78:
    li x17, 0xad4a994c
    li x18, 0xbd8a6c9f
    cv.cmple.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test79
    c.addi x15, 0x1
#tests79-84 test the cv.cmple.sc.h instruction. values loaded in and compared to are expected output values
#cv.cmple.sc.h is of the form "cv.cmple.sc.h rD, rs1, rs2".
test79:
    li x17, 0xb0153c6a
    li x18, 0x17517676
    cv.cmple.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test80
    c.addi x15, 0x1
test80:
    li x17, 0x5f2707ee
    li x18, 0x8164df16
    cv.cmple.sc.h x19, x17, x18
    li x20, 0x00000000
    beq x20, x19, test81
    c.addi x15, 0x1
test81:
    li x17, 0x1c449936
    li x18, 0x26f9059b
    cv.cmple.sc.h x19, x17, x18
    li x20, 0x0000ffff
    beq x20, x19, test82
    c.addi x15, 0x1
test82:
    li x17, 0x82408f8b
    li x18, 0x786cc6e2
    cv.cmple.sc.h x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test83
    c.addi x15, 0x1
test83:
    li x17, 0xaa7a3d5e
    li x18, 0xd11a1b76
    cv.cmple.sc.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test84
    c.addi x15, 0x1
test84:
    li x17, 0xe1a3fa81
    li x18, 0x4332e1a3
    cv.cmple.sc.h x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test85
    c.addi x15, 0x1
#tests85-90 test the cv.cmple.sci.h instruction. values loaded in and compared to are expected output values
#cv.cmple.sci.h is of the form "cv.cmple.sci.h rD, rs1, Imm6".
test85:
    li x17, 0x35b84a12
    cv.cmple.sci.h x19, x17, 0xd
    li x20, 0x00000000
    beq x20, x19, test86
    c.addi x15, 0x1
test86:
    li x17, 0x209d000c
    cv.cmple.sci.h x19, x17, 0xc
    li x20, 0x0000ffff
    beq x20, x19, test87
    c.addi x15, 0x1
test87:
    li x17, 0x0004bf7b
    cv.cmple.sci.h x19, x17, 0x4
    li x20, 0xffffffff
    beq x20, x19, test88
    c.addi x15, 0x1
test88:
    li x17, 0x8726fec2
    cv.cmple.sci.h x19, x17, 0xf
    li x20, 0xffffffff
    beq x20, x19, test89
    c.addi x15, 0x1
test89:
    li x17, 0x407ab95e
    cv.cmple.sci.h x19, x17, 0x8
    li x20, 0x0000ffff
    beq x20, x19, test90
    c.addi x15, 0x1
test90:
    li x17, 0xa05e6fe2
    cv.cmple.sci.h x19, x17, 0xa
    li x20, 0xffff0000
    beq x20, x19, test91
    c.addi x15, 0x1
#tests91-96 test the cv.cmple.b instruction. values loaded in and compared to are expected output values
#cv.cmple.b is of the form "cv.cmple.b rD, rs1, rs2".
test91:
    li x17, 0x92b4c136
    li x18, 0xa6b4282c
    cv.cmple.b x19, x17, x18
    li x20, 0xffffff00
    beq x20, x19, test92
    c.addi x15, 0x1
test92:
    li x17, 0x029ec3d0
    li x18, 0xab0341e5
    cv.cmple.b x19, x17, x18
    li x20, 0x00ffffff
    beq x20, x19, test93
    c.addi x15, 0x1
test93:
    li x17, 0xdec66ef7
    li x18, 0x1c914d93
    cv.cmple.b x19, x17, x18
    li x20, 0xff000000
    beq x20, x19, test94
    c.addi x15, 0x1
test94:
    li x17, 0xc2c21e78
    li x18, 0x6addfa51
    cv.cmple.b x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test95
    c.addi x15, 0x1
test95:
    li x17, 0x58fa4b8c
    li x18, 0xc0c59646
    cv.cmple.b x19, x17, x18
    li x20, 0x000000ff
    beq x20, x19, test96
    c.addi x15, 0x1
test96:
    li x17, 0xcc7cf13a
    li x18, 0x4ce50a42
    cv.cmple.b x19, x17, x18
    li x20, 0xff00ffff
    beq x20, x19, test97
    c.addi x15, 0x1
#tests97-102 test the cv.cmple.sc.b instruction. values loaded in and compared to are expected output values
#cv.cmple.sc.b is of the form "cv.cmple.sc.b rD, rs1, rs2".
test97:
    li x17, 0x0504db6f
    li x18, 0x698c684f
    cv.cmple.sc.b x19, x17, x18
    li x20, 0xffffff00
    beq x20, x19, test98
    c.addi x15, 0x1
test98:
    li x17, 0x09238516
    li x18, 0xde85a2d3
    cv.cmple.sc.b x19, x17, x18
    li x20, 0x0000ff00
    beq x20, x19, test99
    c.addi x15, 0x1
test99:
    li x17, 0xd0a51442
    li x18, 0xa72181d0
    cv.cmple.sc.b x19, x17, x18
    li x20, 0xffff0000
    beq x20, x19, test100
    c.addi x15, 0x1
test100:
    li x17, 0x80f06357
    li x18, 0xd3b54968
    cv.cmple.sc.b x19, x17, x18
    li x20, 0xffffffff
    beq x20, x19, test101
    c.addi x15, 0x1
test101:
    li x17, 0x697390f0
    li x18, 0x0d4163d9
    cv.cmple.sc.b x19, x17, x18
    li x20, 0x0000ff00
    beq x20, x19, test102
    c.addi x15, 0x1
test102:
    li x17, 0xa89d9f78
    li x18, 0xa2005459
    cv.cmple.sc.b x19, x17, x18
    li x20, 0xffffff00
    beq x20, x19, test103
    c.addi x15, 0x1
#tests103-108 test the cv.cmple.sci.b instruction. values loaded in and compared to are expected output values
#cv.cmple.sci.b is of the form "cv.cmple.sci.b rD, rs1, Imm6".
test103:
    li x17, 0xcde20efa
    cv.cmple.sci.b x19, x17, 0xe
    li x20, 0xffffffff
    beq x20, x19, test104
    c.addi x15, 0x1
test104:
    li x17, 0xc65d0bb6
    cv.cmple.sci.b x19, x17, 0xc
    li x20, 0xff00ffff
    beq x20, x19, test105
    c.addi x15, 0x1
test105:
    li x17, 0x25177826
    cv.cmple.sci.b x19, x17, 0x2
    li x20, 0x00000000
    beq x20, x19, test106
    c.addi x15, 0x1
test106:
    li x17, 0x5021f615
    cv.cmple.sci.b x19, x17, 0x7
    li x20, 0x0000ff00
    beq x20, x19, test107
    c.addi x15, 0x1
test107:
    li x17, 0xbf701751
    cv.cmple.sci.b x19, x17, 0x4
    li x20, 0xff000000
    beq x20, x19, test108
    c.addi x15, 0x1
test108:
    li x17, 0x6693f223
    cv.cmple.sci.b x19, x17, 0x0
    li x20, 0x00ffff00
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
