# Copyright (c) 2024 Dolphin Design
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.globl _start
.globl main
.globl exit
.section .text

#define TEST_PASS                      123456789
#define TEST_FAIL                              1
#define VIRT_PERIPH_STATUS_FLAG_ADDR  0x20000000

main:
    li        t0, (0x0 << 3)
    csrs      mstatus, t0
    li        x31, 0x0

#if defined(FPU)
    li x5, 0x00003800
    csrw 0x300, x5 # MSTATUS FPU enable
#endif

    ######### FOR PULP_FPU CFG - START #########
      # for uvme_cv32e40p_fp_instr_covg/cg_f_inst_reg/cr_non_rv32f_rd_rv32f_rs1 - start
        .align 2

        // 1 - jal -> fsub (rs1, rs2)
        jal	x0, _fsub_j0
_fsub_j0:    fsub.s      x0, x0, x0
        jal	x1, _fsub_j1
_fsub_j1:    fsub.s      x1, x1, x1
        jal	x2, _fsub_j2
_fsub_j2:    fsub.s      x2, x2, x2
        jal	x3, _fsub_j3
_fsub_j3:    fsub.s      x3, x3, x3
        jal	x4, _fsub_j4
_fsub_j4:    fsub.s      x4, x4, x4
        jal	x5, _fsub_j5
_fsub_j5:    fsub.s      x5, x5, x5
        jal	x6, _fsub_j6
_fsub_j6:    fsub.s      x6, x6, x6
        jal	x7, _fsub_j7
_fsub_j7:    fsub.s      x7, x7, x7
        jal	x8, _fsub_j8
_fsub_j8:    fsub.s      x8, x8, x8
        jal	x9, _fsub_j9
_fsub_j9:    fsub.s      x9, x9, x9
        jal	x10, _fsub_j10
_fsub_j10:    fsub.s      x10, x10, x10
        jal	x11, _fsub_j11
_fsub_j11:    fsub.s      x11, x11, x11
        jal	x12, _fsub_j12
_fsub_j12:    fsub.s      x12, x12, x12
        jal	x13, _fsub_j13
_fsub_j13:    fsub.s      x13, x13, x13
        jal	x14, _fsub_j14
_fsub_j14:    fsub.s      x14, x14, x14
        jal	x15, _fsub_j15
_fsub_j15:    fsub.s      x15, x15, x15
        jal	x16, _fsub_j16
_fsub_j16:    fsub.s      x16, x16, x16
        jal	x17, _fsub_j17
_fsub_j17:    fsub.s      x17, x17, x17
        jal	x18, _fsub_j18
_fsub_j18:    fsub.s      x18, x18, x18
        jal	x19, _fsub_j19
_fsub_j19:    fsub.s      x19, x19, x19
        jal	x20, _fsub_j20
_fsub_j20:    fsub.s      x20, x20, x20
        jal	x21, _fsub_j21
_fsub_j21:    fsub.s      x21, x21, x21
        jal	x22, _fsub_j22
_fsub_j22:    fsub.s      x22, x22, x22
        jal	x23, _fsub_j23
_fsub_j23:    fsub.s      x23, x23, x23
        jal	x24, _fsub_j24
_fsub_j24:    fsub.s      x24, x24, x24
        jal	x25, _fsub_j25
_fsub_j25:    fsub.s      x25, x25, x25
        jal	x26, _fsub_j26
_fsub_j26:    fsub.s      x26, x26, x26
        jal	x27, _fsub_j27
_fsub_j27:    fsub.s      x27, x27, x27
        jal	x28, _fsub_j28
_fsub_j28:    fsub.s      x28, x28, x28
        jal	x29, _fsub_j29
_fsub_j29:    fsub.s      x29, x29, x29
        jal	x30, _fsub_j30
_fsub_j30:    fsub.s      x30, x30, x30
        jal	x31, _fsub_j31
_fsub_j31:    fsub.s      x31, x31, x31

        // 2 - jalr -> fsub (rs1, rs2)
        la x1, _fsub_jr0
        jalr	x0, x1, 0
_fsub_jr0:   fsub.s      x0, x0, x0
        la x1, _fsub_jr1
        jalr	x1, x1, 0
_fsub_jr1:   fsub.s      x1, x1, x1
        la x1, _fsub_jr2
        jalr	x2, x1, 0
_fsub_jr2:   fsub.s      x2, x2, x2
        la x1, _fsub_jr3
        jalr	x3, x1, 0
_fsub_jr3:   fsub.s      x3, x3, x3
        la x1, _fsub_jr4
        jalr	x4, x1, 0
_fsub_jr4:   fsub.s      x4, x4, x4
        la x1, _fsub_jr5
        jalr	x5, x1, 0
_fsub_jr5:   fsub.s      x5, x5, x5
        la x1, _fsub_jr6
        jalr	x6, x1, 0
_fsub_jr6:   fsub.s      x6, x6, x6
        la x1, _fsub_jr7
        jalr	x7, x1, 0
_fsub_jr7:   fsub.s      x7, x7, x7
        la x1, _fsub_jr8
        jalr	x8, x1, 0
_fsub_jr8:   fsub.s      x8, x8, x8
        la x1, _fsub_jr9
        jalr	x9, x1, 0
_fsub_jr9:   fsub.s      x9, x9, x9
        la x1, _fsub_jr10
        jalr	x10, x1, 0
_fsub_jr10:   fsub.s      x10, x10, x10
        la x1, _fsub_jr11
        jalr	x11, x1, 0
_fsub_jr11:   fsub.s      x11, x11, x11
        la x1, _fsub_jr12
        jalr	x12, x1, 0
_fsub_jr12:   fsub.s      x12, x12, x12
        la x1, _fsub_jr13
        jalr	x13, x1, 0
_fsub_jr13:   fsub.s      x13, x13, x13
        la x1, _fsub_jr14
        jalr	x14, x1, 0
_fsub_jr14:   fsub.s      x14, x14, x14
        la x1, _fsub_jr15
        jalr	x15, x1, 0
_fsub_jr15:   fsub.s      x15, x15, x15
        la x1, _fsub_jr16
        jalr	x16, x1, 0
_fsub_jr16:   fsub.s      x16, x16, x16
        la x1, _fsub_jr17
        jalr	x17, x1, 0
_fsub_jr17:   fsub.s      x17, x17, x17
        la x1, _fsub_jr18
        jalr	x18, x1, 0
_fsub_jr18:   fsub.s      x18, x18, x18
        la x1, _fsub_jr19
        jalr	x19, x1, 0
_fsub_jr19:   fsub.s      x19, x19, x19
        la x1, _fsub_jr20
        jalr	x20, x1, 0
_fsub_jr20:   fsub.s      x20, x20, x20
        la x1, _fsub_jr21
        jalr	x21, x1, 0
_fsub_jr21:   fsub.s      x21, x21, x21
        la x1, _fsub_jr22
        jalr	x22, x1, 0
_fsub_jr22:   fsub.s      x22, x22, x22
        la x1, _fsub_jr23
        jalr	x23, x1, 0
_fsub_jr23:   fsub.s      x23, x23, x23
        la x1, _fsub_jr24
        jalr	x24, x1, 0
_fsub_jr24:   fsub.s      x24, x24, x24
        la x1, _fsub_jr25
        jalr	x25, x1, 0
_fsub_jr25:   fsub.s      x25, x25, x25
        la x1, _fsub_jr26
        jalr	x26, x1, 0
_fsub_jr26:   fsub.s      x26, x26, x26
        la x1, _fsub_jr27
        jalr	x27, x1, 0
_fsub_jr27:   fsub.s      x27, x27, x27
        la x1, _fsub_jr28
        jalr	x28, x1, 0
_fsub_jr28:   fsub.s      x28, x28, x28
        la x1, _fsub_jr29
        jalr	x29, x1, 0
_fsub_jr29:   fsub.s      x29, x29, x29
        la x1, _fsub_jr30
        jalr	x30, x1, 0
_fsub_jr30:   fsub.s      x30, x30, x30
        la x1, _fsub_jr31
        jalr	x31, x1, 0
_fsub_jr31:   fsub.s      x31, x31, x31

        // 3 - jal -> fsqrt (rs1)
        jal	x0, _fsqrt_j0
_fsqrt_j0:    fsqrt.s      x0, x0
        jal	x1, _fsqrt_j1
_fsqrt_j1:    fsqrt.s      x1, x1
        jal	x2, _fsqrt_j2
_fsqrt_j2:    fsqrt.s      x2, x2
        jal	x3, _fsqrt_j3
_fsqrt_j3:    fsqrt.s      x3, x3
        jal	x4, _fsqrt_j4
_fsqrt_j4:    fsqrt.s      x4, x4
        jal	x5, _fsqrt_j5
_fsqrt_j5:    fsqrt.s      x5, x5
        jal	x6, _fsqrt_j6
_fsqrt_j6:    fsqrt.s      x6, x6
        jal	x7, _fsqrt_j7
_fsqrt_j7:    fsqrt.s      x7, x7
        jal	x8, _fsqrt_j8
_fsqrt_j8:    fsqrt.s      x8, x8
        jal	x9, _fsqrt_j9
_fsqrt_j9:    fsqrt.s      x9, x9
        jal	x10, _fsqrt_j10
_fsqrt_j10:    fsqrt.s      x10, x10
        jal	x11, _fsqrt_j11
_fsqrt_j11:    fsqrt.s      x11, x11
        jal	x12, _fsqrt_j12
_fsqrt_j12:    fsqrt.s      x12, x12
        jal	x13, _fsqrt_j13
_fsqrt_j13:    fsqrt.s      x13, x13
        jal	x14, _fsqrt_j14
_fsqrt_j14:    fsqrt.s      x14, x14
        jal	x15, _fsqrt_j15
_fsqrt_j15:    fsqrt.s      x15, x15
        jal	x16, _fsqrt_j16
_fsqrt_j16:    fsqrt.s      x16, x16
        jal	x17, _fsqrt_j17
_fsqrt_j17:    fsqrt.s      x17, x17
        jal	x18, _fsqrt_j18
_fsqrt_j18:    fsqrt.s      x18, x18
        jal	x19, _fsqrt_j19
_fsqrt_j19:    fsqrt.s      x19, x19
        jal	x20, _fsqrt_j20
_fsqrt_j20:    fsqrt.s      x20, x20
        jal	x21, _fsqrt_j21
_fsqrt_j21:    fsqrt.s      x21, x21
        jal	x22, _fsqrt_j22
_fsqrt_j22:    fsqrt.s      x22, x22
        jal	x23, _fsqrt_j23
_fsqrt_j23:    fsqrt.s      x23, x23
        jal	x24, _fsqrt_j24
_fsqrt_j24:    fsqrt.s      x24, x24
        jal	x25, _fsqrt_j25
_fsqrt_j25:    fsqrt.s      x25, x25
        jal	x26, _fsqrt_j26
_fsqrt_j26:    fsqrt.s      x26, x26
        jal	x27, _fsqrt_j27
_fsqrt_j27:    fsqrt.s      x27, x27
        jal	x28, _fsqrt_j28
_fsqrt_j28:    fsqrt.s      x28, x28
        jal	x29, _fsqrt_j29
_fsqrt_j29:    fsqrt.s      x29, x29
        jal	x30, _fsqrt_j30
_fsqrt_j30:    fsqrt.s      x30, x30
        jal	x31, _fsqrt_j31
_fsqrt_j31:    fsqrt.s      x31, x31

        // 4 - jalr -> fsqrt (rs1, rs2)
        la x1, _fsqrt_jr0
        jalr	x0, x1, 0
_fsqrt_jr0:   fsqrt.s      x0, x0
        la x1, _fsqrt_jr1
        jalr	x1, x1, 0
_fsqrt_jr1:   fsqrt.s      x1, x1
        la x1, _fsqrt_jr2
        jalr	x2, x1, 0
_fsqrt_jr2:   fsqrt.s      x2, x2
        la x1, _fsqrt_jr3
        jalr	x3, x1, 0
_fsqrt_jr3:   fsqrt.s      x3, x3
        la x1, _fsqrt_jr4
        jalr	x4, x1, 0
_fsqrt_jr4:   fsqrt.s      x4, x4
        la x1, _fsqrt_jr5
        jalr	x5, x1, 0
_fsqrt_jr5:   fsqrt.s      x5, x5
        la x1, _fsqrt_jr6
        jalr	x6, x1, 0
_fsqrt_jr6:   fsqrt.s      x6, x6
        la x1, _fsqrt_jr7
        jalr	x7, x1, 0
_fsqrt_jr7:   fsqrt.s      x7, x7
        la x1, _fsqrt_jr8
        jalr	x8, x1, 0
_fsqrt_jr8:   fsqrt.s      x8, x8
        la x1, _fsqrt_jr9
        jalr	x9, x1, 0
_fsqrt_jr9:   fsqrt.s      x9, x9
        la x1, _fsqrt_jr10
        jalr	x10, x1, 0
_fsqrt_jr10:   fsqrt.s      x10, x10
        la x1, _fsqrt_jr11
        jalr	x11, x1, 0
_fsqrt_jr11:   fsqrt.s      x11, x11
        la x1, _fsqrt_jr12
        jalr	x12, x1, 0
_fsqrt_jr12:   fsqrt.s      x12, x12
        la x1, _fsqrt_jr13
        jalr	x13, x1, 0
_fsqrt_jr13:   fsqrt.s      x13, x13
        la x1, _fsqrt_jr14
        jalr	x14, x1, 0
_fsqrt_jr14:   fsqrt.s      x14, x14
        la x1, _fsqrt_jr15
        jalr	x15, x1, 0
_fsqrt_jr15:   fsqrt.s      x15, x15
        la x1, _fsqrt_jr16
        jalr	x16, x1, 0
_fsqrt_jr16:   fsqrt.s      x16, x16
        la x1, _fsqrt_jr17
        jalr	x17, x1, 0
_fsqrt_jr17:   fsqrt.s      x17, x17
        la x1, _fsqrt_jr18
        jalr	x18, x1, 0
_fsqrt_jr18:   fsqrt.s      x18, x18
        la x1, _fsqrt_jr19
        jalr	x19, x1, 0
_fsqrt_jr19:   fsqrt.s      x19, x19
        la x1, _fsqrt_jr20
        jalr	x20, x1, 0
_fsqrt_jr20:   fsqrt.s      x20, x20
        la x1, _fsqrt_jr21
        jalr	x21, x1, 0
_fsqrt_jr21:   fsqrt.s      x21, x21
        la x1, _fsqrt_jr22
        jalr	x22, x1, 0
_fsqrt_jr22:   fsqrt.s      x22, x22
        la x1, _fsqrt_jr23
        jalr	x23, x1, 0
_fsqrt_jr23:   fsqrt.s      x23, x23
        la x1, _fsqrt_jr24
        jalr	x24, x1, 0
_fsqrt_jr24:   fsqrt.s      x24, x24
        la x1, _fsqrt_jr25
        jalr	x25, x1, 0
_fsqrt_jr25:   fsqrt.s      x25, x25
        la x1, _fsqrt_jr26
        jalr	x26, x1, 0
_fsqrt_jr26:   fsqrt.s      x26, x26
        la x1, _fsqrt_jr27
        jalr	x27, x1, 0
_fsqrt_jr27:   fsqrt.s      x27, x27
        la x1, _fsqrt_jr28
        jalr	x28, x1, 0
_fsqrt_jr28:   fsqrt.s      x28, x28
        la x1, _fsqrt_jr29
        jalr	x29, x1, 0
_fsqrt_jr29:   fsqrt.s      x29, x29
        la x1, _fsqrt_jr30
        jalr	x30, x1, 0
_fsqrt_jr30:   fsqrt.s      x30, x30
        la x1, _fsqrt_jr31
        jalr	x31, x1, 0
_fsqrt_jr31:   fsqrt.s      x31, x31

        // 5 - jal -> fadd (rs1, rs2)
        jal	x0, _fadd_j0
_fadd_j0:    fadd.s      x0, x0, x0
        jal	x1, _fadd_j1
_fadd_j1:    fadd.s      x1, x1, x1
        jal	x2, _fadd_j2
_fadd_j2:    fadd.s      x2, x2, x2
        jal	x3, _fadd_j3
_fadd_j3:    fadd.s      x3, x3, x3
        jal	x4, _fadd_j4
_fadd_j4:    fadd.s      x4, x4, x4
        jal	x5, _fadd_j5
_fadd_j5:    fadd.s      x5, x5, x5
        jal	x6, _fadd_j6
_fadd_j6:    fadd.s      x6, x6, x6
        jal	x7, _fadd_j7
_fadd_j7:    fadd.s      x7, x7, x7
        jal	x8, _fadd_j8
_fadd_j8:    fadd.s      x8, x8, x8
        jal	x9, _fadd_j9
_fadd_j9:    fadd.s      x9, x9, x9
        jal	x10, _fadd_j10
_fadd_j10:    fadd.s      x10, x10, x10
        jal	x11, _fadd_j11
_fadd_j11:    fadd.s      x11, x11, x11
        jal	x12, _fadd_j12
_fadd_j12:    fadd.s      x12, x12, x12
        jal	x13, _fadd_j13
_fadd_j13:    fadd.s      x13, x13, x13
        jal	x14, _fadd_j14
_fadd_j14:    fadd.s      x14, x14, x14
        jal	x15, _fadd_j15
_fadd_j15:    fadd.s      x15, x15, x15
        jal	x16, _fadd_j16
_fadd_j16:    fadd.s      x16, x16, x16
        jal	x17, _fadd_j17
_fadd_j17:    fadd.s      x17, x17, x17
        jal	x18, _fadd_j18
_fadd_j18:    fadd.s      x18, x18, x18
        jal	x19, _fadd_j19
_fadd_j19:    fadd.s      x19, x19, x19
        jal	x20, _fadd_j20
_fadd_j20:    fadd.s      x20, x20, x20
        jal	x21, _fadd_j21
_fadd_j21:    fadd.s      x21, x21, x21
        jal	x22, _fadd_j22
_fadd_j22:    fadd.s      x22, x22, x22
        jal	x23, _fadd_j23
_fadd_j23:    fadd.s      x23, x23, x23
        jal	x24, _fadd_j24
_fadd_j24:    fadd.s      x24, x24, x24
        jal	x25, _fadd_j25
_fadd_j25:    fadd.s      x25, x25, x25
        jal	x26, _fadd_j26
_fadd_j26:    fadd.s      x26, x26, x26
        jal	x27, _fadd_j27
_fadd_j27:    fadd.s      x27, x27, x27
        jal	x28, _fadd_j28
_fadd_j28:    fadd.s      x28, x28, x28
        jal	x29, _fadd_j29
_fadd_j29:    fadd.s      x29, x29, x29
        jal	x30, _fadd_j30
_fadd_j30:    fadd.s      x30, x30, x30
        jal	x31, _fadd_j31
_fadd_j31:    fadd.s      x31, x31, x31

        // 6 - jalr -> fadd (rs1, rs2)
        la x1, _fadd_jr0
        jalr	x0, x1, 0
_fadd_jr0:   fadd.s      x0, x0, x0
        la x1, _fadd_jr1
        jalr	x1, x1, 0
_fadd_jr1:   fadd.s      x1, x1, x1
        la x1, _fadd_jr2
        jalr	x2, x1, 0
_fadd_jr2:   fadd.s      x2, x2, x2
        la x1, _fadd_jr3
        jalr	x3, x1, 0
_fadd_jr3:   fadd.s      x3, x3, x3
        la x1, _fadd_jr4
        jalr	x4, x1, 0
_fadd_jr4:   fadd.s      x4, x4, x4
        la x1, _fadd_jr5
        jalr	x5, x1, 0
_fadd_jr5:   fadd.s      x5, x5, x5
        la x1, _fadd_jr6
        jalr	x6, x1, 0
_fadd_jr6:   fadd.s      x6, x6, x6
        la x1, _fadd_jr7
        jalr	x7, x1, 0
_fadd_jr7:   fadd.s      x7, x7, x7
        la x1, _fadd_jr8
        jalr	x8, x1, 0
_fadd_jr8:   fadd.s      x8, x8, x8
        la x1, _fadd_jr9
        jalr	x9, x1, 0
_fadd_jr9:   fadd.s      x9, x9, x9
        la x1, _fadd_jr10
        jalr	x10, x1, 0
_fadd_jr10:   fadd.s      x10, x10, x10
        la x1, _fadd_jr11
        jalr	x11, x1, 0
_fadd_jr11:   fadd.s      x11, x11, x11
        la x1, _fadd_jr12
        jalr	x12, x1, 0
_fadd_jr12:   fadd.s      x12, x12, x12
        la x1, _fadd_jr13
        jalr	x13, x1, 0
_fadd_jr13:   fadd.s      x13, x13, x13
        la x1, _fadd_jr14
        jalr	x14, x1, 0
_fadd_jr14:   fadd.s      x14, x14, x14
        la x1, _fadd_jr15
        jalr	x15, x1, 0
_fadd_jr15:   fadd.s      x15, x15, x15
        la x1, _fadd_jr16
        jalr	x16, x1, 0
_fadd_jr16:   fadd.s      x16, x16, x16
        la x1, _fadd_jr17
        jalr	x17, x1, 0
_fadd_jr17:   fadd.s      x17, x17, x17
        la x1, _fadd_jr18
        jalr	x18, x1, 0
_fadd_jr18:   fadd.s      x18, x18, x18
        la x1, _fadd_jr19
        jalr	x19, x1, 0
_fadd_jr19:   fadd.s      x19, x19, x19
        la x1, _fadd_jr20
        jalr	x20, x1, 0
_fadd_jr20:   fadd.s      x20, x20, x20
        la x1, _fadd_jr21
        jalr	x21, x1, 0
_fadd_jr21:   fadd.s      x21, x21, x21
        la x1, _fadd_jr22
        jalr	x22, x1, 0
_fadd_jr22:   fadd.s      x22, x22, x22
        la x1, _fadd_jr23
        jalr	x23, x1, 0
_fadd_jr23:   fadd.s      x23, x23, x23
        la x1, _fadd_jr24
        jalr	x24, x1, 0
_fadd_jr24:   fadd.s      x24, x24, x24
        la x1, _fadd_jr25
        jalr	x25, x1, 0
_fadd_jr25:   fadd.s      x25, x25, x25
        la x1, _fadd_jr26
        jalr	x26, x1, 0
_fadd_jr26:   fadd.s      x26, x26, x26
        la x1, _fadd_jr27
        jalr	x27, x1, 0
_fadd_jr27:   fadd.s      x27, x27, x27
        la x1, _fadd_jr28
        jalr	x28, x1, 0
_fadd_jr28:   fadd.s      x28, x28, x28
        la x1, _fadd_jr29
        jalr	x29, x1, 0
_fadd_jr29:   fadd.s      x29, x29, x29
        la x1, _fadd_jr30
        jalr	x30, x1, 0
_fadd_jr30:   fadd.s      x30, x30, x30
        la x1, _fadd_jr31
        jalr	x31, x1, 0
_fadd_jr31:   fadd.s      x31, x31, x31

        // 7 - jal -> fclass (rs1)
        jal	x0, _fclass_j0
_fclass_j0:    fclass.s      x0, x0
        jal	x1, _fclass_j1
_fclass_j1:    fclass.s      x1, x1
        jal	x2, _fclass_j2
_fclass_j2:    fclass.s      x2, x2
        jal	x3, _fclass_j3
_fclass_j3:    fclass.s      x3, x3
        jal	x4, _fclass_j4
_fclass_j4:    fclass.s      x4, x4
        jal	x5, _fclass_j5
_fclass_j5:    fclass.s      x5, x5
        jal	x6, _fclass_j6
_fclass_j6:    fclass.s      x6, x6
        jal	x7, _fclass_j7
_fclass_j7:    fclass.s      x7, x7
        jal	x8, _fclass_j8
_fclass_j8:    fclass.s      x8, x8
        jal	x9, _fclass_j9
_fclass_j9:    fclass.s      x9, x9
        jal	x10, _fclass_j10
_fclass_j10:    fclass.s      x10, x10
        jal	x11, _fclass_j11
_fclass_j11:    fclass.s      x11, x11
        jal	x12, _fclass_j12
_fclass_j12:    fclass.s      x12, x12
        jal	x13, _fclass_j13
_fclass_j13:    fclass.s      x13, x13
        jal	x14, _fclass_j14
_fclass_j14:    fclass.s      x14, x14
        jal	x15, _fclass_j15
_fclass_j15:    fclass.s      x15, x15
        jal	x16, _fclass_j16
_fclass_j16:    fclass.s      x16, x16
        jal	x17, _fclass_j17
_fclass_j17:    fclass.s      x17, x17
        jal	x18, _fclass_j18
_fclass_j18:    fclass.s      x18, x18
        jal	x19, _fclass_j19
_fclass_j19:    fclass.s      x19, x19
        jal	x20, _fclass_j20
_fclass_j20:    fclass.s      x20, x20
        jal	x21, _fclass_j21
_fclass_j21:    fclass.s      x21, x21
        jal	x22, _fclass_j22
_fclass_j22:    fclass.s      x22, x22
        jal	x23, _fclass_j23
_fclass_j23:    fclass.s      x23, x23
        jal	x24, _fclass_j24
_fclass_j24:    fclass.s      x24, x24
        jal	x25, _fclass_j25
_fclass_j25:    fclass.s      x25, x25
        jal	x26, _fclass_j26
_fclass_j26:    fclass.s      x26, x26
        jal	x27, _fclass_j27
_fclass_j27:    fclass.s      x27, x27
        jal	x28, _fclass_j28
_fclass_j28:    fclass.s      x28, x28
        jal	x29, _fclass_j29
_fclass_j29:    fclass.s      x29, x29
        jal	x30, _fclass_j30
_fclass_j30:    fclass.s      x30, x30
        jal	x31, _fclass_j31
_fclass_j31:    fclass.s      x31, x31

        // 8 - jalr -> fclass (rs1)
        la x1, _fclass_jr0
        jalr	x0, x1, 0
_fclass_jr0:   fclass.s      x0, x0
        la x1, _fclass_jr1
        jalr	x1, x1, 0
_fclass_jr1:   fclass.s      x1, x1
        la x1, _fclass_jr2
        jalr	x2, x1, 0
_fclass_jr2:   fclass.s      x2, x2
        la x1, _fclass_jr3
        jalr	x3, x1, 0
_fclass_jr3:   fclass.s      x3, x3
        la x1, _fclass_jr4
        jalr	x4, x1, 0
_fclass_jr4:   fclass.s      x4, x4
        la x1, _fclass_jr5
        jalr	x5, x1, 0
_fclass_jr5:   fclass.s      x5, x5
        la x1, _fclass_jr6
        jalr	x6, x1, 0
_fclass_jr6:   fclass.s      x6, x6
        la x1, _fclass_jr7
        jalr	x7, x1, 0
_fclass_jr7:   fclass.s      x7, x7
        la x1, _fclass_jr8
        jalr	x8, x1, 0
_fclass_jr8:   fclass.s      x8, x8
        la x1, _fclass_jr9
        jalr	x9, x1, 0
_fclass_jr9:   fclass.s      x9, x9
        la x1, _fclass_jr10
        jalr	x10, x1, 0
_fclass_jr10:   fclass.s      x10, x10
        la x1, _fclass_jr11
        jalr	x11, x1, 0
_fclass_jr11:   fclass.s      x11, x11
        la x1, _fclass_jr12
        jalr	x12, x1, 0
_fclass_jr12:   fclass.s      x12, x12
        la x1, _fclass_jr13
        jalr	x13, x1, 0
_fclass_jr13:   fclass.s      x13, x13
        la x1, _fclass_jr14
        jalr	x14, x1, 0
_fclass_jr14:   fclass.s      x14, x14
        la x1, _fclass_jr15
        jalr	x15, x1, 0
_fclass_jr15:   fclass.s      x15, x15
        la x1, _fclass_jr16
        jalr	x16, x1, 0
_fclass_jr16:   fclass.s      x16, x16
        la x1, _fclass_jr17
        jalr	x17, x1, 0
_fclass_jr17:   fclass.s      x17, x17
        la x1, _fclass_jr18
        jalr	x18, x1, 0
_fclass_jr18:   fclass.s      x18, x18
        la x1, _fclass_jr19
        jalr	x19, x1, 0
_fclass_jr19:   fclass.s      x19, x19
        la x1, _fclass_jr20
        jalr	x20, x1, 0
_fclass_jr20:   fclass.s      x20, x20
        la x1, _fclass_jr21
        jalr	x21, x1, 0
_fclass_jr21:   fclass.s      x21, x21
        la x1, _fclass_jr22
        jalr	x22, x1, 0
_fclass_jr22:   fclass.s      x22, x22
        la x1, _fclass_jr23
        jalr	x23, x1, 0
_fclass_jr23:   fclass.s      x23, x23
        la x1, _fclass_jr24
        jalr	x24, x1, 0
_fclass_jr24:   fclass.s      x24, x24
        la x1, _fclass_jr25
        jalr	x25, x1, 0
_fclass_jr25:   fclass.s      x25, x25
        la x1, _fclass_jr26
        jalr	x26, x1, 0
_fclass_jr26:   fclass.s      x26, x26
        la x1, _fclass_jr27
        jalr	x27, x1, 0
_fclass_jr27:   fclass.s      x27, x27
        la x1, _fclass_jr28
        jalr	x28, x1, 0
_fclass_jr28:   fclass.s      x28, x28
        la x1, _fclass_jr29
        jalr	x29, x1, 0
_fclass_jr29:   fclass.s      x29, x29
        la x1, _fclass_jr30
        jalr	x30, x1, 0
_fclass_jr30:   fclass.s      x30, x30
        la x1, _fclass_jr31
        jalr	x31, x1, 0
_fclass_jr31:   fclass.s      x31, x31

        // 9 - jal -> fcvt.s.w (rs1)
        jal	x0, _fcvtsw_j0
_fcvtsw_j0:    fcvt.s.w      x0, x0
        jal	x1, _fcvtsw_j1
_fcvtsw_j1:    fcvt.s.w      x1, x1
        jal	x2, _fcvtsw_j2
_fcvtsw_j2:    fcvt.s.w      x2, x2
        jal	x3, _fcvtsw_j3
_fcvtsw_j3:    fcvt.s.w      x3, x3
        jal	x4, _fcvtsw_j4
_fcvtsw_j4:    fcvt.s.w      x4, x4
        jal	x5, _fcvtsw_j5
_fcvtsw_j5:    fcvt.s.w      x5, x5
        jal	x6, _fcvtsw_j6
_fcvtsw_j6:    fcvt.s.w      x6, x6
        jal	x7, _fcvtsw_j7
_fcvtsw_j7:    fcvt.s.w      x7, x7
        jal	x8, _fcvtsw_j8
_fcvtsw_j8:    fcvt.s.w      x8, x8
        jal	x9, _fcvtsw_j9
_fcvtsw_j9:    fcvt.s.w      x9, x9
        jal	x10, _fcvtsw_j10
_fcvtsw_j10:    fcvt.s.w      x10, x10
        jal	x11, _fcvtsw_j11
_fcvtsw_j11:    fcvt.s.w      x11, x11
        jal	x12, _fcvtsw_j12
_fcvtsw_j12:    fcvt.s.w      x12, x12
        jal	x13, _fcvtsw_j13
_fcvtsw_j13:    fcvt.s.w      x13, x13
        jal	x14, _fcvtsw_j14
_fcvtsw_j14:    fcvt.s.w      x14, x14
        jal	x15, _fcvtsw_j15
_fcvtsw_j15:    fcvt.s.w      x15, x15
        jal	x16, _fcvtsw_j16
_fcvtsw_j16:    fcvt.s.w      x16, x16
        jal	x17, _fcvtsw_j17
_fcvtsw_j17:    fcvt.s.w      x17, x17
        jal	x18, _fcvtsw_j18
_fcvtsw_j18:    fcvt.s.w      x18, x18
        jal	x19, _fcvtsw_j19
_fcvtsw_j19:    fcvt.s.w      x19, x19
        jal	x20, _fcvtsw_j20
_fcvtsw_j20:    fcvt.s.w      x20, x20
        jal	x21, _fcvtsw_j21
_fcvtsw_j21:    fcvt.s.w      x21, x21
        jal	x22, _fcvtsw_j22
_fcvtsw_j22:    fcvt.s.w      x22, x22
        jal	x23, _fcvtsw_j23
_fcvtsw_j23:    fcvt.s.w      x23, x23
        jal	x24, _fcvtsw_j24
_fcvtsw_j24:    fcvt.s.w      x24, x24
        jal	x25, _fcvtsw_j25
_fcvtsw_j25:    fcvt.s.w      x25, x25
        jal	x26, _fcvtsw_j26
_fcvtsw_j26:    fcvt.s.w      x26, x26
        jal	x27, _fcvtsw_j27
_fcvtsw_j27:    fcvt.s.w      x27, x27
        jal	x28, _fcvtsw_j28
_fcvtsw_j28:    fcvt.s.w      x28, x28
        jal	x29, _fcvtsw_j29
_fcvtsw_j29:    fcvt.s.w      x29, x29
        jal	x30, _fcvtsw_j30
_fcvtsw_j30:    fcvt.s.w      x30, x30
        jal	x31, _fcvtsw_j31
_fcvtsw_j31:    fcvt.s.w      x31, x31

        // 10 - jal -> fcvt.s.w (rs1)
        la x1, _fcvtsw_jr0
        jalr	x0, x1, 0
_fcvtsw_jr0:   fcvt.s.w      x0, x0
        la x1, _fcvtsw_jr1
        jalr	x1, x1, 0
_fcvtsw_jr1:   fcvt.s.w      x1, x1
        la x1, _fcvtsw_jr2
        jalr	x2, x1, 0
_fcvtsw_jr2:   fcvt.s.w      x2, x2
        la x1, _fcvtsw_jr3
        jalr	x3, x1, 0
_fcvtsw_jr3:   fcvt.s.w      x3, x3
        la x1, _fcvtsw_jr4
        jalr	x4, x1, 0
_fcvtsw_jr4:   fcvt.s.w      x4, x4
        la x1, _fcvtsw_jr5
        jalr	x5, x1, 0
_fcvtsw_jr5:   fcvt.s.w      x5, x5
        la x1, _fcvtsw_jr6
        jalr	x6, x1, 0
_fcvtsw_jr6:   fcvt.s.w      x6, x6
        la x1, _fcvtsw_jr7
        jalr	x7, x1, 0
_fcvtsw_jr7:   fcvt.s.w      x7, x7
        la x1, _fcvtsw_jr8
        jalr	x8, x1, 0
_fcvtsw_jr8:   fcvt.s.w      x8, x8
        la x1, _fcvtsw_jr9
        jalr	x9, x1, 0
_fcvtsw_jr9:   fcvt.s.w      x9, x9
        la x1, _fcvtsw_jr10
        jalr	x10, x1, 0
_fcvtsw_jr10:   fcvt.s.w      x10, x10
        la x1, _fcvtsw_jr11
        jalr	x11, x1, 0
_fcvtsw_jr11:   fcvt.s.w      x11, x11
        la x1, _fcvtsw_jr12
        jalr	x12, x1, 0
_fcvtsw_jr12:   fcvt.s.w      x12, x12
        la x1, _fcvtsw_jr13
        jalr	x13, x1, 0
_fcvtsw_jr13:   fcvt.s.w      x13, x13
        la x1, _fcvtsw_jr14
        jalr	x14, x1, 0
_fcvtsw_jr14:   fcvt.s.w      x14, x14
        la x1, _fcvtsw_jr15
        jalr	x15, x1, 0
_fcvtsw_jr15:   fcvt.s.w      x15, x15
        la x1, _fcvtsw_jr16
        jalr	x16, x1, 0
_fcvtsw_jr16:   fcvt.s.w      x16, x16
        la x1, _fcvtsw_jr17
        jalr	x17, x1, 0
_fcvtsw_jr17:   fcvt.s.w      x17, x17
        la x1, _fcvtsw_jr18
        jalr	x18, x1, 0
_fcvtsw_jr18:   fcvt.s.w      x18, x18
        la x1, _fcvtsw_jr19
        jalr	x19, x1, 0
_fcvtsw_jr19:   fcvt.s.w      x19, x19
        la x1, _fcvtsw_jr20
        jalr	x20, x1, 0
_fcvtsw_jr20:   fcvt.s.w      x20, x20
        la x1, _fcvtsw_jr21
        jalr	x21, x1, 0
_fcvtsw_jr21:   fcvt.s.w      x21, x21
        la x1, _fcvtsw_jr22
        jalr	x22, x1, 0
_fcvtsw_jr22:   fcvt.s.w      x22, x22
        la x1, _fcvtsw_jr23
        jalr	x23, x1, 0
_fcvtsw_jr23:   fcvt.s.w      x23, x23
        la x1, _fcvtsw_jr24
        jalr	x24, x1, 0
_fcvtsw_jr24:   fcvt.s.w      x24, x24
        la x1, _fcvtsw_jr25
        jalr	x25, x1, 0
_fcvtsw_jr25:   fcvt.s.w      x25, x25
        la x1, _fcvtsw_jr26
        jalr	x26, x1, 0
_fcvtsw_jr26:   fcvt.s.w      x26, x26
        la x1, _fcvtsw_jr27
        jalr	x27, x1, 0
_fcvtsw_jr27:   fcvt.s.w      x27, x27
        la x1, _fcvtsw_jr28
        jalr	x28, x1, 0
_fcvtsw_jr28:   fcvt.s.w      x28, x28
        la x1, _fcvtsw_jr29
        jalr	x29, x1, 0
_fcvtsw_jr29:   fcvt.s.w      x29, x29
        la x1, _fcvtsw_jr30
        jalr	x30, x1, 0
_fcvtsw_jr30:   fcvt.s.w      x30, x30
        la x1, _fcvtsw_jr31
        jalr	x31, x1, 0
_fcvtsw_jr31:   fcvt.s.w      x31, x31

        // 11 - jal -> fcvtswu (rs1)
        jal	x0, _fcvtswu_j0
_fcvtswu_j0:    fcvt.s.wu      x0, x0
        jal	x1, _fcvtswu_j1
_fcvtswu_j1:    fcvt.s.wu      x1, x1
        jal	x2, _fcvtswu_j2
_fcvtswu_j2:    fcvt.s.wu      x2, x2
        jal	x3, _fcvtswu_j3
_fcvtswu_j3:    fcvt.s.wu      x3, x3
        jal	x4, _fcvtswu_j4
_fcvtswu_j4:    fcvt.s.wu      x4, x4
        jal	x5, _fcvtswu_j5
_fcvtswu_j5:    fcvt.s.wu      x5, x5
        jal	x6, _fcvtswu_j6
_fcvtswu_j6:    fcvt.s.wu      x6, x6
        jal	x7, _fcvtswu_j7
_fcvtswu_j7:    fcvt.s.wu      x7, x7
        jal	x8, _fcvtswu_j8
_fcvtswu_j8:    fcvt.s.wu      x8, x8
        jal	x9, _fcvtswu_j9
_fcvtswu_j9:    fcvt.s.wu      x9, x9
        jal	x10, _fcvtswu_j10
_fcvtswu_j10:    fcvt.s.wu      x10, x10
        jal	x11, _fcvtswu_j11
_fcvtswu_j11:    fcvt.s.wu      x11, x11
        jal	x12, _fcvtswu_j12
_fcvtswu_j12:    fcvt.s.wu      x12, x12
        jal	x13, _fcvtswu_j13
_fcvtswu_j13:    fcvt.s.wu      x13, x13
        jal	x14, _fcvtswu_j14
_fcvtswu_j14:    fcvt.s.wu      x14, x14
        jal	x15, _fcvtswu_j15
_fcvtswu_j15:    fcvt.s.wu      x15, x15
        jal	x16, _fcvtswu_j16
_fcvtswu_j16:    fcvt.s.wu      x16, x16
        jal	x17, _fcvtswu_j17
_fcvtswu_j17:    fcvt.s.wu      x17, x17
        jal	x18, _fcvtswu_j18
_fcvtswu_j18:    fcvt.s.wu      x18, x18
        jal	x19, _fcvtswu_j19
_fcvtswu_j19:    fcvt.s.wu      x19, x19
        jal	x20, _fcvtswu_j20
_fcvtswu_j20:    fcvt.s.wu      x20, x20
        jal	x21, _fcvtswu_j21
_fcvtswu_j21:    fcvt.s.wu      x21, x21
        jal	x22, _fcvtswu_j22
_fcvtswu_j22:    fcvt.s.wu      x22, x22
        jal	x23, _fcvtswu_j23
_fcvtswu_j23:    fcvt.s.wu      x23, x23
        jal	x24, _fcvtswu_j24
_fcvtswu_j24:    fcvt.s.wu      x24, x24
        jal	x25, _fcvtswu_j25
_fcvtswu_j25:    fcvt.s.wu      x25, x25
        jal	x26, _fcvtswu_j26
_fcvtswu_j26:    fcvt.s.wu      x26, x26
        jal	x27, _fcvtswu_j27
_fcvtswu_j27:    fcvt.s.wu      x27, x27
        jal	x28, _fcvtswu_j28
_fcvtswu_j28:    fcvt.s.wu      x28, x28
        jal	x29, _fcvtswu_j29
_fcvtswu_j29:    fcvt.s.wu      x29, x29
        jal	x30, _fcvtswu_j30
_fcvtswu_j30:    fcvt.s.wu      x30, x30
        jal	x31, _fcvtswu_j31
_fcvtswu_j31:    fcvt.s.wu      x31, x31

        // 12 - jalr -> fcvtswu (rs1)
        la x1, _fcvtswu_jr0
        jalr	x0, x1, 0
_fcvtswu_jr0:   fcvt.s.wu      x0, x0
        la x1, _fcvtswu_jr1
        jalr	x1, x1, 0
_fcvtswu_jr1:   fcvt.s.wu      x1, x1
        la x1, _fcvtswu_jr2
        jalr	x2, x1, 0
_fcvtswu_jr2:   fcvt.s.wu      x2, x2
        la x1, _fcvtswu_jr3
        jalr	x3, x1, 0
_fcvtswu_jr3:   fcvt.s.wu      x3, x3
        la x1, _fcvtswu_jr4
        jalr	x4, x1, 0
_fcvtswu_jr4:   fcvt.s.wu      x4, x4
        la x1, _fcvtswu_jr5
        jalr	x5, x1, 0
_fcvtswu_jr5:   fcvt.s.wu      x5, x5
        la x1, _fcvtswu_jr6
        jalr	x6, x1, 0
_fcvtswu_jr6:   fcvt.s.wu      x6, x6
        la x1, _fcvtswu_jr7
        jalr	x7, x1, 0
_fcvtswu_jr7:   fcvt.s.wu      x7, x7
        la x1, _fcvtswu_jr8
        jalr	x8, x1, 0
_fcvtswu_jr8:   fcvt.s.wu      x8, x8
        la x1, _fcvtswu_jr9
        jalr	x9, x1, 0
_fcvtswu_jr9:   fcvt.s.wu      x9, x9
        la x1, _fcvtswu_jr10
        jalr	x10, x1, 0
_fcvtswu_jr10:   fcvt.s.wu      x10, x10
        la x1, _fcvtswu_jr11
        jalr	x11, x1, 0
_fcvtswu_jr11:   fcvt.s.wu      x11, x11
        la x1, _fcvtswu_jr12
        jalr	x12, x1, 0
_fcvtswu_jr12:   fcvt.s.wu      x12, x12
        la x1, _fcvtswu_jr13
        jalr	x13, x1, 0
_fcvtswu_jr13:   fcvt.s.wu      x13, x13
        la x1, _fcvtswu_jr14
        jalr	x14, x1, 0
_fcvtswu_jr14:   fcvt.s.wu      x14, x14
        la x1, _fcvtswu_jr15
        jalr	x15, x1, 0
_fcvtswu_jr15:   fcvt.s.wu      x15, x15
        la x1, _fcvtswu_jr16
        jalr	x16, x1, 0
_fcvtswu_jr16:   fcvt.s.wu      x16, x16
        la x1, _fcvtswu_jr17
        jalr	x17, x1, 0
_fcvtswu_jr17:   fcvt.s.wu      x17, x17
        la x1, _fcvtswu_jr18
        jalr	x18, x1, 0
_fcvtswu_jr18:   fcvt.s.wu      x18, x18
        la x1, _fcvtswu_jr19
        jalr	x19, x1, 0
_fcvtswu_jr19:   fcvt.s.wu      x19, x19
        la x1, _fcvtswu_jr20
        jalr	x20, x1, 0
_fcvtswu_jr20:   fcvt.s.wu      x20, x20
        la x1, _fcvtswu_jr21
        jalr	x21, x1, 0
_fcvtswu_jr21:   fcvt.s.wu      x21, x21
        la x1, _fcvtswu_jr22
        jalr	x22, x1, 0
_fcvtswu_jr22:   fcvt.s.wu      x22, x22
        la x1, _fcvtswu_jr23
        jalr	x23, x1, 0
_fcvtswu_jr23:   fcvt.s.wu      x23, x23
        la x1, _fcvtswu_jr24
        jalr	x24, x1, 0
_fcvtswu_jr24:   fcvt.s.wu      x24, x24
        la x1, _fcvtswu_jr25
        jalr	x25, x1, 0
_fcvtswu_jr25:   fcvt.s.wu      x25, x25
        la x1, _fcvtswu_jr26
        jalr	x26, x1, 0
_fcvtswu_jr26:   fcvt.s.wu      x26, x26
        la x1, _fcvtswu_jr27
        jalr	x27, x1, 0
_fcvtswu_jr27:   fcvt.s.wu      x27, x27
        la x1, _fcvtswu_jr28
        jalr	x28, x1, 0
_fcvtswu_jr28:   fcvt.s.wu      x28, x28
        la x1, _fcvtswu_jr29
        jalr	x29, x1, 0
_fcvtswu_jr29:   fcvt.s.wu      x29, x29
        la x1, _fcvtswu_jr30
        jalr	x30, x1, 0
_fcvtswu_jr30:   fcvt.s.wu      x30, x30
        la x1, _fcvtswu_jr31
        jalr	x31, x1, 0
_fcvtswu_jr31:   fcvt.s.wu      x31, x31

        // 13 - jal -> fcvtws (rs1)
        jal	x0, _fcvtws_j0
_fcvtws_j0:    fcvt.w.s      x0, x0
        jal	x1, _fcvtws_j1
_fcvtws_j1:    fcvt.w.s      x1, x1
        jal	x2, _fcvtws_j2
_fcvtws_j2:    fcvt.w.s      x2, x2
        jal	x3, _fcvtws_j3
_fcvtws_j3:    fcvt.w.s      x3, x3
        jal	x4, _fcvtws_j4
_fcvtws_j4:    fcvt.w.s      x4, x4
        jal	x5, _fcvtws_j5
_fcvtws_j5:    fcvt.w.s      x5, x5
        jal	x6, _fcvtws_j6
_fcvtws_j6:    fcvt.w.s      x6, x6
        jal	x7, _fcvtws_j7
_fcvtws_j7:    fcvt.w.s      x7, x7
        jal	x8, _fcvtws_j8
_fcvtws_j8:    fcvt.w.s      x8, x8
        jal	x9, _fcvtws_j9
_fcvtws_j9:    fcvt.w.s      x9, x9
        jal	x10, _fcvtws_j10
_fcvtws_j10:    fcvt.w.s      x10, x10
        jal	x11, _fcvtws_j11
_fcvtws_j11:    fcvt.w.s      x11, x11
        jal	x12, _fcvtws_j12
_fcvtws_j12:    fcvt.w.s      x12, x12
        jal	x13, _fcvtws_j13
_fcvtws_j13:    fcvt.w.s      x13, x13
        jal	x14, _fcvtws_j14
_fcvtws_j14:    fcvt.w.s      x14, x14
        jal	x15, _fcvtws_j15
_fcvtws_j15:    fcvt.w.s      x15, x15
        jal	x16, _fcvtws_j16
_fcvtws_j16:    fcvt.w.s      x16, x16
        jal	x17, _fcvtws_j17
_fcvtws_j17:    fcvt.w.s      x17, x17
        jal	x18, _fcvtws_j18
_fcvtws_j18:    fcvt.w.s      x18, x18
        jal	x19, _fcvtws_j19
_fcvtws_j19:    fcvt.w.s      x19, x19
        jal	x20, _fcvtws_j20
_fcvtws_j20:    fcvt.w.s      x20, x20
        jal	x21, _fcvtws_j21
_fcvtws_j21:    fcvt.w.s      x21, x21
        jal	x22, _fcvtws_j22
_fcvtws_j22:    fcvt.w.s      x22, x22
        jal	x23, _fcvtws_j23
_fcvtws_j23:    fcvt.w.s      x23, x23
        jal	x24, _fcvtws_j24
_fcvtws_j24:    fcvt.w.s      x24, x24
        jal	x25, _fcvtws_j25
_fcvtws_j25:    fcvt.w.s      x25, x25
        jal	x26, _fcvtws_j26
_fcvtws_j26:    fcvt.w.s      x26, x26
        jal	x27, _fcvtws_j27
_fcvtws_j27:    fcvt.w.s      x27, x27
        jal	x28, _fcvtws_j28
_fcvtws_j28:    fcvt.w.s      x28, x28
        jal	x29, _fcvtws_j29
_fcvtws_j29:    fcvt.w.s      x29, x29
        jal	x30, _fcvtws_j30
_fcvtws_j30:    fcvt.w.s      x30, x30
        jal	x31, _fcvtws_j31
_fcvtws_j31:    fcvt.w.s      x31, x31

        // 14 - jalr -> fcvtws (rs1)
        la x1, _fcvtws_jr0
        jalr	x0, x1, 0
_fcvtws_jr0:   fcvt.w.s      x0, x0
        la x1, _fcvtws_jr1
        jalr	x1, x1, 0
_fcvtws_jr1:   fcvt.w.s      x1, x1
        la x1, _fcvtws_jr2
        jalr	x2, x1, 0
_fcvtws_jr2:   fcvt.w.s      x2, x2
        la x1, _fcvtws_jr3
        jalr	x3, x1, 0
_fcvtws_jr3:   fcvt.w.s      x3, x3
        la x1, _fcvtws_jr4
        jalr	x4, x1, 0
_fcvtws_jr4:   fcvt.w.s      x4, x4
        la x1, _fcvtws_jr5
        jalr	x5, x1, 0
_fcvtws_jr5:   fcvt.w.s      x5, x5
        la x1, _fcvtws_jr6
        jalr	x6, x1, 0
_fcvtws_jr6:   fcvt.w.s      x6, x6
        la x1, _fcvtws_jr7
        jalr	x7, x1, 0
_fcvtws_jr7:   fcvt.w.s      x7, x7
        la x1, _fcvtws_jr8
        jalr	x8, x1, 0
_fcvtws_jr8:   fcvt.w.s      x8, x8
        la x1, _fcvtws_jr9
        jalr	x9, x1, 0
_fcvtws_jr9:   fcvt.w.s      x9, x9
        la x1, _fcvtws_jr10
        jalr	x10, x1, 0
_fcvtws_jr10:   fcvt.w.s      x10, x10
        la x1, _fcvtws_jr11
        jalr	x11, x1, 0
_fcvtws_jr11:   fcvt.w.s      x11, x11
        la x1, _fcvtws_jr12
        jalr	x12, x1, 0
_fcvtws_jr12:   fcvt.w.s      x12, x12
        la x1, _fcvtws_jr13
        jalr	x13, x1, 0
_fcvtws_jr13:   fcvt.w.s      x13, x13
        la x1, _fcvtws_jr14
        jalr	x14, x1, 0
_fcvtws_jr14:   fcvt.w.s      x14, x14
        la x1, _fcvtws_jr15
        jalr	x15, x1, 0
_fcvtws_jr15:   fcvt.w.s      x15, x15
        la x1, _fcvtws_jr16
        jalr	x16, x1, 0
_fcvtws_jr16:   fcvt.w.s      x16, x16
        la x1, _fcvtws_jr17
        jalr	x17, x1, 0
_fcvtws_jr17:   fcvt.w.s      x17, x17
        la x1, _fcvtws_jr18
        jalr	x18, x1, 0
_fcvtws_jr18:   fcvt.w.s      x18, x18
        la x1, _fcvtws_jr19
        jalr	x19, x1, 0
_fcvtws_jr19:   fcvt.w.s      x19, x19
        la x1, _fcvtws_jr20
        jalr	x20, x1, 0
_fcvtws_jr20:   fcvt.w.s      x20, x20
        la x1, _fcvtws_jr21
        jalr	x21, x1, 0
_fcvtws_jr21:   fcvt.w.s      x21, x21
        la x1, _fcvtws_jr22
        jalr	x22, x1, 0
_fcvtws_jr22:   fcvt.w.s      x22, x22
        la x1, _fcvtws_jr23
        jalr	x23, x1, 0
_fcvtws_jr23:   fcvt.w.s      x23, x23
        la x1, _fcvtws_jr24
        jalr	x24, x1, 0
_fcvtws_jr24:   fcvt.w.s      x24, x24
        la x1, _fcvtws_jr25
        jalr	x25, x1, 0
_fcvtws_jr25:   fcvt.w.s      x25, x25
        la x1, _fcvtws_jr26
        jalr	x26, x1, 0
_fcvtws_jr26:   fcvt.w.s      x26, x26
        la x1, _fcvtws_jr27
        jalr	x27, x1, 0
_fcvtws_jr27:   fcvt.w.s      x27, x27
        la x1, _fcvtws_jr28
        jalr	x28, x1, 0
_fcvtws_jr28:   fcvt.w.s      x28, x28
        la x1, _fcvtws_jr29
        jalr	x29, x1, 0
_fcvtws_jr29:   fcvt.w.s      x29, x29
        la x1, _fcvtws_jr30
        jalr	x30, x1, 0
_fcvtws_jr30:   fcvt.w.s      x30, x30
        la x1, _fcvtws_jr31
        jalr	x31, x1, 0
_fcvtws_jr31:   fcvt.w.s      x31, x31

        // 15 - jal -> fcvtwus (rs1)
        jal	x0, _fcvtwus_j0
_fcvtwus_j0:    fcvt.wu.s      x0, x0
        jal	x1, _fcvtwus_j1
_fcvtwus_j1:    fcvt.wu.s      x1, x1
        jal	x2, _fcvtwus_j2
_fcvtwus_j2:    fcvt.wu.s      x2, x2
        jal	x3, _fcvtwus_j3
_fcvtwus_j3:    fcvt.wu.s      x3, x3
        jal	x4, _fcvtwus_j4
_fcvtwus_j4:    fcvt.wu.s      x4, x4
        jal	x5, _fcvtwus_j5
_fcvtwus_j5:    fcvt.wu.s      x5, x5
        jal	x6, _fcvtwus_j6
_fcvtwus_j6:    fcvt.wu.s      x6, x6
        jal	x7, _fcvtwus_j7
_fcvtwus_j7:    fcvt.wu.s      x7, x7
        jal	x8, _fcvtwus_j8
_fcvtwus_j8:    fcvt.wu.s      x8, x8
        jal	x9, _fcvtwus_j9
_fcvtwus_j9:    fcvt.wu.s      x9, x9
        jal	x10, _fcvtwus_j10
_fcvtwus_j10:    fcvt.wu.s      x10, x10
        jal	x11, _fcvtwus_j11
_fcvtwus_j11:    fcvt.wu.s      x11, x11
        jal	x12, _fcvtwus_j12
_fcvtwus_j12:    fcvt.wu.s      x12, x12
        jal	x13, _fcvtwus_j13
_fcvtwus_j13:    fcvt.wu.s      x13, x13
        jal	x14, _fcvtwus_j14
_fcvtwus_j14:    fcvt.wu.s      x14, x14
        jal	x15, _fcvtwus_j15
_fcvtwus_j15:    fcvt.wu.s      x15, x15
        jal	x16, _fcvtwus_j16
_fcvtwus_j16:    fcvt.wu.s      x16, x16
        jal	x17, _fcvtwus_j17
_fcvtwus_j17:    fcvt.wu.s      x17, x17
        jal	x18, _fcvtwus_j18
_fcvtwus_j18:    fcvt.wu.s      x18, x18
        jal	x19, _fcvtwus_j19
_fcvtwus_j19:    fcvt.wu.s      x19, x19
        jal	x20, _fcvtwus_j20
_fcvtwus_j20:    fcvt.wu.s      x20, x20
        jal	x21, _fcvtwus_j21
_fcvtwus_j21:    fcvt.wu.s      x21, x21
        jal	x22, _fcvtwus_j22
_fcvtwus_j22:    fcvt.wu.s      x22, x22
        jal	x23, _fcvtwus_j23
_fcvtwus_j23:    fcvt.wu.s      x23, x23
        jal	x24, _fcvtwus_j24
_fcvtwus_j24:    fcvt.wu.s      x24, x24
        jal	x25, _fcvtwus_j25
_fcvtwus_j25:    fcvt.wu.s      x25, x25
        jal	x26, _fcvtwus_j26
_fcvtwus_j26:    fcvt.wu.s      x26, x26
        jal	x27, _fcvtwus_j27
_fcvtwus_j27:    fcvt.wu.s      x27, x27
        jal	x28, _fcvtwus_j28
_fcvtwus_j28:    fcvt.wu.s      x28, x28
        jal	x29, _fcvtwus_j29
_fcvtwus_j29:    fcvt.wu.s      x29, x29
        jal	x30, _fcvtwus_j30
_fcvtwus_j30:    fcvt.wu.s      x30, x30
        jal	x31, _fcvtwus_j31
_fcvtwus_j31:    fcvt.wu.s      x31, x31

        // 16 - jalr -> fcvtwus (rs1)
        la x1, _fcvtwus_jr0
        jalr	x0, x1, 0
_fcvtwus_jr0:   fcvt.wu.s      x0, x0
        la x1, _fcvtwus_jr1
        jalr	x1, x1, 0
_fcvtwus_jr1:   fcvt.wu.s      x1, x1
        la x1, _fcvtwus_jr2
        jalr	x2, x1, 0
_fcvtwus_jr2:   fcvt.wu.s      x2, x2
        la x1, _fcvtwus_jr3
        jalr	x3, x1, 0
_fcvtwus_jr3:   fcvt.wu.s      x3, x3
        la x1, _fcvtwus_jr4
        jalr	x4, x1, 0
_fcvtwus_jr4:   fcvt.wu.s      x4, x4
        la x1, _fcvtwus_jr5
        jalr	x5, x1, 0
_fcvtwus_jr5:   fcvt.wu.s      x5, x5
        la x1, _fcvtwus_jr6
        jalr	x6, x1, 0
_fcvtwus_jr6:   fcvt.wu.s      x6, x6
        la x1, _fcvtwus_jr7
        jalr	x7, x1, 0
_fcvtwus_jr7:   fcvt.wu.s      x7, x7
        la x1, _fcvtwus_jr8
        jalr	x8, x1, 0
_fcvtwus_jr8:   fcvt.wu.s      x8, x8
        la x1, _fcvtwus_jr9
        jalr	x9, x1, 0
_fcvtwus_jr9:   fcvt.wu.s      x9, x9
        la x1, _fcvtwus_jr10
        jalr	x10, x1, 0
_fcvtwus_jr10:   fcvt.wu.s      x10, x10
        la x1, _fcvtwus_jr11
        jalr	x11, x1, 0
_fcvtwus_jr11:   fcvt.wu.s      x11, x11
        la x1, _fcvtwus_jr12
        jalr	x12, x1, 0
_fcvtwus_jr12:   fcvt.wu.s      x12, x12
        la x1, _fcvtwus_jr13
        jalr	x13, x1, 0
_fcvtwus_jr13:   fcvt.wu.s      x13, x13
        la x1, _fcvtwus_jr14
        jalr	x14, x1, 0
_fcvtwus_jr14:   fcvt.wu.s      x14, x14
        la x1, _fcvtwus_jr15
        jalr	x15, x1, 0
_fcvtwus_jr15:   fcvt.wu.s      x15, x15
        la x1, _fcvtwus_jr16
        jalr	x16, x1, 0
_fcvtwus_jr16:   fcvt.wu.s      x16, x16
        la x1, _fcvtwus_jr17
        jalr	x17, x1, 0
_fcvtwus_jr17:   fcvt.wu.s      x17, x17
        la x1, _fcvtwus_jr18
        jalr	x18, x1, 0
_fcvtwus_jr18:   fcvt.wu.s      x18, x18
        la x1, _fcvtwus_jr19
        jalr	x19, x1, 0
_fcvtwus_jr19:   fcvt.wu.s      x19, x19
        la x1, _fcvtwus_jr20
        jalr	x20, x1, 0
_fcvtwus_jr20:   fcvt.wu.s      x20, x20
        la x1, _fcvtwus_jr21
        jalr	x21, x1, 0
_fcvtwus_jr21:   fcvt.wu.s      x21, x21
        la x1, _fcvtwus_jr22
        jalr	x22, x1, 0
_fcvtwus_jr22:   fcvt.wu.s      x22, x22
        la x1, _fcvtwus_jr23
        jalr	x23, x1, 0
_fcvtwus_jr23:   fcvt.wu.s      x23, x23
        la x1, _fcvtwus_jr24
        jalr	x24, x1, 0
_fcvtwus_jr24:   fcvt.wu.s      x24, x24
        la x1, _fcvtwus_jr25
        jalr	x25, x1, 0
_fcvtwus_jr25:   fcvt.wu.s      x25, x25
        la x1, _fcvtwus_jr26
        jalr	x26, x1, 0
_fcvtwus_jr26:   fcvt.wu.s      x26, x26
        la x1, _fcvtwus_jr27
        jalr	x27, x1, 0
_fcvtwus_jr27:   fcvt.wu.s      x27, x27
        la x1, _fcvtwus_jr28
        jalr	x28, x1, 0
_fcvtwus_jr28:   fcvt.wu.s      x28, x28
        la x1, _fcvtwus_jr29
        jalr	x29, x1, 0
_fcvtwus_jr29:   fcvt.wu.s      x29, x29
        la x1, _fcvtwus_jr30
        jalr	x30, x1, 0
_fcvtwus_jr30:   fcvt.wu.s      x30, x30
        la x1, _fcvtwus_jr31
        jalr	x31, x1, 0
_fcvtwus_jr31:   fcvt.wu.s      x31, x31

        // 17 - jal -> fdiv (rs1, rs2)
        jal	x0, _fdiv_j0
_fdiv_j0:    fdiv.s      x0, x0, x0
        jal	x1, _fdiv_j1
_fdiv_j1:    fdiv.s      x1, x1, x1
        jal	x2, _fdiv_j2
_fdiv_j2:    fdiv.s      x2, x2, x2
        jal	x3, _fdiv_j3
_fdiv_j3:    fdiv.s      x3, x3, x3
        jal	x4, _fdiv_j4
_fdiv_j4:    fdiv.s      x4, x4, x4
        jal	x5, _fdiv_j5
_fdiv_j5:    fdiv.s      x5, x5, x5
        jal	x6, _fdiv_j6
_fdiv_j6:    fdiv.s      x6, x6, x6
        jal	x7, _fdiv_j7
_fdiv_j7:    fdiv.s      x7, x7, x7
        jal	x8, _fdiv_j8
_fdiv_j8:    fdiv.s      x8, x8, x8
        jal	x9, _fdiv_j9
_fdiv_j9:    fdiv.s      x9, x9, x9
        jal	x10, _fdiv_j10
_fdiv_j10:    fdiv.s      x10, x10, x10
        jal	x11, _fdiv_j11
_fdiv_j11:    fdiv.s      x11, x11, x11
        jal	x12, _fdiv_j12
_fdiv_j12:    fdiv.s      x12, x12, x12
        jal	x13, _fdiv_j13
_fdiv_j13:    fdiv.s      x13, x13, x13
        jal	x14, _fdiv_j14
_fdiv_j14:    fdiv.s      x14, x14, x14
        jal	x15, _fdiv_j15
_fdiv_j15:    fdiv.s      x15, x15, x15
        jal	x16, _fdiv_j16
_fdiv_j16:    fdiv.s      x16, x16, x16
        jal	x17, _fdiv_j17
_fdiv_j17:    fdiv.s      x17, x17, x17
        jal	x18, _fdiv_j18
_fdiv_j18:    fdiv.s      x18, x18, x18
        jal	x19, _fdiv_j19
_fdiv_j19:    fdiv.s      x19, x19, x19
        jal	x20, _fdiv_j20
_fdiv_j20:    fdiv.s      x20, x20, x20
        jal	x21, _fdiv_j21
_fdiv_j21:    fdiv.s      x21, x21, x21
        jal	x22, _fdiv_j22
_fdiv_j22:    fdiv.s      x22, x22, x22
        jal	x23, _fdiv_j23
_fdiv_j23:    fdiv.s      x23, x23, x23
        jal	x24, _fdiv_j24
_fdiv_j24:    fdiv.s      x24, x24, x24
        jal	x25, _fdiv_j25
_fdiv_j25:    fdiv.s      x25, x25, x25
        jal	x26, _fdiv_j26
_fdiv_j26:    fdiv.s      x26, x26, x26
        jal	x27, _fdiv_j27
_fdiv_j27:    fdiv.s      x27, x27, x27
        jal	x28, _fdiv_j28
_fdiv_j28:    fdiv.s      x28, x28, x28
        jal	x29, _fdiv_j29
_fdiv_j29:    fdiv.s      x29, x29, x29
        jal	x30, _fdiv_j30
_fdiv_j30:    fdiv.s      x30, x30, x30
        jal	x31, _fdiv_j31
_fdiv_j31:    fdiv.s      x31, x31, x31

        // 18 - jalr -> fdiv (rs1, rs2)
        la x1, _fdiv_jr0
        jalr	x0, x1, 0
_fdiv_jr0:   fdiv.s      x0, x0, x0
        la x1, _fdiv_jr1
        jalr	x1, x1, 0
_fdiv_jr1:   fdiv.s      x1, x1, x1
        la x1, _fdiv_jr2
        jalr	x2, x1, 0
_fdiv_jr2:   fdiv.s      x2, x2, x2
        la x1, _fdiv_jr3
        jalr	x3, x1, 0
_fdiv_jr3:   fdiv.s      x3, x3, x3
        la x1, _fdiv_jr4
        jalr	x4, x1, 0
_fdiv_jr4:   fdiv.s      x4, x4, x4
        la x1, _fdiv_jr5
        jalr	x5, x1, 0
_fdiv_jr5:   fdiv.s      x5, x5, x5
        la x1, _fdiv_jr6
        jalr	x6, x1, 0
_fdiv_jr6:   fdiv.s      x6, x6, x6
        la x1, _fdiv_jr7
        jalr	x7, x1, 0
_fdiv_jr7:   fdiv.s      x7, x7, x7
        la x1, _fdiv_jr8
        jalr	x8, x1, 0
_fdiv_jr8:   fdiv.s      x8, x8, x8
        la x1, _fdiv_jr9
        jalr	x9, x1, 0
_fdiv_jr9:   fdiv.s      x9, x9, x9
        la x1, _fdiv_jr10
        jalr	x10, x1, 0
_fdiv_jr10:   fdiv.s      x10, x10, x10
        la x1, _fdiv_jr11
        jalr	x11, x1, 0
_fdiv_jr11:   fdiv.s      x11, x11, x11
        la x1, _fdiv_jr12
        jalr	x12, x1, 0
_fdiv_jr12:   fdiv.s      x12, x12, x12
        la x1, _fdiv_jr13
        jalr	x13, x1, 0
_fdiv_jr13:   fdiv.s      x13, x13, x13
        la x1, _fdiv_jr14
        jalr	x14, x1, 0
_fdiv_jr14:   fdiv.s      x14, x14, x14
        la x1, _fdiv_jr15
        jalr	x15, x1, 0
_fdiv_jr15:   fdiv.s      x15, x15, x15
        la x1, _fdiv_jr16
        jalr	x16, x1, 0
_fdiv_jr16:   fdiv.s      x16, x16, x16
        la x1, _fdiv_jr17
        jalr	x17, x1, 0
_fdiv_jr17:   fdiv.s      x17, x17, x17
        la x1, _fdiv_jr18
        jalr	x18, x1, 0
_fdiv_jr18:   fdiv.s      x18, x18, x18
        la x1, _fdiv_jr19
        jalr	x19, x1, 0
_fdiv_jr19:   fdiv.s      x19, x19, x19
        la x1, _fdiv_jr20
        jalr	x20, x1, 0
_fdiv_jr20:   fdiv.s      x20, x20, x20
        la x1, _fdiv_jr21
        jalr	x21, x1, 0
_fdiv_jr21:   fdiv.s      x21, x21, x21
        la x1, _fdiv_jr22
        jalr	x22, x1, 0
_fdiv_jr22:   fdiv.s      x22, x22, x22
        la x1, _fdiv_jr23
        jalr	x23, x1, 0
_fdiv_jr23:   fdiv.s      x23, x23, x23
        la x1, _fdiv_jr24
        jalr	x24, x1, 0
_fdiv_jr24:   fdiv.s      x24, x24, x24
        la x1, _fdiv_jr25
        jalr	x25, x1, 0
_fdiv_jr25:   fdiv.s      x25, x25, x25
        la x1, _fdiv_jr26
        jalr	x26, x1, 0
_fdiv_jr26:   fdiv.s      x26, x26, x26
        la x1, _fdiv_jr27
        jalr	x27, x1, 0
_fdiv_jr27:   fdiv.s      x27, x27, x27
        la x1, _fdiv_jr28
        jalr	x28, x1, 0
_fdiv_jr28:   fdiv.s      x28, x28, x28
        la x1, _fdiv_jr29
        jalr	x29, x1, 0
_fdiv_jr29:   fdiv.s      x29, x29, x29
        la x1, _fdiv_jr30
        jalr	x30, x1, 0
_fdiv_jr30:   fdiv.s      x30, x30, x30
        la x1, _fdiv_jr31
        jalr	x31, x1, 0
_fdiv_jr31:   fdiv.s      x31, x31, x31

        // 19 - jal -> feq (rs1, rs2)
        jal	x0, _feq_j0
_feq_j0:    feq.s      x0, x0, x0
        jal	x1, _feq_j1
_feq_j1:    feq.s      x1, x1, x1
        jal	x2, _feq_j2
_feq_j2:    feq.s      x2, x2, x2
        jal	x3, _feq_j3
_feq_j3:    feq.s      x3, x3, x3
        jal	x4, _feq_j4
_feq_j4:    feq.s      x4, x4, x4
        jal	x5, _feq_j5
_feq_j5:    feq.s      x5, x5, x5
        jal	x6, _feq_j6
_feq_j6:    feq.s      x6, x6, x6
        jal	x7, _feq_j7
_feq_j7:    feq.s      x7, x7, x7
        jal	x8, _feq_j8
_feq_j8:    feq.s      x8, x8, x8
        jal	x9, _feq_j9
_feq_j9:    feq.s      x9, x9, x9
        jal	x10, _feq_j10
_feq_j10:    feq.s      x10, x10, x10
        jal	x11, _feq_j11
_feq_j11:    feq.s      x11, x11, x11
        jal	x12, _feq_j12
_feq_j12:    feq.s      x12, x12, x12
        jal	x13, _feq_j13
_feq_j13:    feq.s      x13, x13, x13
        jal	x14, _feq_j14
_feq_j14:    feq.s      x14, x14, x14
        jal	x15, _feq_j15
_feq_j15:    feq.s      x15, x15, x15
        jal	x16, _feq_j16
_feq_j16:    feq.s      x16, x16, x16
        jal	x17, _feq_j17
_feq_j17:    feq.s      x17, x17, x17
        jal	x18, _feq_j18
_feq_j18:    feq.s      x18, x18, x18
        jal	x19, _feq_j19
_feq_j19:    feq.s      x19, x19, x19
        jal	x20, _feq_j20
_feq_j20:    feq.s      x20, x20, x20
        jal	x21, _feq_j21
_feq_j21:    feq.s      x21, x21, x21
        jal	x22, _feq_j22
_feq_j22:    feq.s      x22, x22, x22
        jal	x23, _feq_j23
_feq_j23:    feq.s      x23, x23, x23
        jal	x24, _feq_j24
_feq_j24:    feq.s      x24, x24, x24
        jal	x25, _feq_j25
_feq_j25:    feq.s      x25, x25, x25
        jal	x26, _feq_j26
_feq_j26:    feq.s      x26, x26, x26
        jal	x27, _feq_j27
_feq_j27:    feq.s      x27, x27, x27
        jal	x28, _feq_j28
_feq_j28:    feq.s      x28, x28, x28
        jal	x29, _feq_j29
_feq_j29:    feq.s      x29, x29, x29
        jal	x30, _feq_j30
_feq_j30:    feq.s      x30, x30, x30
        jal	x31, _feq_j31
_feq_j31:    feq.s      x31, x31, x31

        // 20 - jalr -> feq (rs1, rs2)
        la x1, _feq_jr0
        jalr	x0, x1, 0
_feq_jr0:   feq.s      x0, x0, x0
        la x1, _feq_jr1
        jalr	x1, x1, 0
_feq_jr1:   feq.s      x1, x1, x1
        la x1, _feq_jr2
        jalr	x2, x1, 0
_feq_jr2:   feq.s      x2, x2, x2
        la x1, _feq_jr3
        jalr	x3, x1, 0
_feq_jr3:   feq.s      x3, x3, x3
        la x1, _feq_jr4
        jalr	x4, x1, 0
_feq_jr4:   feq.s      x4, x4, x4
        la x1, _feq_jr5
        jalr	x5, x1, 0
_feq_jr5:   feq.s      x5, x5, x5
        la x1, _feq_jr6
        jalr	x6, x1, 0
_feq_jr6:   feq.s      x6, x6, x6
        la x1, _feq_jr7
        jalr	x7, x1, 0
_feq_jr7:   feq.s      x7, x7, x7
        la x1, _feq_jr8
        jalr	x8, x1, 0
_feq_jr8:   feq.s      x8, x8, x8
        la x1, _feq_jr9
        jalr	x9, x1, 0
_feq_jr9:   feq.s      x9, x9, x9
        la x1, _feq_jr10
        jalr	x10, x1, 0
_feq_jr10:   feq.s      x10, x10, x10
        la x1, _feq_jr11
        jalr	x11, x1, 0
_feq_jr11:   feq.s      x11, x11, x11
        la x1, _feq_jr12
        jalr	x12, x1, 0
_feq_jr12:   feq.s      x12, x12, x12
        la x1, _feq_jr13
        jalr	x13, x1, 0
_feq_jr13:   feq.s      x13, x13, x13
        la x1, _feq_jr14
        jalr	x14, x1, 0
_feq_jr14:   feq.s      x14, x14, x14
        la x1, _feq_jr15
        jalr	x15, x1, 0
_feq_jr15:   feq.s      x15, x15, x15
        la x1, _feq_jr16
        jalr	x16, x1, 0
_feq_jr16:   feq.s      x16, x16, x16
        la x1, _feq_jr17
        jalr	x17, x1, 0
_feq_jr17:   feq.s      x17, x17, x17
        la x1, _feq_jr18
        jalr	x18, x1, 0
_feq_jr18:   feq.s      x18, x18, x18
        la x1, _feq_jr19
        jalr	x19, x1, 0
_feq_jr19:   feq.s      x19, x19, x19
        la x1, _feq_jr20
        jalr	x20, x1, 0
_feq_jr20:   feq.s      x20, x20, x20
        la x1, _feq_jr21
        jalr	x21, x1, 0
_feq_jr21:   feq.s      x21, x21, x21
        la x1, _feq_jr22
        jalr	x22, x1, 0
_feq_jr22:   feq.s      x22, x22, x22
        la x1, _feq_jr23
        jalr	x23, x1, 0
_feq_jr23:   feq.s      x23, x23, x23
        la x1, _feq_jr24
        jalr	x24, x1, 0
_feq_jr24:   feq.s      x24, x24, x24
        la x1, _feq_jr25
        jalr	x25, x1, 0
_feq_jr25:   feq.s      x25, x25, x25
        la x1, _feq_jr26
        jalr	x26, x1, 0
_feq_jr26:   feq.s      x26, x26, x26
        la x1, _feq_jr27
        jalr	x27, x1, 0
_feq_jr27:   feq.s      x27, x27, x27
        la x1, _feq_jr28
        jalr	x28, x1, 0
_feq_jr28:   feq.s      x28, x28, x28
        la x1, _feq_jr29
        jalr	x29, x1, 0
_feq_jr29:   feq.s      x29, x29, x29
        la x1, _feq_jr30
        jalr	x30, x1, 0
_feq_jr30:   feq.s      x30, x30, x30
        la x1, _feq_jr31
        jalr	x31, x1, 0
_feq_jr31:   feq.s      x31, x31, x31

        // 21 - jal -> fle (rs1, rs2)
        jal	x0, _fle_j0
_fle_j0:    fle.s      x0, x0, x0
        jal	x1, _fle_j1
_fle_j1:    fle.s      x1, x1, x1
        jal	x2, _fle_j2
_fle_j2:    fle.s      x2, x2, x2
        jal	x3, _fle_j3
_fle_j3:    fle.s      x3, x3, x3
        jal	x4, _fle_j4
_fle_j4:    fle.s      x4, x4, x4
        jal	x5, _fle_j5
_fle_j5:    fle.s      x5, x5, x5
        jal	x6, _fle_j6
_fle_j6:    fle.s      x6, x6, x6
        jal	x7, _fle_j7
_fle_j7:    fle.s      x7, x7, x7
        jal	x8, _fle_j8
_fle_j8:    fle.s      x8, x8, x8
        jal	x9, _fle_j9
_fle_j9:    fle.s      x9, x9, x9
        jal	x10, _fle_j10
_fle_j10:    fle.s      x10, x10, x10
        jal	x11, _fle_j11
_fle_j11:    fle.s      x11, x11, x11
        jal	x12, _fle_j12
_fle_j12:    fle.s      x12, x12, x12
        jal	x13, _fle_j13
_fle_j13:    fle.s      x13, x13, x13
        jal	x14, _fle_j14
_fle_j14:    fle.s      x14, x14, x14
        jal	x15, _fle_j15
_fle_j15:    fle.s      x15, x15, x15
        jal	x16, _fle_j16
_fle_j16:    fle.s      x16, x16, x16
        jal	x17, _fle_j17
_fle_j17:    fle.s      x17, x17, x17
        jal	x18, _fle_j18
_fle_j18:    fle.s      x18, x18, x18
        jal	x19, _fle_j19
_fle_j19:    fle.s      x19, x19, x19
        jal	x20, _fle_j20
_fle_j20:    fle.s      x20, x20, x20
        jal	x21, _fle_j21
_fle_j21:    fle.s      x21, x21, x21
        jal	x22, _fle_j22
_fle_j22:    fle.s      x22, x22, x22
        jal	x23, _fle_j23
_fle_j23:    fle.s      x23, x23, x23
        jal	x24, _fle_j24
_fle_j24:    fle.s      x24, x24, x24
        jal	x25, _fle_j25
_fle_j25:    fle.s      x25, x25, x25
        jal	x26, _fle_j26
_fle_j26:    fle.s      x26, x26, x26
        jal	x27, _fle_j27
_fle_j27:    fle.s      x27, x27, x27
        jal	x28, _fle_j28
_fle_j28:    fle.s      x28, x28, x28
        jal	x29, _fle_j29
_fle_j29:    fle.s      x29, x29, x29
        jal	x30, _fle_j30
_fle_j30:    fle.s      x30, x30, x30
        jal	x31, _fle_j31
_fle_j31:    fle.s      x31, x31, x31

        // 22 - jal -> fle (rs1, rs2)
        la x1, _fle_jr0
        jalr	x0, x1, 0
_fle_jr0:   fle.s      x0, x0, x0
        la x1, _fle_jr1
        jalr	x1, x1, 0
_fle_jr1:   fle.s      x1, x1, x1
        la x1, _fle_jr2
        jalr	x2, x1, 0
_fle_jr2:   fle.s      x2, x2, x2
        la x1, _fle_jr3
        jalr	x3, x1, 0
_fle_jr3:   fle.s      x3, x3, x3
        la x1, _fle_jr4
        jalr	x4, x1, 0
_fle_jr4:   fle.s      x4, x4, x4
        la x1, _fle_jr5
        jalr	x5, x1, 0
_fle_jr5:   fle.s      x5, x5, x5
        la x1, _fle_jr6
        jalr	x6, x1, 0
_fle_jr6:   fle.s      x6, x6, x6
        la x1, _fle_jr7
        jalr	x7, x1, 0
_fle_jr7:   fle.s      x7, x7, x7
        la x1, _fle_jr8
        jalr	x8, x1, 0
_fle_jr8:   fle.s      x8, x8, x8
        la x1, _fle_jr9
        jalr	x9, x1, 0
_fle_jr9:   fle.s      x9, x9, x9
        la x1, _fle_jr10
        jalr	x10, x1, 0
_fle_jr10:   fle.s      x10, x10, x10
        la x1, _fle_jr11
        jalr	x11, x1, 0
_fle_jr11:   fle.s      x11, x11, x11
        la x1, _fle_jr12
        jalr	x12, x1, 0
_fle_jr12:   fle.s      x12, x12, x12
        la x1, _fle_jr13
        jalr	x13, x1, 0
_fle_jr13:   fle.s      x13, x13, x13
        la x1, _fle_jr14
        jalr	x14, x1, 0
_fle_jr14:   fle.s      x14, x14, x14
        la x1, _fle_jr15
        jalr	x15, x1, 0
_fle_jr15:   fle.s      x15, x15, x15
        la x1, _fle_jr16
        jalr	x16, x1, 0
_fle_jr16:   fle.s      x16, x16, x16
        la x1, _fle_jr17
        jalr	x17, x1, 0
_fle_jr17:   fle.s      x17, x17, x17
        la x1, _fle_jr18
        jalr	x18, x1, 0
_fle_jr18:   fle.s      x18, x18, x18
        la x1, _fle_jr19
        jalr	x19, x1, 0
_fle_jr19:   fle.s      x19, x19, x19
        la x1, _fle_jr20
        jalr	x20, x1, 0
_fle_jr20:   fle.s      x20, x20, x20
        la x1, _fle_jr21
        jalr	x21, x1, 0
_fle_jr21:   fle.s      x21, x21, x21
        la x1, _fle_jr22
        jalr	x22, x1, 0
_fle_jr22:   fle.s      x22, x22, x22
        la x1, _fle_jr23
        jalr	x23, x1, 0
_fle_jr23:   fle.s      x23, x23, x23
        la x1, _fle_jr24
        jalr	x24, x1, 0
_fle_jr24:   fle.s      x24, x24, x24
        la x1, _fle_jr25
        jalr	x25, x1, 0
_fle_jr25:   fle.s      x25, x25, x25
        la x1, _fle_jr26
        jalr	x26, x1, 0
_fle_jr26:   fle.s      x26, x26, x26
        la x1, _fle_jr27
        jalr	x27, x1, 0
_fle_jr27:   fle.s      x27, x27, x27
        la x1, _fle_jr28
        jalr	x28, x1, 0
_fle_jr28:   fle.s      x28, x28, x28
        la x1, _fle_jr29
        jalr	x29, x1, 0
_fle_jr29:   fle.s      x29, x29, x29
        la x1, _fle_jr30
        jalr	x30, x1, 0
_fle_jr30:   fle.s      x30, x30, x30
        la x1, _fle_jr31
        jalr	x31, x1, 0
_fle_jr31:   fle.s      x31, x31, x31

        // 23 - jal -> flt (rs1, rs2)
        jal	x0, _flt_j0
_flt_j0:    flt.s      x0, x0, x0
        jal	x1, _flt_j1
_flt_j1:    flt.s      x1, x1, x1
        jal	x2, _flt_j2
_flt_j2:    flt.s      x2, x2, x2
        jal	x3, _flt_j3
_flt_j3:    flt.s      x3, x3, x3
        jal	x4, _flt_j4
_flt_j4:    flt.s      x4, x4, x4
        jal	x5, _flt_j5
_flt_j5:    flt.s      x5, x5, x5
        jal	x6, _flt_j6
_flt_j6:    flt.s      x6, x6, x6
        jal	x7, _flt_j7
_flt_j7:    flt.s      x7, x7, x7
        jal	x8, _flt_j8
_flt_j8:    flt.s      x8, x8, x8
        jal	x9, _flt_j9
_flt_j9:    flt.s      x9, x9, x9
        jal	x10, _flt_j10
_flt_j10:    flt.s      x10, x10, x10
        jal	x11, _flt_j11
_flt_j11:    flt.s      x11, x11, x11
        jal	x12, _flt_j12
_flt_j12:    flt.s      x12, x12, x12
        jal	x13, _flt_j13
_flt_j13:    flt.s      x13, x13, x13
        jal	x14, _flt_j14
_flt_j14:    flt.s      x14, x14, x14
        jal	x15, _flt_j15
_flt_j15:    flt.s      x15, x15, x15
        jal	x16, _flt_j16
_flt_j16:    flt.s      x16, x16, x16
        jal	x17, _flt_j17
_flt_j17:    flt.s      x17, x17, x17
        jal	x18, _flt_j18
_flt_j18:    flt.s      x18, x18, x18
        jal	x19, _flt_j19
_flt_j19:    flt.s      x19, x19, x19
        jal	x20, _flt_j20
_flt_j20:    flt.s      x20, x20, x20
        jal	x21, _flt_j21
_flt_j21:    flt.s      x21, x21, x21
        jal	x22, _flt_j22
_flt_j22:    flt.s      x22, x22, x22
        jal	x23, _flt_j23
_flt_j23:    flt.s      x23, x23, x23
        jal	x24, _flt_j24
_flt_j24:    flt.s      x24, x24, x24
        jal	x25, _flt_j25
_flt_j25:    flt.s      x25, x25, x25
        jal	x26, _flt_j26
_flt_j26:    flt.s      x26, x26, x26
        jal	x27, _flt_j27
_flt_j27:    flt.s      x27, x27, x27
        jal	x28, _flt_j28
_flt_j28:    flt.s      x28, x28, x28
        jal	x29, _flt_j29
_flt_j29:    flt.s      x29, x29, x29
        jal	x30, _flt_j30
_flt_j30:    flt.s      x30, x30, x30
        jal	x31, _flt_j31
_flt_j31:    flt.s      x31, x31, x31

        // 24 - jalr -> flt (rs1, rs2)
        la x1, _flt_jr0
        jalr	x0, x1, 0
_flt_jr0:   flt.s      x0, x0, x0
        la x1, _flt_jr1
        jalr	x1, x1, 0
_flt_jr1:   flt.s      x1, x1, x1
        la x1, _flt_jr2
        jalr	x2, x1, 0
_flt_jr2:   flt.s      x2, x2, x2
        la x1, _flt_jr3
        jalr	x3, x1, 0
_flt_jr3:   flt.s      x3, x3, x3
        la x1, _flt_jr4
        jalr	x4, x1, 0
_flt_jr4:   flt.s      x4, x4, x4
        la x1, _flt_jr5
        jalr	x5, x1, 0
_flt_jr5:   flt.s      x5, x5, x5
        la x1, _flt_jr6
        jalr	x6, x1, 0
_flt_jr6:   flt.s      x6, x6, x6
        la x1, _flt_jr7
        jalr	x7, x1, 0
_flt_jr7:   flt.s      x7, x7, x7
        la x1, _flt_jr8
        jalr	x8, x1, 0
_flt_jr8:   flt.s      x8, x8, x8
        la x1, _flt_jr9
        jalr	x9, x1, 0
_flt_jr9:   flt.s      x9, x9, x9
        la x1, _flt_jr10
        jalr	x10, x1, 0
_flt_jr10:   flt.s      x10, x10, x10
        la x1, _flt_jr11
        jalr	x11, x1, 0
_flt_jr11:   flt.s      x11, x11, x11
        la x1, _flt_jr12
        jalr	x12, x1, 0
_flt_jr12:   flt.s      x12, x12, x12
        la x1, _flt_jr13
        jalr	x13, x1, 0
_flt_jr13:   flt.s      x13, x13, x13
        la x1, _flt_jr14
        jalr	x14, x1, 0
_flt_jr14:   flt.s      x14, x14, x14
        la x1, _flt_jr15
        jalr	x15, x1, 0
_flt_jr15:   flt.s      x15, x15, x15
        la x1, _flt_jr16
        jalr	x16, x1, 0
_flt_jr16:   flt.s      x16, x16, x16
        la x1, _flt_jr17
        jalr	x17, x1, 0
_flt_jr17:   flt.s      x17, x17, x17
        la x1, _flt_jr18
        jalr	x18, x1, 0
_flt_jr18:   flt.s      x18, x18, x18
        la x1, _flt_jr19
        jalr	x19, x1, 0
_flt_jr19:   flt.s      x19, x19, x19
        la x1, _flt_jr20
        jalr	x20, x1, 0
_flt_jr20:   flt.s      x20, x20, x20
        la x1, _flt_jr21
        jalr	x21, x1, 0
_flt_jr21:   flt.s      x21, x21, x21
        la x1, _flt_jr22
        jalr	x22, x1, 0
_flt_jr22:   flt.s      x22, x22, x22
        la x1, _flt_jr23
        jalr	x23, x1, 0
_flt_jr23:   flt.s      x23, x23, x23
        la x1, _flt_jr24
        jalr	x24, x1, 0
_flt_jr24:   flt.s      x24, x24, x24
        la x1, _flt_jr25
        jalr	x25, x1, 0
_flt_jr25:   flt.s      x25, x25, x25
        la x1, _flt_jr26
        jalr	x26, x1, 0
_flt_jr26:   flt.s      x26, x26, x26
        la x1, _flt_jr27
        jalr	x27, x1, 0
_flt_jr27:   flt.s      x27, x27, x27
        la x1, _flt_jr28
        jalr	x28, x1, 0
_flt_jr28:   flt.s      x28, x28, x28
        la x1, _flt_jr29
        jalr	x29, x1, 0
_flt_jr29:   flt.s      x29, x29, x29
        la x1, _flt_jr30
        jalr	x30, x1, 0
_flt_jr30:   flt.s      x30, x30, x30
        la x1, _flt_jr31
        jalr	x31, x1, 0
_flt_jr31:   flt.s      x31, x31, x31

        // 25 - jal -> fmadd (rs1, rs2, rs3)
        jal	x0, _fmadd_j0
_fmadd_j0:    fmadd.s      x0, x0, x0, x0
        jal	x1, _fmadd_j1
_fmadd_j1:    fmadd.s      x1, x1, x1, x1
        jal	x2, _fmadd_j2
_fmadd_j2:    fmadd.s      x2, x2, x2, x2
        jal	x3, _fmadd_j3
_fmadd_j3:    fmadd.s      x3, x3, x3, x3
        jal	x4, _fmadd_j4
_fmadd_j4:    fmadd.s      x4, x4, x4, x4
        jal	x5, _fmadd_j5
_fmadd_j5:    fmadd.s      x5, x5, x5, x5
        jal	x6, _fmadd_j6
_fmadd_j6:    fmadd.s      x6, x6, x6, x6
        jal	x7, _fmadd_j7
_fmadd_j7:    fmadd.s      x7, x7, x7, x7
        jal	x8, _fmadd_j8
_fmadd_j8:    fmadd.s      x8, x8, x8, x8
        jal	x9, _fmadd_j9
_fmadd_j9:    fmadd.s      x9, x9, x9, x9
        jal	x10, _fmadd_j10
_fmadd_j10:    fmadd.s      x10, x10, x10, x10
        jal	x11, _fmadd_j11
_fmadd_j11:    fmadd.s      x11, x11, x11, x11
        jal	x12, _fmadd_j12
_fmadd_j12:    fmadd.s      x12, x12, x12, x12
        jal	x13, _fmadd_j13
_fmadd_j13:    fmadd.s      x13, x13, x13, x13
        jal	x14, _fmadd_j14
_fmadd_j14:    fmadd.s      x14, x14, x14, x14
        jal	x15, _fmadd_j15
_fmadd_j15:    fmadd.s      x15, x15, x15, x15
        jal	x16, _fmadd_j16
_fmadd_j16:    fmadd.s      x16, x16, x16, x16
        jal	x17, _fmadd_j17
_fmadd_j17:    fmadd.s      x17, x17, x17, x17
        jal	x18, _fmadd_j18
_fmadd_j18:    fmadd.s      x18, x18, x18, x18
        jal	x19, _fmadd_j19
_fmadd_j19:    fmadd.s      x19, x19, x19, x19
        jal	x20, _fmadd_j20
_fmadd_j20:    fmadd.s      x20, x20, x20, x20
        jal	x21, _fmadd_j21
_fmadd_j21:    fmadd.s      x21, x21, x21, x21
        jal	x22, _fmadd_j22
_fmadd_j22:    fmadd.s      x22, x22, x22, x22
        jal	x23, _fmadd_j23
_fmadd_j23:    fmadd.s      x23, x23, x23, x23
        jal	x24, _fmadd_j24
_fmadd_j24:    fmadd.s      x24, x24, x24, x24
        jal	x25, _fmadd_j25
_fmadd_j25:    fmadd.s      x25, x25, x25, x25
        jal	x26, _fmadd_j26
_fmadd_j26:    fmadd.s      x26, x26, x26, x26
        jal	x27, _fmadd_j27
_fmadd_j27:    fmadd.s      x27, x27, x27, x27
        jal	x28, _fmadd_j28
_fmadd_j28:    fmadd.s      x28, x28, x28, x28
        jal	x29, _fmadd_j29
_fmadd_j29:    fmadd.s      x29, x29, x29, x29
        jal	x30, _fmadd_j30
_fmadd_j30:    fmadd.s      x30, x30, x30, x30
        jal	x31, _fmadd_j31
_fmadd_j31:    fmadd.s      x31, x31, x31, x31

        // 26 - jalr -> fmadd (rs1, rs2, rs3)
        la x1, _fmadd_jr0
        jalr	x0, x1, 0
_fmadd_jr0:   fmadd.s      x0, x0, x0, x0
        la x1, _fmadd_jr1
        jalr	x1, x1, 0
_fmadd_jr1:   fmadd.s      x1, x1, x1, x1
        la x1, _fmadd_jr2
        jalr	x2, x1, 0
_fmadd_jr2:   fmadd.s      x2, x2, x2, x2
        la x1, _fmadd_jr3
        jalr	x3, x1, 0
_fmadd_jr3:   fmadd.s      x3, x3, x3, x3
        la x1, _fmadd_jr4
        jalr	x4, x1, 0
_fmadd_jr4:   fmadd.s      x4, x4, x4, x4
        la x1, _fmadd_jr5
        jalr	x5, x1, 0
_fmadd_jr5:   fmadd.s      x5, x5, x5, x5
        la x1, _fmadd_jr6
        jalr	x6, x1, 0
_fmadd_jr6:   fmadd.s      x6, x6, x6, x6
        la x1, _fmadd_jr7
        jalr	x7, x1, 0
_fmadd_jr7:   fmadd.s      x7, x7, x7, x7
        la x1, _fmadd_jr8
        jalr	x8, x1, 0
_fmadd_jr8:   fmadd.s      x8, x8, x8, x8
        la x1, _fmadd_jr9
        jalr	x9, x1, 0
_fmadd_jr9:   fmadd.s      x9, x9, x9, x9
        la x1, _fmadd_jr10
        jalr	x10, x1, 0
_fmadd_jr10:   fmadd.s      x10, x10, x10, x10
        la x1, _fmadd_jr11
        jalr	x11, x1, 0
_fmadd_jr11:   fmadd.s      x11, x11, x11, x11
        la x1, _fmadd_jr12
        jalr	x12, x1, 0
_fmadd_jr12:   fmadd.s      x12, x12, x12, x12
        la x1, _fmadd_jr13
        jalr	x13, x1, 0
_fmadd_jr13:   fmadd.s      x13, x13, x13, x13
        la x1, _fmadd_jr14
        jalr	x14, x1, 0
_fmadd_jr14:   fmadd.s      x14, x14, x14, x14
        la x1, _fmadd_jr15
        jalr	x15, x1, 0
_fmadd_jr15:   fmadd.s      x15, x15, x15, x15
        la x1, _fmadd_jr16
        jalr	x16, x1, 0
_fmadd_jr16:   fmadd.s      x16, x16, x16, x16
        la x1, _fmadd_jr17
        jalr	x17, x1, 0
_fmadd_jr17:   fmadd.s      x17, x17, x17, x17
        la x1, _fmadd_jr18
        jalr	x18, x1, 0
_fmadd_jr18:   fmadd.s      x18, x18, x18, x18
        la x1, _fmadd_jr19
        jalr	x19, x1, 0
_fmadd_jr19:   fmadd.s      x19, x19, x19, x19
        la x1, _fmadd_jr20
        jalr	x20, x1, 0
_fmadd_jr20:   fmadd.s      x20, x20, x20, x20
        la x1, _fmadd_jr21
        jalr	x21, x1, 0
_fmadd_jr21:   fmadd.s      x21, x21, x21, x21
        la x1, _fmadd_jr22
        jalr	x22, x1, 0
_fmadd_jr22:   fmadd.s      x22, x22, x22, x22
        la x1, _fmadd_jr23
        jalr	x23, x1, 0
_fmadd_jr23:   fmadd.s      x23, x23, x23, x23
        la x1, _fmadd_jr24
        jalr	x24, x1, 0
_fmadd_jr24:   fmadd.s      x24, x24, x24, x24
        la x1, _fmadd_jr25
        jalr	x25, x1, 0
_fmadd_jr25:   fmadd.s      x25, x25, x25, x25
        la x1, _fmadd_jr26
        jalr	x26, x1, 0
_fmadd_jr26:   fmadd.s      x26, x26, x26, x26
        la x1, _fmadd_jr27
        jalr	x27, x1, 0
_fmadd_jr27:   fmadd.s      x27, x27, x27, x27
        la x1, _fmadd_jr28
        jalr	x28, x1, 0
_fmadd_jr28:   fmadd.s      x28, x28, x28, x28
        la x1, _fmadd_jr29
        jalr	x29, x1, 0
_fmadd_jr29:   fmadd.s      x29, x29, x29, x29
        la x1, _fmadd_jr30
        jalr	x30, x1, 0
_fmadd_jr30:   fmadd.s      x30, x30, x30, x30
        la x1, _fmadd_jr31
        jalr	x31, x1, 0
_fmadd_jr31:   fmadd.s      x31, x31, x31, x31

        // 27 - jal -> fmax (rs1, rs2)
        jal	x0, _fmax_j0
_fmax_j0:    fmax.s      x0, x0, x0
        jal	x1, _fmax_j1
_fmax_j1:    fmax.s      x1, x1, x1
        jal	x2, _fmax_j2
_fmax_j2:    fmax.s      x2, x2, x2
        jal	x3, _fmax_j3
_fmax_j3:    fmax.s      x3, x3, x3
        jal	x4, _fmax_j4
_fmax_j4:    fmax.s      x4, x4, x4
        jal	x5, _fmax_j5
_fmax_j5:    fmax.s      x5, x5, x5
        jal	x6, _fmax_j6
_fmax_j6:    fmax.s      x6, x6, x6
        jal	x7, _fmax_j7
_fmax_j7:    fmax.s      x7, x7, x7
        jal	x8, _fmax_j8
_fmax_j8:    fmax.s      x8, x8, x8
        jal	x9, _fmax_j9
_fmax_j9:    fmax.s      x9, x9, x9
        jal	x10, _fmax_j10
_fmax_j10:    fmax.s      x10, x10, x10
        jal	x11, _fmax_j11
_fmax_j11:    fmax.s      x11, x11, x11
        jal	x12, _fmax_j12
_fmax_j12:    fmax.s      x12, x12, x12
        jal	x13, _fmax_j13
_fmax_j13:    fmax.s      x13, x13, x13
        jal	x14, _fmax_j14
_fmax_j14:    fmax.s      x14, x14, x14
        jal	x15, _fmax_j15
_fmax_j15:    fmax.s      x15, x15, x15
        jal	x16, _fmax_j16
_fmax_j16:    fmax.s      x16, x16, x16
        jal	x17, _fmax_j17
_fmax_j17:    fmax.s      x17, x17, x17
        jal	x18, _fmax_j18
_fmax_j18:    fmax.s      x18, x18, x18
        jal	x19, _fmax_j19
_fmax_j19:    fmax.s      x19, x19, x19
        jal	x20, _fmax_j20
_fmax_j20:    fmax.s      x20, x20, x20
        jal	x21, _fmax_j21
_fmax_j21:    fmax.s      x21, x21, x21
        jal	x22, _fmax_j22
_fmax_j22:    fmax.s      x22, x22, x22
        jal	x23, _fmax_j23
_fmax_j23:    fmax.s      x23, x23, x23
        jal	x24, _fmax_j24
_fmax_j24:    fmax.s      x24, x24, x24
        jal	x25, _fmax_j25
_fmax_j25:    fmax.s      x25, x25, x25
        jal	x26, _fmax_j26
_fmax_j26:    fmax.s      x26, x26, x26
        jal	x27, _fmax_j27
_fmax_j27:    fmax.s      x27, x27, x27
        jal	x28, _fmax_j28
_fmax_j28:    fmax.s      x28, x28, x28
        jal	x29, _fmax_j29
_fmax_j29:    fmax.s      x29, x29, x29
        jal	x30, _fmax_j30
_fmax_j30:    fmax.s      x30, x30, x30
        jal	x31, _fmax_j31
_fmax_j31:    fmax.s      x31, x31, x31

        // 28 - jalr -> fmax (rs1, rs2)
        la x1, _fmax_jr0
        jalr	x0, x1, 0
_fmax_jr0:   fmax.s      x0, x0, x0
        la x1, _fmax_jr1
        jalr	x1, x1, 0
_fmax_jr1:   fmax.s      x1, x1, x1
        la x1, _fmax_jr2
        jalr	x2, x1, 0
_fmax_jr2:   fmax.s      x2, x2, x2
        la x1, _fmax_jr3
        jalr	x3, x1, 0
_fmax_jr3:   fmax.s      x3, x3, x3
        la x1, _fmax_jr4
        jalr	x4, x1, 0
_fmax_jr4:   fmax.s      x4, x4, x4
        la x1, _fmax_jr5
        jalr	x5, x1, 0
_fmax_jr5:   fmax.s      x5, x5, x5
        la x1, _fmax_jr6
        jalr	x6, x1, 0
_fmax_jr6:   fmax.s      x6, x6, x6
        la x1, _fmax_jr7
        jalr	x7, x1, 0
_fmax_jr7:   fmax.s      x7, x7, x7
        la x1, _fmax_jr8
        jalr	x8, x1, 0
_fmax_jr8:   fmax.s      x8, x8, x8
        la x1, _fmax_jr9
        jalr	x9, x1, 0
_fmax_jr9:   fmax.s      x9, x9, x9
        la x1, _fmax_jr10
        jalr	x10, x1, 0
_fmax_jr10:   fmax.s      x10, x10, x10
        la x1, _fmax_jr11
        jalr	x11, x1, 0
_fmax_jr11:   fmax.s      x11, x11, x11
        la x1, _fmax_jr12
        jalr	x12, x1, 0
_fmax_jr12:   fmax.s      x12, x12, x12
        la x1, _fmax_jr13
        jalr	x13, x1, 0
_fmax_jr13:   fmax.s      x13, x13, x13
        la x1, _fmax_jr14
        jalr	x14, x1, 0
_fmax_jr14:   fmax.s      x14, x14, x14
        la x1, _fmax_jr15
        jalr	x15, x1, 0
_fmax_jr15:   fmax.s      x15, x15, x15
        la x1, _fmax_jr16
        jalr	x16, x1, 0
_fmax_jr16:   fmax.s      x16, x16, x16
        la x1, _fmax_jr17
        jalr	x17, x1, 0
_fmax_jr17:   fmax.s      x17, x17, x17
        la x1, _fmax_jr18
        jalr	x18, x1, 0
_fmax_jr18:   fmax.s      x18, x18, x18
        la x1, _fmax_jr19
        jalr	x19, x1, 0
_fmax_jr19:   fmax.s      x19, x19, x19
        la x1, _fmax_jr20
        jalr	x20, x1, 0
_fmax_jr20:   fmax.s      x20, x20, x20
        la x1, _fmax_jr21
        jalr	x21, x1, 0
_fmax_jr21:   fmax.s      x21, x21, x21
        la x1, _fmax_jr22
        jalr	x22, x1, 0
_fmax_jr22:   fmax.s      x22, x22, x22
        la x1, _fmax_jr23
        jalr	x23, x1, 0
_fmax_jr23:   fmax.s      x23, x23, x23
        la x1, _fmax_jr24
        jalr	x24, x1, 0
_fmax_jr24:   fmax.s      x24, x24, x24
        la x1, _fmax_jr25
        jalr	x25, x1, 0
_fmax_jr25:   fmax.s      x25, x25, x25
        la x1, _fmax_jr26
        jalr	x26, x1, 0
_fmax_jr26:   fmax.s      x26, x26, x26
        la x1, _fmax_jr27
        jalr	x27, x1, 0
_fmax_jr27:   fmax.s      x27, x27, x27
        la x1, _fmax_jr28
        jalr	x28, x1, 0
_fmax_jr28:   fmax.s      x28, x28, x28
        la x1, _fmax_jr29
        jalr	x29, x1, 0
_fmax_jr29:   fmax.s      x29, x29, x29
        la x1, _fmax_jr30
        jalr	x30, x1, 0
_fmax_jr30:   fmax.s      x30, x30, x30
        la x1, _fmax_jr31
        jalr	x31, x1, 0
_fmax_jr31:   fmax.s      x31, x31, x31

        // 29 - jal -> fmin (rs1, rs2)
        jal	x0, _fmin_j0
_fmin_j0:    fmin.s      x0, x0, x0
        jal	x1, _fmin_j1
_fmin_j1:    fmin.s      x1, x1, x1
        jal	x2, _fmin_j2
_fmin_j2:    fmin.s      x2, x2, x2
        jal	x3, _fmin_j3
_fmin_j3:    fmin.s      x3, x3, x3
        jal	x4, _fmin_j4
_fmin_j4:    fmin.s      x4, x4, x4
        jal	x5, _fmin_j5
_fmin_j5:    fmin.s      x5, x5, x5
        jal	x6, _fmin_j6
_fmin_j6:    fmin.s      x6, x6, x6
        jal	x7, _fmin_j7
_fmin_j7:    fmin.s      x7, x7, x7
        jal	x8, _fmin_j8
_fmin_j8:    fmin.s      x8, x8, x8
        jal	x9, _fmin_j9
_fmin_j9:    fmin.s      x9, x9, x9
        jal	x10, _fmin_j10
_fmin_j10:    fmin.s      x10, x10, x10
        jal	x11, _fmin_j11
_fmin_j11:    fmin.s      x11, x11, x11
        jal	x12, _fmin_j12
_fmin_j12:    fmin.s      x12, x12, x12
        jal	x13, _fmin_j13
_fmin_j13:    fmin.s      x13, x13, x13
        jal	x14, _fmin_j14
_fmin_j14:    fmin.s      x14, x14, x14
        jal	x15, _fmin_j15
_fmin_j15:    fmin.s      x15, x15, x15
        jal	x16, _fmin_j16
_fmin_j16:    fmin.s      x16, x16, x16
        jal	x17, _fmin_j17
_fmin_j17:    fmin.s      x17, x17, x17
        jal	x18, _fmin_j18
_fmin_j18:    fmin.s      x18, x18, x18
        jal	x19, _fmin_j19
_fmin_j19:    fmin.s      x19, x19, x19
        jal	x20, _fmin_j20
_fmin_j20:    fmin.s      x20, x20, x20
        jal	x21, _fmin_j21
_fmin_j21:    fmin.s      x21, x21, x21
        jal	x22, _fmin_j22
_fmin_j22:    fmin.s      x22, x22, x22
        jal	x23, _fmin_j23
_fmin_j23:    fmin.s      x23, x23, x23
        jal	x24, _fmin_j24
_fmin_j24:    fmin.s      x24, x24, x24
        jal	x25, _fmin_j25
_fmin_j25:    fmin.s      x25, x25, x25
        jal	x26, _fmin_j26
_fmin_j26:    fmin.s      x26, x26, x26
        jal	x27, _fmin_j27
_fmin_j27:    fmin.s      x27, x27, x27
        jal	x28, _fmin_j28
_fmin_j28:    fmin.s      x28, x28, x28
        jal	x29, _fmin_j29
_fmin_j29:    fmin.s      x29, x29, x29
        jal	x30, _fmin_j30
_fmin_j30:    fmin.s      x30, x30, x30
        jal	x31, _fmin_j31
_fmin_j31:    fmin.s      x31, x31, x31

        // 30 - jalr -> fmin (rs1, rs2)
        la x1, _fmin_jr0
        jalr	x0, x1, 0
_fmin_jr0:   fmin.s      x0, x0, x0
        la x1, _fmin_jr1
        jalr	x1, x1, 0
_fmin_jr1:   fmin.s      x1, x1, x1
        la x1, _fmin_jr2
        jalr	x2, x1, 0
_fmin_jr2:   fmin.s      x2, x2, x2
        la x1, _fmin_jr3
        jalr	x3, x1, 0
_fmin_jr3:   fmin.s      x3, x3, x3
        la x1, _fmin_jr4
        jalr	x4, x1, 0
_fmin_jr4:   fmin.s      x4, x4, x4
        la x1, _fmin_jr5
        jalr	x5, x1, 0
_fmin_jr5:   fmin.s      x5, x5, x5
        la x1, _fmin_jr6
        jalr	x6, x1, 0
_fmin_jr6:   fmin.s      x6, x6, x6
        la x1, _fmin_jr7
        jalr	x7, x1, 0
_fmin_jr7:   fmin.s      x7, x7, x7
        la x1, _fmin_jr8
        jalr	x8, x1, 0
_fmin_jr8:   fmin.s      x8, x8, x8
        la x1, _fmin_jr9
        jalr	x9, x1, 0
_fmin_jr9:   fmin.s      x9, x9, x9
        la x1, _fmin_jr10
        jalr	x10, x1, 0
_fmin_jr10:   fmin.s      x10, x10, x10
        la x1, _fmin_jr11
        jalr	x11, x1, 0
_fmin_jr11:   fmin.s      x11, x11, x11
        la x1, _fmin_jr12
        jalr	x12, x1, 0
_fmin_jr12:   fmin.s      x12, x12, x12
        la x1, _fmin_jr13
        jalr	x13, x1, 0
_fmin_jr13:   fmin.s      x13, x13, x13
        la x1, _fmin_jr14
        jalr	x14, x1, 0
_fmin_jr14:   fmin.s      x14, x14, x14
        la x1, _fmin_jr15
        jalr	x15, x1, 0
_fmin_jr15:   fmin.s      x15, x15, x15
        la x1, _fmin_jr16
        jalr	x16, x1, 0
_fmin_jr16:   fmin.s      x16, x16, x16
        la x1, _fmin_jr17
        jalr	x17, x1, 0
_fmin_jr17:   fmin.s      x17, x17, x17
        la x1, _fmin_jr18
        jalr	x18, x1, 0
_fmin_jr18:   fmin.s      x18, x18, x18
        la x1, _fmin_jr19
        jalr	x19, x1, 0
_fmin_jr19:   fmin.s      x19, x19, x19
        la x1, _fmin_jr20
        jalr	x20, x1, 0
_fmin_jr20:   fmin.s      x20, x20, x20
        la x1, _fmin_jr21
        jalr	x21, x1, 0
_fmin_jr21:   fmin.s      x21, x21, x21
        la x1, _fmin_jr22
        jalr	x22, x1, 0
_fmin_jr22:   fmin.s      x22, x22, x22
        la x1, _fmin_jr23
        jalr	x23, x1, 0
_fmin_jr23:   fmin.s      x23, x23, x23
        la x1, _fmin_jr24
        jalr	x24, x1, 0
_fmin_jr24:   fmin.s      x24, x24, x24
        la x1, _fmin_jr25
        jalr	x25, x1, 0
_fmin_jr25:   fmin.s      x25, x25, x25
        la x1, _fmin_jr26
        jalr	x26, x1, 0
_fmin_jr26:   fmin.s      x26, x26, x26
        la x1, _fmin_jr27
        jalr	x27, x1, 0
_fmin_jr27:   fmin.s      x27, x27, x27
        la x1, _fmin_jr28
        jalr	x28, x1, 0
_fmin_jr28:   fmin.s      x28, x28, x28
        la x1, _fmin_jr29
        jalr	x29, x1, 0
_fmin_jr29:   fmin.s      x29, x29, x29
        la x1, _fmin_jr30
        jalr	x30, x1, 0
_fmin_jr30:   fmin.s      x30, x30, x30
        la x1, _fmin_jr31
        jalr	x31, x1, 0
_fmin_jr31:   fmin.s      x31, x31, x31

        // 31 - jal -> fmsub (rs1, rs2, rs3)
        jal	x0, _fmsub_j0
_fmsub_j0:    fmsub.s      x0, x0, x0, x0
        jal	x1, _fmsub_j1
_fmsub_j1:    fmsub.s      x1, x1, x1, x1
        jal	x2, _fmsub_j2
_fmsub_j2:    fmsub.s      x2, x2, x2, x2
        jal	x3, _fmsub_j3
_fmsub_j3:    fmsub.s      x3, x3, x3, x3
        jal	x4, _fmsub_j4
_fmsub_j4:    fmsub.s      x4, x4, x4, x4
        jal	x5, _fmsub_j5
_fmsub_j5:    fmsub.s      x5, x5, x5, x5
        jal	x6, _fmsub_j6
_fmsub_j6:    fmsub.s      x6, x6, x6, x6
        jal	x7, _fmsub_j7
_fmsub_j7:    fmsub.s      x7, x7, x7, x7
        jal	x8, _fmsub_j8
_fmsub_j8:    fmsub.s      x8, x8, x8, x8
        jal	x9, _fmsub_j9
_fmsub_j9:    fmsub.s      x9, x9, x9, x9
        jal	x10, _fmsub_j10
_fmsub_j10:    fmsub.s      x10, x10, x10, x10
        jal	x11, _fmsub_j11
_fmsub_j11:    fmsub.s      x11, x11, x11, x11
        jal	x12, _fmsub_j12
_fmsub_j12:    fmsub.s      x12, x12, x12, x12
        jal	x13, _fmsub_j13
_fmsub_j13:    fmsub.s      x13, x13, x13, x13
        jal	x14, _fmsub_j14
_fmsub_j14:    fmsub.s      x14, x14, x14, x14
        jal	x15, _fmsub_j15
_fmsub_j15:    fmsub.s      x15, x15, x15, x15
        jal	x16, _fmsub_j16
_fmsub_j16:    fmsub.s      x16, x16, x16, x16
        jal	x17, _fmsub_j17
_fmsub_j17:    fmsub.s      x17, x17, x17, x17
        jal	x18, _fmsub_j18
_fmsub_j18:    fmsub.s      x18, x18, x18, x18
        jal	x19, _fmsub_j19
_fmsub_j19:    fmsub.s      x19, x19, x19, x19
        jal	x20, _fmsub_j20
_fmsub_j20:    fmsub.s      x20, x20, x20, x20
        jal	x21, _fmsub_j21
_fmsub_j21:    fmsub.s      x21, x21, x21, x21
        jal	x22, _fmsub_j22
_fmsub_j22:    fmsub.s      x22, x22, x22, x22
        jal	x23, _fmsub_j23
_fmsub_j23:    fmsub.s      x23, x23, x23, x23
        jal	x24, _fmsub_j24
_fmsub_j24:    fmsub.s      x24, x24, x24, x24
        jal	x25, _fmsub_j25
_fmsub_j25:    fmsub.s      x25, x25, x25, x25
        jal	x26, _fmsub_j26
_fmsub_j26:    fmsub.s      x26, x26, x26, x26
        jal	x27, _fmsub_j27
_fmsub_j27:    fmsub.s      x27, x27, x27, x27
        jal	x28, _fmsub_j28
_fmsub_j28:    fmsub.s      x28, x28, x28, x28
        jal	x29, _fmsub_j29
_fmsub_j29:    fmsub.s      x29, x29, x29, x29
        jal	x30, _fmsub_j30
_fmsub_j30:    fmsub.s      x30, x30, x30, x30
        jal	x31, _fmsub_j31
_fmsub_j31:    fmsub.s      x31, x31, x31, x31

        // 32 - jalr -> fmsub (rs1, rs2, rs3)
        la x1, _fmsub_jr0
        jalr	x0, x1, 0
_fmsub_jr0:   fmsub.s      x0, x0, x0, x0
        la x1, _fmsub_jr1
        jalr	x1, x1, 0
_fmsub_jr1:   fmsub.s      x1, x1, x1, x1
        la x1, _fmsub_jr2
        jalr	x2, x1, 0
_fmsub_jr2:   fmsub.s      x2, x2, x2, x2
        la x1, _fmsub_jr3
        jalr	x3, x1, 0
_fmsub_jr3:   fmsub.s      x3, x3, x3, x3
        la x1, _fmsub_jr4
        jalr	x4, x1, 0
_fmsub_jr4:   fmsub.s      x4, x4, x4, x4
        la x1, _fmsub_jr5
        jalr	x5, x1, 0
_fmsub_jr5:   fmsub.s      x5, x5, x5, x5
        la x1, _fmsub_jr6
        jalr	x6, x1, 0
_fmsub_jr6:   fmsub.s      x6, x6, x6, x6
        la x1, _fmsub_jr7
        jalr	x7, x1, 0
_fmsub_jr7:   fmsub.s      x7, x7, x7, x7
        la x1, _fmsub_jr8
        jalr	x8, x1, 0
_fmsub_jr8:   fmsub.s      x8, x8, x8, x8
        la x1, _fmsub_jr9
        jalr	x9, x1, 0
_fmsub_jr9:   fmsub.s      x9, x9, x9, x9
        la x1, _fmsub_jr10
        jalr	x10, x1, 0
_fmsub_jr10:   fmsub.s      x10, x10, x10, x10
        la x1, _fmsub_jr11
        jalr	x11, x1, 0
_fmsub_jr11:   fmsub.s      x11, x11, x11, x11
        la x1, _fmsub_jr12
        jalr	x12, x1, 0
_fmsub_jr12:   fmsub.s      x12, x12, x12, x12
        la x1, _fmsub_jr13
        jalr	x13, x1, 0
_fmsub_jr13:   fmsub.s      x13, x13, x13, x13
        la x1, _fmsub_jr14
        jalr	x14, x1, 0
_fmsub_jr14:   fmsub.s      x14, x14, x14, x14
        la x1, _fmsub_jr15
        jalr	x15, x1, 0
_fmsub_jr15:   fmsub.s      x15, x15, x15, x15
        la x1, _fmsub_jr16
        jalr	x16, x1, 0
_fmsub_jr16:   fmsub.s      x16, x16, x16, x16
        la x1, _fmsub_jr17
        jalr	x17, x1, 0
_fmsub_jr17:   fmsub.s      x17, x17, x17, x17
        la x1, _fmsub_jr18
        jalr	x18, x1, 0
_fmsub_jr18:   fmsub.s      x18, x18, x18, x18
        la x1, _fmsub_jr19
        jalr	x19, x1, 0
_fmsub_jr19:   fmsub.s      x19, x19, x19, x19
        la x1, _fmsub_jr20
        jalr	x20, x1, 0
_fmsub_jr20:   fmsub.s      x20, x20, x20, x20
        la x1, _fmsub_jr21
        jalr	x21, x1, 0
_fmsub_jr21:   fmsub.s      x21, x21, x21, x21
        la x1, _fmsub_jr22
        jalr	x22, x1, 0
_fmsub_jr22:   fmsub.s      x22, x22, x22, x22
        la x1, _fmsub_jr23
        jalr	x23, x1, 0
_fmsub_jr23:   fmsub.s      x23, x23, x23, x23
        la x1, _fmsub_jr24
        jalr	x24, x1, 0
_fmsub_jr24:   fmsub.s      x24, x24, x24, x24
        la x1, _fmsub_jr25
        jalr	x25, x1, 0
_fmsub_jr25:   fmsub.s      x25, x25, x25, x25
        la x1, _fmsub_jr26
        jalr	x26, x1, 0
_fmsub_jr26:   fmsub.s      x26, x26, x26, x26
        la x1, _fmsub_jr27
        jalr	x27, x1, 0
_fmsub_jr27:   fmsub.s      x27, x27, x27, x27
        la x1, _fmsub_jr28
        jalr	x28, x1, 0
_fmsub_jr28:   fmsub.s      x28, x28, x28, x28
        la x1, _fmsub_jr29
        jalr	x29, x1, 0
_fmsub_jr29:   fmsub.s      x29, x29, x29, x29
        la x1, _fmsub_jr30
        jalr	x30, x1, 0
_fmsub_jr30:   fmsub.s      x30, x30, x30, x30
        la x1, _fmsub_jr31
        jalr	x31, x1, 0
_fmsub_jr31:   fmsub.s      x31, x31, x31, x31

        // 33 - jal -> fmul (rs1, rs2)
        jal	x0, _fmul_j0
_fmul_j0:    fmul.s      x0, x0, x0
        jal	x1, _fmul_j1
_fmul_j1:    fmul.s      x1, x1, x1
        jal	x2, _fmul_j2
_fmul_j2:    fmul.s      x2, x2, x2
        jal	x3, _fmul_j3
_fmul_j3:    fmul.s      x3, x3, x3
        jal	x4, _fmul_j4
_fmul_j4:    fmul.s      x4, x4, x4
        jal	x5, _fmul_j5
_fmul_j5:    fmul.s      x5, x5, x5
        jal	x6, _fmul_j6
_fmul_j6:    fmul.s      x6, x6, x6
        jal	x7, _fmul_j7
_fmul_j7:    fmul.s      x7, x7, x7
        jal	x8, _fmul_j8
_fmul_j8:    fmul.s      x8, x8, x8
        jal	x9, _fmul_j9
_fmul_j9:    fmul.s      x9, x9, x9
        jal	x10, _fmul_j10
_fmul_j10:    fmul.s      x10, x10, x10
        jal	x11, _fmul_j11
_fmul_j11:    fmul.s      x11, x11, x11
        jal	x12, _fmul_j12
_fmul_j12:    fmul.s      x12, x12, x12
        jal	x13, _fmul_j13
_fmul_j13:    fmul.s      x13, x13, x13
        jal	x14, _fmul_j14
_fmul_j14:    fmul.s      x14, x14, x14
        jal	x15, _fmul_j15
_fmul_j15:    fmul.s      x15, x15, x15
        jal	x16, _fmul_j16
_fmul_j16:    fmul.s      x16, x16, x16
        jal	x17, _fmul_j17
_fmul_j17:    fmul.s      x17, x17, x17
        jal	x18, _fmul_j18
_fmul_j18:    fmul.s      x18, x18, x18
        jal	x19, _fmul_j19
_fmul_j19:    fmul.s      x19, x19, x19
        jal	x20, _fmul_j20
_fmul_j20:    fmul.s      x20, x20, x20
        jal	x21, _fmul_j21
_fmul_j21:    fmul.s      x21, x21, x21
        jal	x22, _fmul_j22
_fmul_j22:    fmul.s      x22, x22, x22
        jal	x23, _fmul_j23
_fmul_j23:    fmul.s      x23, x23, x23
        jal	x24, _fmul_j24
_fmul_j24:    fmul.s      x24, x24, x24
        jal	x25, _fmul_j25
_fmul_j25:    fmul.s      x25, x25, x25
        jal	x26, _fmul_j26
_fmul_j26:    fmul.s      x26, x26, x26
        jal	x27, _fmul_j27
_fmul_j27:    fmul.s      x27, x27, x27
        jal	x28, _fmul_j28
_fmul_j28:    fmul.s      x28, x28, x28
        jal	x29, _fmul_j29
_fmul_j29:    fmul.s      x29, x29, x29
        jal	x30, _fmul_j30
_fmul_j30:    fmul.s      x30, x30, x30
        jal	x31, _fmul_j31
_fmul_j31:    fmul.s      x31, x31, x31

        // 34 - jalr -> fmul (rs1, rs2)
        la x1, _fmul_jr0
        jalr	x0, x1, 0
_fmul_jr0:   fmul.s      x0, x0, x0
        la x1, _fmul_jr1
        jalr	x1, x1, 0
_fmul_jr1:   fmul.s      x1, x1, x1
        la x1, _fmul_jr2
        jalr	x2, x1, 0
_fmul_jr2:   fmul.s      x2, x2, x2
        la x1, _fmul_jr3
        jalr	x3, x1, 0
_fmul_jr3:   fmul.s      x3, x3, x3
        la x1, _fmul_jr4
        jalr	x4, x1, 0
_fmul_jr4:   fmul.s      x4, x4, x4
        la x1, _fmul_jr5
        jalr	x5, x1, 0
_fmul_jr5:   fmul.s      x5, x5, x5
        la x1, _fmul_jr6
        jalr	x6, x1, 0
_fmul_jr6:   fmul.s      x6, x6, x6
        la x1, _fmul_jr7
        jalr	x7, x1, 0
_fmul_jr7:   fmul.s      x7, x7, x7
        la x1, _fmul_jr8
        jalr	x8, x1, 0
_fmul_jr8:   fmul.s      x8, x8, x8
        la x1, _fmul_jr9
        jalr	x9, x1, 0
_fmul_jr9:   fmul.s      x9, x9, x9
        la x1, _fmul_jr10
        jalr	x10, x1, 0
_fmul_jr10:   fmul.s      x10, x10, x10
        la x1, _fmul_jr11
        jalr	x11, x1, 0
_fmul_jr11:   fmul.s      x11, x11, x11
        la x1, _fmul_jr12
        jalr	x12, x1, 0
_fmul_jr12:   fmul.s      x12, x12, x12
        la x1, _fmul_jr13
        jalr	x13, x1, 0
_fmul_jr13:   fmul.s      x13, x13, x13
        la x1, _fmul_jr14
        jalr	x14, x1, 0
_fmul_jr14:   fmul.s      x14, x14, x14
        la x1, _fmul_jr15
        jalr	x15, x1, 0
_fmul_jr15:   fmul.s      x15, x15, x15
        la x1, _fmul_jr16
        jalr	x16, x1, 0
_fmul_jr16:   fmul.s      x16, x16, x16
        la x1, _fmul_jr17
        jalr	x17, x1, 0
_fmul_jr17:   fmul.s      x17, x17, x17
        la x1, _fmul_jr18
        jalr	x18, x1, 0
_fmul_jr18:   fmul.s      x18, x18, x18
        la x1, _fmul_jr19
        jalr	x19, x1, 0
_fmul_jr19:   fmul.s      x19, x19, x19
        la x1, _fmul_jr20
        jalr	x20, x1, 0
_fmul_jr20:   fmul.s      x20, x20, x20
        la x1, _fmul_jr21
        jalr	x21, x1, 0
_fmul_jr21:   fmul.s      x21, x21, x21
        la x1, _fmul_jr22
        jalr	x22, x1, 0
_fmul_jr22:   fmul.s      x22, x22, x22
        la x1, _fmul_jr23
        jalr	x23, x1, 0
_fmul_jr23:   fmul.s      x23, x23, x23
        la x1, _fmul_jr24
        jalr	x24, x1, 0
_fmul_jr24:   fmul.s      x24, x24, x24
        la x1, _fmul_jr25
        jalr	x25, x1, 0
_fmul_jr25:   fmul.s      x25, x25, x25
        la x1, _fmul_jr26
        jalr	x26, x1, 0
_fmul_jr26:   fmul.s      x26, x26, x26
        la x1, _fmul_jr27
        jalr	x27, x1, 0
_fmul_jr27:   fmul.s      x27, x27, x27
        la x1, _fmul_jr28
        jalr	x28, x1, 0
_fmul_jr28:   fmul.s      x28, x28, x28
        la x1, _fmul_jr29
        jalr	x29, x1, 0
_fmul_jr29:   fmul.s      x29, x29, x29
        la x1, _fmul_jr30
        jalr	x30, x1, 0
_fmul_jr30:   fmul.s      x30, x30, x30
        la x1, _fmul_jr31
        jalr	x31, x1, 0
_fmul_jr31:   fmul.s      x31, x31, x31

        // 35 - jal -> fnmadd (rs1, rs2, rs3)
        jal	x0, _fnmadd_j0
_fnmadd_j0:    fnmadd.s      x0, x0, x0, x0
        jal	x1, _fnmadd_j1
_fnmadd_j1:    fnmadd.s      x1, x1, x1, x1
        jal	x2, _fnmadd_j2
_fnmadd_j2:    fnmadd.s      x2, x2, x2, x2
        jal	x3, _fnmadd_j3
_fnmadd_j3:    fnmadd.s      x3, x3, x3, x3
        jal	x4, _fnmadd_j4
_fnmadd_j4:    fnmadd.s      x4, x4, x4, x4
        jal	x5, _fnmadd_j5
_fnmadd_j5:    fnmadd.s      x5, x5, x5, x5
        jal	x6, _fnmadd_j6
_fnmadd_j6:    fnmadd.s      x6, x6, x6, x6
        jal	x7, _fnmadd_j7
_fnmadd_j7:    fnmadd.s      x7, x7, x7, x7
        jal	x8, _fnmadd_j8
_fnmadd_j8:    fnmadd.s      x8, x8, x8, x8
        jal	x9, _fnmadd_j9
_fnmadd_j9:    fnmadd.s      x9, x9, x9, x9
        jal	x10, _fnmadd_j10
_fnmadd_j10:    fnmadd.s      x10, x10, x10, x10
        jal	x11, _fnmadd_j11
_fnmadd_j11:    fnmadd.s      x11, x11, x11, x11
        jal	x12, _fnmadd_j12
_fnmadd_j12:    fnmadd.s      x12, x12, x12, x12
        jal	x13, _fnmadd_j13
_fnmadd_j13:    fnmadd.s      x13, x13, x13, x13
        jal	x14, _fnmadd_j14
_fnmadd_j14:    fnmadd.s      x14, x14, x14, x14
        jal	x15, _fnmadd_j15
_fnmadd_j15:    fnmadd.s      x15, x15, x15, x15
        jal	x16, _fnmadd_j16
_fnmadd_j16:    fnmadd.s      x16, x16, x16, x16
        jal	x17, _fnmadd_j17
_fnmadd_j17:    fnmadd.s      x17, x17, x17, x17
        jal	x18, _fnmadd_j18
_fnmadd_j18:    fnmadd.s      x18, x18, x18, x18
        jal	x19, _fnmadd_j19
_fnmadd_j19:    fnmadd.s      x19, x19, x19, x19
        jal	x20, _fnmadd_j20
_fnmadd_j20:    fnmadd.s      x20, x20, x20, x20
        jal	x21, _fnmadd_j21
_fnmadd_j21:    fnmadd.s      x21, x21, x21, x21
        jal	x22, _fnmadd_j22
_fnmadd_j22:    fnmadd.s      x22, x22, x22, x22
        jal	x23, _fnmadd_j23
_fnmadd_j23:    fnmadd.s      x23, x23, x23, x23
        jal	x24, _fnmadd_j24
_fnmadd_j24:    fnmadd.s      x24, x24, x24, x24
        jal	x25, _fnmadd_j25
_fnmadd_j25:    fnmadd.s      x25, x25, x25, x25
        jal	x26, _fnmadd_j26
_fnmadd_j26:    fnmadd.s      x26, x26, x26, x26
        jal	x27, _fnmadd_j27
_fnmadd_j27:    fnmadd.s      x27, x27, x27, x27
        jal	x28, _fnmadd_j28
_fnmadd_j28:    fnmadd.s      x28, x28, x28, x28
        jal	x29, _fnmadd_j29
_fnmadd_j29:    fnmadd.s      x29, x29, x29, x29
        jal	x30, _fnmadd_j30
_fnmadd_j30:    fnmadd.s      x30, x30, x30, x30
        jal	x31, _fnmadd_j31
_fnmadd_j31:    fnmadd.s      x31, x31, x31, x31

        // 36 - jalr -> fnmadd (rs1, rs2, rs3)
        la x1, _fnmadd_jr0
        jalr	x0, x1, 0
_fnmadd_jr0:   fnmadd.s      x0, x0, x0, x0
        la x1, _fnmadd_jr1
        jalr	x1, x1, 0
_fnmadd_jr1:   fnmadd.s      x1, x1, x1, x1
        la x1, _fnmadd_jr2
        jalr	x2, x1, 0
_fnmadd_jr2:   fnmadd.s      x2, x2, x2, x2
        la x1, _fnmadd_jr3
        jalr	x3, x1, 0
_fnmadd_jr3:   fnmadd.s      x3, x3, x3, x3
        la x1, _fnmadd_jr4
        jalr	x4, x1, 0
_fnmadd_jr4:   fnmadd.s      x4, x4, x4, x4
        la x1, _fnmadd_jr5
        jalr	x5, x1, 0
_fnmadd_jr5:   fnmadd.s      x5, x5, x5, x5
        la x1, _fnmadd_jr6
        jalr	x6, x1, 0
_fnmadd_jr6:   fnmadd.s      x6, x6, x6, x6
        la x1, _fnmadd_jr7
        jalr	x7, x1, 0
_fnmadd_jr7:   fnmadd.s      x7, x7, x7, x7
        la x1, _fnmadd_jr8
        jalr	x8, x1, 0
_fnmadd_jr8:   fnmadd.s      x8, x8, x8, x8
        la x1, _fnmadd_jr9
        jalr	x9, x1, 0
_fnmadd_jr9:   fnmadd.s      x9, x9, x9, x9
        la x1, _fnmadd_jr10
        jalr	x10, x1, 0
_fnmadd_jr10:   fnmadd.s      x10, x10, x10, x10
        la x1, _fnmadd_jr11
        jalr	x11, x1, 0
_fnmadd_jr11:   fnmadd.s      x11, x11, x11, x11
        la x1, _fnmadd_jr12
        jalr	x12, x1, 0
_fnmadd_jr12:   fnmadd.s      x12, x12, x12, x12
        la x1, _fnmadd_jr13
        jalr	x13, x1, 0
_fnmadd_jr13:   fnmadd.s      x13, x13, x13, x13
        la x1, _fnmadd_jr14
        jalr	x14, x1, 0
_fnmadd_jr14:   fnmadd.s      x14, x14, x14, x14
        la x1, _fnmadd_jr15
        jalr	x15, x1, 0
_fnmadd_jr15:   fnmadd.s      x15, x15, x15, x15
        la x1, _fnmadd_jr16
        jalr	x16, x1, 0
_fnmadd_jr16:   fnmadd.s      x16, x16, x16, x16
        la x1, _fnmadd_jr17
        jalr	x17, x1, 0
_fnmadd_jr17:   fnmadd.s      x17, x17, x17, x17
        la x1, _fnmadd_jr18
        jalr	x18, x1, 0
_fnmadd_jr18:   fnmadd.s      x18, x18, x18, x18
        la x1, _fnmadd_jr19
        jalr	x19, x1, 0
_fnmadd_jr19:   fnmadd.s      x19, x19, x19, x19
        la x1, _fnmadd_jr20
        jalr	x20, x1, 0
_fnmadd_jr20:   fnmadd.s      x20, x20, x20, x20
        la x1, _fnmadd_jr21
        jalr	x21, x1, 0
_fnmadd_jr21:   fnmadd.s      x21, x21, x21, x21
        la x1, _fnmadd_jr22
        jalr	x22, x1, 0
_fnmadd_jr22:   fnmadd.s      x22, x22, x22, x22
        la x1, _fnmadd_jr23
        jalr	x23, x1, 0
_fnmadd_jr23:   fnmadd.s      x23, x23, x23, x23
        la x1, _fnmadd_jr24
        jalr	x24, x1, 0
_fnmadd_jr24:   fnmadd.s      x24, x24, x24, x24
        la x1, _fnmadd_jr25
        jalr	x25, x1, 0
_fnmadd_jr25:   fnmadd.s      x25, x25, x25, x25
        la x1, _fnmadd_jr26
        jalr	x26, x1, 0
_fnmadd_jr26:   fnmadd.s      x26, x26, x26, x26
        la x1, _fnmadd_jr27
        jalr	x27, x1, 0
_fnmadd_jr27:   fnmadd.s      x27, x27, x27, x27
        la x1, _fnmadd_jr28
        jalr	x28, x1, 0
_fnmadd_jr28:   fnmadd.s      x28, x28, x28, x28
        la x1, _fnmadd_jr29
        jalr	x29, x1, 0
_fnmadd_jr29:   fnmadd.s      x29, x29, x29, x29
        la x1, _fnmadd_jr30
        jalr	x30, x1, 0
_fnmadd_jr30:   fnmadd.s      x30, x30, x30, x30
        la x1, _fnmadd_jr31
        jalr	x31, x1, 0
_fnmadd_jr31:   fnmadd.s      x31, x31, x31, x31

        // 37 - jalr -> fnmsub (rs1, rs2, rs3)
        jal	x0, _fnmsub_j0
_fnmsub_j0:    fnmsub.s      x0, x0, x0, x0
        jal	x1, _fnmsub_j1
_fnmsub_j1:    fnmsub.s      x1, x1, x1, x1
        jal	x2, _fnmsub_j2
_fnmsub_j2:    fnmsub.s      x2, x2, x2, x2
        jal	x3, _fnmsub_j3
_fnmsub_j3:    fnmsub.s      x3, x3, x3, x3
        jal	x4, _fnmsub_j4
_fnmsub_j4:    fnmsub.s      x4, x4, x4, x4
        jal	x5, _fnmsub_j5
_fnmsub_j5:    fnmsub.s      x5, x5, x5, x5
        jal	x6, _fnmsub_j6
_fnmsub_j6:    fnmsub.s      x6, x6, x6, x6
        jal	x7, _fnmsub_j7
_fnmsub_j7:    fnmsub.s      x7, x7, x7, x7
        jal	x8, _fnmsub_j8
_fnmsub_j8:    fnmsub.s      x8, x8, x8, x8
        jal	x9, _fnmsub_j9
_fnmsub_j9:    fnmsub.s      x9, x9, x9, x9
        jal	x10, _fnmsub_j10
_fnmsub_j10:    fnmsub.s      x10, x10, x10, x10
        jal	x11, _fnmsub_j11
_fnmsub_j11:    fnmsub.s      x11, x11, x11, x11
        jal	x12, _fnmsub_j12
_fnmsub_j12:    fnmsub.s      x12, x12, x12, x12
        jal	x13, _fnmsub_j13
_fnmsub_j13:    fnmsub.s      x13, x13, x13, x13
        jal	x14, _fnmsub_j14
_fnmsub_j14:    fnmsub.s      x14, x14, x14, x14
        jal	x15, _fnmsub_j15
_fnmsub_j15:    fnmsub.s      x15, x15, x15, x15
        jal	x16, _fnmsub_j16
_fnmsub_j16:    fnmsub.s      x16, x16, x16, x16
        jal	x17, _fnmsub_j17
_fnmsub_j17:    fnmsub.s      x17, x17, x17, x17
        jal	x18, _fnmsub_j18
_fnmsub_j18:    fnmsub.s      x18, x18, x18, x18
        jal	x19, _fnmsub_j19
_fnmsub_j19:    fnmsub.s      x19, x19, x19, x19
        jal	x20, _fnmsub_j20
_fnmsub_j20:    fnmsub.s      x20, x20, x20, x20
        jal	x21, _fnmsub_j21
_fnmsub_j21:    fnmsub.s      x21, x21, x21, x21
        jal	x22, _fnmsub_j22
_fnmsub_j22:    fnmsub.s      x22, x22, x22, x22
        jal	x23, _fnmsub_j23
_fnmsub_j23:    fnmsub.s      x23, x23, x23, x23
        jal	x24, _fnmsub_j24
_fnmsub_j24:    fnmsub.s      x24, x24, x24, x24
        jal	x25, _fnmsub_j25
_fnmsub_j25:    fnmsub.s      x25, x25, x25, x25
        jal	x26, _fnmsub_j26
_fnmsub_j26:    fnmsub.s      x26, x26, x26, x26
        jal	x27, _fnmsub_j27
_fnmsub_j27:    fnmsub.s      x27, x27, x27, x27
        jal	x28, _fnmsub_j28
_fnmsub_j28:    fnmsub.s      x28, x28, x28, x28
        jal	x29, _fnmsub_j29
_fnmsub_j29:    fnmsub.s      x29, x29, x29, x29
        jal	x30, _fnmsub_j30
_fnmsub_j30:    fnmsub.s      x30, x30, x30, x30
        jal	x31, _fnmsub_j31
_fnmsub_j31:    fnmsub.s      x31, x31, x31, x31

        // 38 - jalr -> fnmsub (rs1, rs2, rs3)
        la x1, _fnmsub_jr0
        jalr	x0, x1, 0
_fnmsub_jr0:   fnmsub.s      x0, x0, x0, x0
        la x1, _fnmsub_jr1
        jalr	x1, x1, 0
_fnmsub_jr1:   fnmsub.s      x1, x1, x1, x1
        la x1, _fnmsub_jr2
        jalr	x2, x1, 0
_fnmsub_jr2:   fnmsub.s      x2, x2, x2, x2
        la x1, _fnmsub_jr3
        jalr	x3, x1, 0
_fnmsub_jr3:   fnmsub.s      x3, x3, x3, x3
        la x1, _fnmsub_jr4
        jalr	x4, x1, 0
_fnmsub_jr4:   fnmsub.s      x4, x4, x4, x4
        la x1, _fnmsub_jr5
        jalr	x5, x1, 0
_fnmsub_jr5:   fnmsub.s      x5, x5, x5, x5
        la x1, _fnmsub_jr6
        jalr	x6, x1, 0
_fnmsub_jr6:   fnmsub.s      x6, x6, x6, x6
        la x1, _fnmsub_jr7
        jalr	x7, x1, 0
_fnmsub_jr7:   fnmsub.s      x7, x7, x7, x7
        la x1, _fnmsub_jr8
        jalr	x8, x1, 0
_fnmsub_jr8:   fnmsub.s      x8, x8, x8, x8
        la x1, _fnmsub_jr9
        jalr	x9, x1, 0
_fnmsub_jr9:   fnmsub.s      x9, x9, x9, x9
        la x1, _fnmsub_jr10
        jalr	x10, x1, 0
_fnmsub_jr10:   fnmsub.s      x10, x10, x10, x10
        la x1, _fnmsub_jr11
        jalr	x11, x1, 0
_fnmsub_jr11:   fnmsub.s      x11, x11, x11, x11
        la x1, _fnmsub_jr12
        jalr	x12, x1, 0
_fnmsub_jr12:   fnmsub.s      x12, x12, x12, x12
        la x1, _fnmsub_jr13
        jalr	x13, x1, 0
_fnmsub_jr13:   fnmsub.s      x13, x13, x13, x13
        la x1, _fnmsub_jr14
        jalr	x14, x1, 0
_fnmsub_jr14:   fnmsub.s      x14, x14, x14, x14
        la x1, _fnmsub_jr15
        jalr	x15, x1, 0
_fnmsub_jr15:   fnmsub.s      x15, x15, x15, x15
        la x1, _fnmsub_jr16
        jalr	x16, x1, 0
_fnmsub_jr16:   fnmsub.s      x16, x16, x16, x16
        la x1, _fnmsub_jr17
        jalr	x17, x1, 0
_fnmsub_jr17:   fnmsub.s      x17, x17, x17, x17
        la x1, _fnmsub_jr18
        jalr	x18, x1, 0
_fnmsub_jr18:   fnmsub.s      x18, x18, x18, x18
        la x1, _fnmsub_jr19
        jalr	x19, x1, 0
_fnmsub_jr19:   fnmsub.s      x19, x19, x19, x19
        la x1, _fnmsub_jr20
        jalr	x20, x1, 0
_fnmsub_jr20:   fnmsub.s      x20, x20, x20, x20
        la x1, _fnmsub_jr21
        jalr	x21, x1, 0
_fnmsub_jr21:   fnmsub.s      x21, x21, x21, x21
        la x1, _fnmsub_jr22
        jalr	x22, x1, 0
_fnmsub_jr22:   fnmsub.s      x22, x22, x22, x22
        la x1, _fnmsub_jr23
        jalr	x23, x1, 0
_fnmsub_jr23:   fnmsub.s      x23, x23, x23, x23
        la x1, _fnmsub_jr24
        jalr	x24, x1, 0
_fnmsub_jr24:   fnmsub.s      x24, x24, x24, x24
        la x1, _fnmsub_jr25
        jalr	x25, x1, 0
_fnmsub_jr25:   fnmsub.s      x25, x25, x25, x25
        la x1, _fnmsub_jr26
        jalr	x26, x1, 0
_fnmsub_jr26:   fnmsub.s      x26, x26, x26, x26
        la x1, _fnmsub_jr27
        jalr	x27, x1, 0
_fnmsub_jr27:   fnmsub.s      x27, x27, x27, x27
        la x1, _fnmsub_jr28
        jalr	x28, x1, 0
_fnmsub_jr28:   fnmsub.s      x28, x28, x28, x28
        la x1, _fnmsub_jr29
        jalr	x29, x1, 0
_fnmsub_jr29:   fnmsub.s      x29, x29, x29, x29
        la x1, _fnmsub_jr30
        jalr	x30, x1, 0
_fnmsub_jr30:   fnmsub.s      x30, x30, x30, x30
        la x1, _fnmsub_jr31
        jalr	x31, x1, 0
_fnmsub_jr31:   fnmsub.s      x31, x31, x31, x31

        // 39 - jal -> fsgnjn (rs1, rs2)
        jal	x0, _fsgnjn_j0
_fsgnjn_j0:    fsgnjn.s      x0, x0, x0
        jal	x1, _fsgnjn_j1
_fsgnjn_j1:    fsgnjn.s      x1, x1, x1
        jal	x2, _fsgnjn_j2
_fsgnjn_j2:    fsgnjn.s      x2, x2, x2
        jal	x3, _fsgnjn_j3
_fsgnjn_j3:    fsgnjn.s      x3, x3, x3
        jal	x4, _fsgnjn_j4
_fsgnjn_j4:    fsgnjn.s      x4, x4, x4
        jal	x5, _fsgnjn_j5
_fsgnjn_j5:    fsgnjn.s      x5, x5, x5
        jal	x6, _fsgnjn_j6
_fsgnjn_j6:    fsgnjn.s      x6, x6, x6
        jal	x7, _fsgnjn_j7
_fsgnjn_j7:    fsgnjn.s      x7, x7, x7
        jal	x8, _fsgnjn_j8
_fsgnjn_j8:    fsgnjn.s      x8, x8, x8
        jal	x9, _fsgnjn_j9
_fsgnjn_j9:    fsgnjn.s      x9, x9, x9
        jal	x10, _fsgnjn_j10
_fsgnjn_j10:    fsgnjn.s      x10, x10, x10
        jal	x11, _fsgnjn_j11
_fsgnjn_j11:    fsgnjn.s      x11, x11, x11
        jal	x12, _fsgnjn_j12
_fsgnjn_j12:    fsgnjn.s      x12, x12, x12
        jal	x13, _fsgnjn_j13
_fsgnjn_j13:    fsgnjn.s      x13, x13, x13
        jal	x14, _fsgnjn_j14
_fsgnjn_j14:    fsgnjn.s      x14, x14, x14
        jal	x15, _fsgnjn_j15
_fsgnjn_j15:    fsgnjn.s      x15, x15, x15
        jal	x16, _fsgnjn_j16
_fsgnjn_j16:    fsgnjn.s      x16, x16, x16
        jal	x17, _fsgnjn_j17
_fsgnjn_j17:    fsgnjn.s      x17, x17, x17
        jal	x18, _fsgnjn_j18
_fsgnjn_j18:    fsgnjn.s      x18, x18, x18
        jal	x19, _fsgnjn_j19
_fsgnjn_j19:    fsgnjn.s      x19, x19, x19
        jal	x20, _fsgnjn_j20
_fsgnjn_j20:    fsgnjn.s      x20, x20, x20
        jal	x21, _fsgnjn_j21
_fsgnjn_j21:    fsgnjn.s      x21, x21, x21
        jal	x22, _fsgnjn_j22
_fsgnjn_j22:    fsgnjn.s      x22, x22, x22
        jal	x23, _fsgnjn_j23
_fsgnjn_j23:    fsgnjn.s      x23, x23, x23
        jal	x24, _fsgnjn_j24
_fsgnjn_j24:    fsgnjn.s      x24, x24, x24
        jal	x25, _fsgnjn_j25
_fsgnjn_j25:    fsgnjn.s      x25, x25, x25
        jal	x26, _fsgnjn_j26
_fsgnjn_j26:    fsgnjn.s      x26, x26, x26
        jal	x27, _fsgnjn_j27
_fsgnjn_j27:    fsgnjn.s      x27, x27, x27
        jal	x28, _fsgnjn_j28
_fsgnjn_j28:    fsgnjn.s      x28, x28, x28
        jal	x29, _fsgnjn_j29
_fsgnjn_j29:    fsgnjn.s      x29, x29, x29
        jal	x30, _fsgnjn_j30
_fsgnjn_j30:    fsgnjn.s      x30, x30, x30
        jal	x31, _fsgnjn_j31
_fsgnjn_j31:    fsgnjn.s      x31, x31, x31

        // 40 - jalr -> fsgnjn (rs1, rs2)
        la x1, _fsgnjn_jr0
        jalr	x0, x1, 0
_fsgnjn_jr0:   fsgnjn.s      x0, x0, x0
        la x1, _fsgnjn_jr1
        jalr	x1, x1, 0
_fsgnjn_jr1:   fsgnjn.s      x1, x1, x1
        la x1, _fsgnjn_jr2
        jalr	x2, x1, 0
_fsgnjn_jr2:   fsgnjn.s      x2, x2, x2
        la x1, _fsgnjn_jr3
        jalr	x3, x1, 0
_fsgnjn_jr3:   fsgnjn.s      x3, x3, x3
        la x1, _fsgnjn_jr4
        jalr	x4, x1, 0
_fsgnjn_jr4:   fsgnjn.s      x4, x4, x4
        la x1, _fsgnjn_jr5
        jalr	x5, x1, 0
_fsgnjn_jr5:   fsgnjn.s      x5, x5, x5
        la x1, _fsgnjn_jr6
        jalr	x6, x1, 0
_fsgnjn_jr6:   fsgnjn.s      x6, x6, x6
        la x1, _fsgnjn_jr7
        jalr	x7, x1, 0
_fsgnjn_jr7:   fsgnjn.s      x7, x7, x7
        la x1, _fsgnjn_jr8
        jalr	x8, x1, 0
_fsgnjn_jr8:   fsgnjn.s      x8, x8, x8
        la x1, _fsgnjn_jr9
        jalr	x9, x1, 0
_fsgnjn_jr9:   fsgnjn.s      x9, x9, x9
        la x1, _fsgnjn_jr10
        jalr	x10, x1, 0
_fsgnjn_jr10:   fsgnjn.s      x10, x10, x10
        la x1, _fsgnjn_jr11
        jalr	x11, x1, 0
_fsgnjn_jr11:   fsgnjn.s      x11, x11, x11
        la x1, _fsgnjn_jr12
        jalr	x12, x1, 0
_fsgnjn_jr12:   fsgnjn.s      x12, x12, x12
        la x1, _fsgnjn_jr13
        jalr	x13, x1, 0
_fsgnjn_jr13:   fsgnjn.s      x13, x13, x13
        la x1, _fsgnjn_jr14
        jalr	x14, x1, 0
_fsgnjn_jr14:   fsgnjn.s      x14, x14, x14
        la x1, _fsgnjn_jr15
        jalr	x15, x1, 0
_fsgnjn_jr15:   fsgnjn.s      x15, x15, x15
        la x1, _fsgnjn_jr16
        jalr	x16, x1, 0
_fsgnjn_jr16:   fsgnjn.s      x16, x16, x16
        la x1, _fsgnjn_jr17
        jalr	x17, x1, 0
_fsgnjn_jr17:   fsgnjn.s      x17, x17, x17
        la x1, _fsgnjn_jr18
        jalr	x18, x1, 0
_fsgnjn_jr18:   fsgnjn.s      x18, x18, x18
        la x1, _fsgnjn_jr19
        jalr	x19, x1, 0
_fsgnjn_jr19:   fsgnjn.s      x19, x19, x19
        la x1, _fsgnjn_jr20
        jalr	x20, x1, 0
_fsgnjn_jr20:   fsgnjn.s      x20, x20, x20
        la x1, _fsgnjn_jr21
        jalr	x21, x1, 0
_fsgnjn_jr21:   fsgnjn.s      x21, x21, x21
        la x1, _fsgnjn_jr22
        jalr	x22, x1, 0
_fsgnjn_jr22:   fsgnjn.s      x22, x22, x22
        la x1, _fsgnjn_jr23
        jalr	x23, x1, 0
_fsgnjn_jr23:   fsgnjn.s      x23, x23, x23
        la x1, _fsgnjn_jr24
        jalr	x24, x1, 0
_fsgnjn_jr24:   fsgnjn.s      x24, x24, x24
        la x1, _fsgnjn_jr25
        jalr	x25, x1, 0
_fsgnjn_jr25:   fsgnjn.s      x25, x25, x25
        la x1, _fsgnjn_jr26
        jalr	x26, x1, 0
_fsgnjn_jr26:   fsgnjn.s      x26, x26, x26
        la x1, _fsgnjn_jr27
        jalr	x27, x1, 0
_fsgnjn_jr27:   fsgnjn.s      x27, x27, x27
        la x1, _fsgnjn_jr28
        jalr	x28, x1, 0
_fsgnjn_jr28:   fsgnjn.s      x28, x28, x28
        la x1, _fsgnjn_jr29
        jalr	x29, x1, 0
_fsgnjn_jr29:   fsgnjn.s      x29, x29, x29
        la x1, _fsgnjn_jr30
        jalr	x30, x1, 0
_fsgnjn_jr30:   fsgnjn.s      x30, x30, x30
        la x1, _fsgnjn_jr31
        jalr	x31, x1, 0
_fsgnjn_jr31:   fsgnjn.s      x31, x31, x31

        // 41 - jal -> fsgnj (rs1, rs2)
        jal	x0, _fsgnj_j0
_fsgnj_j0:    fsgnj.s      x0, x0, x0
        jal	x1, _fsgnj_j1
_fsgnj_j1:    fsgnj.s      x1, x1, x1
        jal	x2, _fsgnj_j2
_fsgnj_j2:    fsgnj.s      x2, x2, x2
        jal	x3, _fsgnj_j3
_fsgnj_j3:    fsgnj.s      x3, x3, x3
        jal	x4, _fsgnj_j4
_fsgnj_j4:    fsgnj.s      x4, x4, x4
        jal	x5, _fsgnj_j5
_fsgnj_j5:    fsgnj.s      x5, x5, x5
        jal	x6, _fsgnj_j6
_fsgnj_j6:    fsgnj.s      x6, x6, x6
        jal	x7, _fsgnj_j7
_fsgnj_j7:    fsgnj.s      x7, x7, x7
        jal	x8, _fsgnj_j8
_fsgnj_j8:    fsgnj.s      x8, x8, x8
        jal	x9, _fsgnj_j9
_fsgnj_j9:    fsgnj.s      x9, x9, x9
        jal	x10, _fsgnj_j10
_fsgnj_j10:    fsgnj.s      x10, x10, x10
        jal	x11, _fsgnj_j11
_fsgnj_j11:    fsgnj.s      x11, x11, x11
        jal	x12, _fsgnj_j12
_fsgnj_j12:    fsgnj.s      x12, x12, x12
        jal	x13, _fsgnj_j13
_fsgnj_j13:    fsgnj.s      x13, x13, x13
        jal	x14, _fsgnj_j14
_fsgnj_j14:    fsgnj.s      x14, x14, x14
        jal	x15, _fsgnj_j15
_fsgnj_j15:    fsgnj.s      x15, x15, x15
        jal	x16, _fsgnj_j16
_fsgnj_j16:    fsgnj.s      x16, x16, x16
        jal	x17, _fsgnj_j17
_fsgnj_j17:    fsgnj.s      x17, x17, x17
        jal	x18, _fsgnj_j18
_fsgnj_j18:    fsgnj.s      x18, x18, x18
        jal	x19, _fsgnj_j19
_fsgnj_j19:    fsgnj.s      x19, x19, x19
        jal	x20, _fsgnj_j20
_fsgnj_j20:    fsgnj.s      x20, x20, x20
        jal	x21, _fsgnj_j21
_fsgnj_j21:    fsgnj.s      x21, x21, x21
        jal	x22, _fsgnj_j22
_fsgnj_j22:    fsgnj.s      x22, x22, x22
        jal	x23, _fsgnj_j23
_fsgnj_j23:    fsgnj.s      x23, x23, x23
        jal	x24, _fsgnj_j24
_fsgnj_j24:    fsgnj.s      x24, x24, x24
        jal	x25, _fsgnj_j25
_fsgnj_j25:    fsgnj.s      x25, x25, x25
        jal	x26, _fsgnj_j26
_fsgnj_j26:    fsgnj.s      x26, x26, x26
        jal	x27, _fsgnj_j27
_fsgnj_j27:    fsgnj.s      x27, x27, x27
        jal	x28, _fsgnj_j28
_fsgnj_j28:    fsgnj.s      x28, x28, x28
        jal	x29, _fsgnj_j29
_fsgnj_j29:    fsgnj.s      x29, x29, x29
        jal	x30, _fsgnj_j30
_fsgnj_j30:    fsgnj.s      x30, x30, x30
        jal	x31, _fsgnj_j31
_fsgnj_j31:    fsgnj.s      x31, x31, x31

        // 42 - jalr -> fsgnj (rs1, rs2)
        la x1, _fsgnj_jr0
        jalr	x0, x1, 0
_fsgnj_jr0:   fsgnj.s      x0, x0, x0
        la x1, _fsgnj_jr1
        jalr	x1, x1, 0
_fsgnj_jr1:   fsgnj.s      x1, x1, x1
        la x1, _fsgnj_jr2
        jalr	x2, x1, 0
_fsgnj_jr2:   fsgnj.s      x2, x2, x2
        la x1, _fsgnj_jr3
        jalr	x3, x1, 0
_fsgnj_jr3:   fsgnj.s      x3, x3, x3
        la x1, _fsgnj_jr4
        jalr	x4, x1, 0
_fsgnj_jr4:   fsgnj.s      x4, x4, x4
        la x1, _fsgnj_jr5
        jalr	x5, x1, 0
_fsgnj_jr5:   fsgnj.s      x5, x5, x5
        la x1, _fsgnj_jr6
        jalr	x6, x1, 0
_fsgnj_jr6:   fsgnj.s      x6, x6, x6
        la x1, _fsgnj_jr7
        jalr	x7, x1, 0
_fsgnj_jr7:   fsgnj.s      x7, x7, x7
        la x1, _fsgnj_jr8
        jalr	x8, x1, 0
_fsgnj_jr8:   fsgnj.s      x8, x8, x8
        la x1, _fsgnj_jr9
        jalr	x9, x1, 0
_fsgnj_jr9:   fsgnj.s      x9, x9, x9
        la x1, _fsgnj_jr10
        jalr	x10, x1, 0
_fsgnj_jr10:   fsgnj.s      x10, x10, x10
        la x1, _fsgnj_jr11
        jalr	x11, x1, 0
_fsgnj_jr11:   fsgnj.s      x11, x11, x11
        la x1, _fsgnj_jr12
        jalr	x12, x1, 0
_fsgnj_jr12:   fsgnj.s      x12, x12, x12
        la x1, _fsgnj_jr13
        jalr	x13, x1, 0
_fsgnj_jr13:   fsgnj.s      x13, x13, x13
        la x1, _fsgnj_jr14
        jalr	x14, x1, 0
_fsgnj_jr14:   fsgnj.s      x14, x14, x14
        la x1, _fsgnj_jr15
        jalr	x15, x1, 0
_fsgnj_jr15:   fsgnj.s      x15, x15, x15
        la x1, _fsgnj_jr16
        jalr	x16, x1, 0
_fsgnj_jr16:   fsgnj.s      x16, x16, x16
        la x1, _fsgnj_jr17
        jalr	x17, x1, 0
_fsgnj_jr17:   fsgnj.s      x17, x17, x17
        la x1, _fsgnj_jr18
        jalr	x18, x1, 0
_fsgnj_jr18:   fsgnj.s      x18, x18, x18
        la x1, _fsgnj_jr19
        jalr	x19, x1, 0
_fsgnj_jr19:   fsgnj.s      x19, x19, x19
        la x1, _fsgnj_jr20
        jalr	x20, x1, 0
_fsgnj_jr20:   fsgnj.s      x20, x20, x20
        la x1, _fsgnj_jr21
        jalr	x21, x1, 0
_fsgnj_jr21:   fsgnj.s      x21, x21, x21
        la x1, _fsgnj_jr22
        jalr	x22, x1, 0
_fsgnj_jr22:   fsgnj.s      x22, x22, x22
        la x1, _fsgnj_jr23
        jalr	x23, x1, 0
_fsgnj_jr23:   fsgnj.s      x23, x23, x23
        la x1, _fsgnj_jr24
        jalr	x24, x1, 0
_fsgnj_jr24:   fsgnj.s      x24, x24, x24
        la x1, _fsgnj_jr25
        jalr	x25, x1, 0
_fsgnj_jr25:   fsgnj.s      x25, x25, x25
        la x1, _fsgnj_jr26
        jalr	x26, x1, 0
_fsgnj_jr26:   fsgnj.s      x26, x26, x26
        la x1, _fsgnj_jr27
        jalr	x27, x1, 0
_fsgnj_jr27:   fsgnj.s      x27, x27, x27
        la x1, _fsgnj_jr28
        jalr	x28, x1, 0
_fsgnj_jr28:   fsgnj.s      x28, x28, x28
        la x1, _fsgnj_jr29
        jalr	x29, x1, 0
_fsgnj_jr29:   fsgnj.s      x29, x29, x29
        la x1, _fsgnj_jr30
        jalr	x30, x1, 0
_fsgnj_jr30:   fsgnj.s      x30, x30, x30
        la x1, _fsgnj_jr31
        jalr	x31, x1, 0
_fsgnj_jr31:   fsgnj.s      x31, x31, x31

        // 43 - jal -> fsgnjx (rs1, rs2)
        jal	x0, _fsgnjx_j0
_fsgnjx_j0:    fsgnjx.s      x0, x0, x0
        jal	x1, _fsgnjx_j1
_fsgnjx_j1:    fsgnjx.s      x1, x1, x1
        jal	x2, _fsgnjx_j2
_fsgnjx_j2:    fsgnjx.s      x2, x2, x2
        jal	x3, _fsgnjx_j3
_fsgnjx_j3:    fsgnjx.s      x3, x3, x3
        jal	x4, _fsgnjx_j4
_fsgnjx_j4:    fsgnjx.s      x4, x4, x4
        jal	x5, _fsgnjx_j5
_fsgnjx_j5:    fsgnjx.s      x5, x5, x5
        jal	x6, _fsgnjx_j6
_fsgnjx_j6:    fsgnjx.s      x6, x6, x6
        jal	x7, _fsgnjx_j7
_fsgnjx_j7:    fsgnjx.s      x7, x7, x7
        jal	x8, _fsgnjx_j8
_fsgnjx_j8:    fsgnjx.s      x8, x8, x8
        jal	x9, _fsgnjx_j9
_fsgnjx_j9:    fsgnjx.s      x9, x9, x9
        jal	x10, _fsgnjx_j10
_fsgnjx_j10:    fsgnjx.s      x10, x10, x10
        jal	x11, _fsgnjx_j11
_fsgnjx_j11:    fsgnjx.s      x11, x11, x11
        jal	x12, _fsgnjx_j12
_fsgnjx_j12:    fsgnjx.s      x12, x12, x12
        jal	x13, _fsgnjx_j13
_fsgnjx_j13:    fsgnjx.s      x13, x13, x13
        jal	x14, _fsgnjx_j14
_fsgnjx_j14:    fsgnjx.s      x14, x14, x14
        jal	x15, _fsgnjx_j15
_fsgnjx_j15:    fsgnjx.s      x15, x15, x15
        jal	x16, _fsgnjx_j16
_fsgnjx_j16:    fsgnjx.s      x16, x16, x16
        jal	x17, _fsgnjx_j17
_fsgnjx_j17:    fsgnjx.s      x17, x17, x17
        jal	x18, _fsgnjx_j18
_fsgnjx_j18:    fsgnjx.s      x18, x18, x18
        jal	x19, _fsgnjx_j19
_fsgnjx_j19:    fsgnjx.s      x19, x19, x19
        jal	x20, _fsgnjx_j20
_fsgnjx_j20:    fsgnjx.s      x20, x20, x20
        jal	x21, _fsgnjx_j21
_fsgnjx_j21:    fsgnjx.s      x21, x21, x21
        jal	x22, _fsgnjx_j22
_fsgnjx_j22:    fsgnjx.s      x22, x22, x22
        jal	x23, _fsgnjx_j23
_fsgnjx_j23:    fsgnjx.s      x23, x23, x23
        jal	x24, _fsgnjx_j24
_fsgnjx_j24:    fsgnjx.s      x24, x24, x24
        jal	x25, _fsgnjx_j25
_fsgnjx_j25:    fsgnjx.s      x25, x25, x25
        jal	x26, _fsgnjx_j26
_fsgnjx_j26:    fsgnjx.s      x26, x26, x26
        jal	x27, _fsgnjx_j27
_fsgnjx_j27:    fsgnjx.s      x27, x27, x27
        jal	x28, _fsgnjx_j28
_fsgnjx_j28:    fsgnjx.s      x28, x28, x28
        jal	x29, _fsgnjx_j29
_fsgnjx_j29:    fsgnjx.s      x29, x29, x29
        jal	x30, _fsgnjx_j30
_fsgnjx_j30:    fsgnjx.s      x30, x30, x30
        jal	x31, _fsgnjx_j31
_fsgnjx_j31:    fsgnjx.s      x31, x31, x31

        // 44 - jalr -> fsgnjx (rs1, rs2)
        la x1, _fsgnjx_jr0
        jalr	x0, x1, 0
_fsgnjx_jr0:   fsgnjx.s      x0, x0, x0
        la x1, _fsgnjx_jr1
        jalr	x1, x1, 0
_fsgnjx_jr1:   fsgnjx.s      x1, x1, x1
        la x1, _fsgnjx_jr2
        jalr	x2, x1, 0
_fsgnjx_jr2:   fsgnjx.s      x2, x2, x2
        la x1, _fsgnjx_jr3
        jalr	x3, x1, 0
_fsgnjx_jr3:   fsgnjx.s      x3, x3, x3
        la x1, _fsgnjx_jr4
        jalr	x4, x1, 0
_fsgnjx_jr4:   fsgnjx.s      x4, x4, x4
        la x1, _fsgnjx_jr5
        jalr	x5, x1, 0
_fsgnjx_jr5:   fsgnjx.s      x5, x5, x5
        la x1, _fsgnjx_jr6
        jalr	x6, x1, 0
_fsgnjx_jr6:   fsgnjx.s      x6, x6, x6
        la x1, _fsgnjx_jr7
        jalr	x7, x1, 0
_fsgnjx_jr7:   fsgnjx.s      x7, x7, x7
        la x1, _fsgnjx_jr8
        jalr	x8, x1, 0
_fsgnjx_jr8:   fsgnjx.s      x8, x8, x8
        la x1, _fsgnjx_jr9
        jalr	x9, x1, 0
_fsgnjx_jr9:   fsgnjx.s      x9, x9, x9
        la x1, _fsgnjx_jr10
        jalr	x10, x1, 0
_fsgnjx_jr10:   fsgnjx.s      x10, x10, x10
        la x1, _fsgnjx_jr11
        jalr	x11, x1, 0
_fsgnjx_jr11:   fsgnjx.s      x11, x11, x11
        la x1, _fsgnjx_jr12
        jalr	x12, x1, 0
_fsgnjx_jr12:   fsgnjx.s      x12, x12, x12
        la x1, _fsgnjx_jr13
        jalr	x13, x1, 0
_fsgnjx_jr13:   fsgnjx.s      x13, x13, x13
        la x1, _fsgnjx_jr14
        jalr	x14, x1, 0
_fsgnjx_jr14:   fsgnjx.s      x14, x14, x14
        la x1, _fsgnjx_jr15
        jalr	x15, x1, 0
_fsgnjx_jr15:   fsgnjx.s      x15, x15, x15
        la x1, _fsgnjx_jr16
        jalr	x16, x1, 0
_fsgnjx_jr16:   fsgnjx.s      x16, x16, x16
        la x1, _fsgnjx_jr17
        jalr	x17, x1, 0
_fsgnjx_jr17:   fsgnjx.s      x17, x17, x17
        la x1, _fsgnjx_jr18
        jalr	x18, x1, 0
_fsgnjx_jr18:   fsgnjx.s      x18, x18, x18
        la x1, _fsgnjx_jr19
        jalr	x19, x1, 0
_fsgnjx_jr19:   fsgnjx.s      x19, x19, x19
        la x1, _fsgnjx_jr20
        jalr	x20, x1, 0
_fsgnjx_jr20:   fsgnjx.s      x20, x20, x20
        la x1, _fsgnjx_jr21
        jalr	x21, x1, 0
_fsgnjx_jr21:   fsgnjx.s      x21, x21, x21
        la x1, _fsgnjx_jr22
        jalr	x22, x1, 0
_fsgnjx_jr22:   fsgnjx.s      x22, x22, x22
        la x1, _fsgnjx_jr23
        jalr	x23, x1, 0
_fsgnjx_jr23:   fsgnjx.s      x23, x23, x23
        la x1, _fsgnjx_jr24
        jalr	x24, x1, 0
_fsgnjx_jr24:   fsgnjx.s      x24, x24, x24
        la x1, _fsgnjx_jr25
        jalr	x25, x1, 0
_fsgnjx_jr25:   fsgnjx.s      x25, x25, x25
        la x1, _fsgnjx_jr26
        jalr	x26, x1, 0
_fsgnjx_jr26:   fsgnjx.s      x26, x26, x26
        la x1, _fsgnjx_jr27
        jalr	x27, x1, 0
_fsgnjx_jr27:   fsgnjx.s      x27, x27, x27
        la x1, _fsgnjx_jr28
        jalr	x28, x1, 0
_fsgnjx_jr28:   fsgnjx.s      x28, x28, x28
        la x1, _fsgnjx_jr29
        jalr	x29, x1, 0
_fsgnjx_jr29:   fsgnjx.s      x29, x29, x29
        la x1, _fsgnjx_jr30
        jalr	x30, x1, 0
_fsgnjx_jr30:   fsgnjx.s      x30, x30, x30
        la x1, _fsgnjx_jr31
        jalr	x31, x1, 0
_fsgnjx_jr31:   fsgnjx.s      x31, x31, x31

        // 45 - custom_0 - rd0
        sw        x1, 0(x1)
        cv.lbu    x0, (x1), 4
        fadd.s    x1, x0, x0
        cv.lbu    x0, (x1), 4
        fdiv.s    x1, x0, x0
        cv.lbu    x0, (x1), 4
        feq.s     x1, x0, x0
        cv.lbu    x0, (x1), 4
        fle.s     x1, x0, x0
        cv.lbu    x0, (x1), 4
        flt.s     x1, x0, x0
        cv.lbu    x0, (x1), 4
        fmax.s    x1, x0, x0
        cv.lbu    x0, (x1), 4
        fmin.s    x1, x0, x0
        cv.lbu    x0, (x1), 4
        fmul.s    x1, x0, x0
        cv.lbu    x0, (x1), 4
        fsgnjn.s  x1, x0, x0
        cv.lbu    x0, (x1), 4
        fsgnj.s   x1, x0, x0
        cv.lbu    x0, (x1), 4
        fsgnjx.s  x1, x0, x0
        cv.lbu    x0, (x1), 4
        fsub.s    x1, x0, x0
        cv.lbu    x0, (x1), 4
        fmadd.s   x1, x0, x0, x0
        cv.lbu    x0, (x1), 4
        fmsub.s   x1, x0, x0, x0
        cv.lbu    x0, (x1), 4
        fnmadd.s  x1, x0, x0, x0
        cv.lbu    x0, (x1), 4
        fnmadd.s  x1, x0, x0, x0
        cv.lbu    x0, (x1), 4
        fnmsub.s  x1, x0, x0, x0
        cv.lbu    x0, (x1), 4
        fsqrt.s   x1, x0
        cv.lbu    x0, (x1), 4
        fcvt.s.w  x1, x0
        cv.lbu    x0, (x1), 4
        fcvt.wu.s x1, x0

        // 46 - custom_1 - rd0
        cv.lbu    x0, (x1), x0
        fnmsub.s  x1, x0, x0, x0
        cv.lbu    x0, (x1), x0
        fnmadd.s  x1, x0, x0, x0

        // 47 - 
        // 48 - 
        // 49 - 
        // 50 - 
        // (rs1, rs2, rs3)  refer lines 1994-2057
        // (rs1, rs2, rs3)  refer lines 2060-2155
        // (rs1, rs2)       refer lines 26-89
        // (rs1, rs2)       refer lines 92-187
        // (rs1)            refer lines 190-253
        // (rs1)            refer lines 256-351

      # for uvme_cv32e40p_fp_instr_covg/cg_f_inst_reg/cr_non_rv32f_rd_rv32f_rs1 - end
    ######### FOR PULP_FPU CFG - END   #########

    ######### Added for ex_stage hole coverage #########
    la x1, test_end
    li x2, 1
    fcvt.s.w x2, x2

    fdiv.s x3, x1, x2
    div x4, x5, x0
    jalr x0, x3, 0
    ######### End for ex_stage hole coverage #########

test_end:
    li x18, TEST_PASS

    li x17, VIRT_PERIPH_STATUS_FLAG_ADDR
    sw x18,0(x17)
    j _exit

_exit:
    j _exit

