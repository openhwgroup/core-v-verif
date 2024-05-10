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

        // 1
        jal	x0, _j0
_j0:    fcvt.s.w             f0, x0
        jal	x1, _j1
_j1:    fcvt.s.w             f1, x1
        jal	x2, _j2
_j2:    fcvt.s.w             f2, x2
        jal	x3, _j3
_j3:    fcvt.s.w             f3, x3
        jal	x4, _j4
_j4:    fcvt.s.w             f4, x4
        jal	x5, _j5
_j5:    fcvt.s.w             f5, x5
        jal	x6, _j6
_j6:    fcvt.s.w             f6, x6
        jal	x7, _j7
_j7:    fcvt.s.w             f7, x7
        jal	x8, _j8
_j8:    fcvt.s.w             f8, x8
        jal	x9, _j9
_j9:    fcvt.s.w             f9, x9
        jal	x10, _j10
_j10:   fcvt.s.w             f10, x10
        jal	x11, _j11
_j11:   fcvt.s.w             f11, x11
        jal	x12, _j12
_j12:   fcvt.s.w             f12, x12
        jal	x13, _j13
_j13:   fcvt.s.w             f13, x13
        jal	x14, _j14
_j14:   fcvt.s.w             f14, x14
        jal	x15, _j15
_j15:   fcvt.s.w             f15, x15
        jal	x16, _j16
_j16:   fcvt.s.w             f16, x16
        jal	x17, _j17
_j17:   fcvt.s.w             f17, x17
        jal	x18, _j18
_j18:   fcvt.s.w             f18, x18
        jal	x19, _j19
_j19:   fcvt.s.w             f19, x19
        jal	x20, _j20
_j20:   fcvt.s.w             f20, x20
        jal	x21, _j21
_j21:   fcvt.s.w             f21, x21
        jal	x22, _j22
_j22:   fcvt.s.w             f22, x22
        jal	x23, _j23
_j23:   fcvt.s.w             f23, x23
        jal	x24, _j24
_j24:   fcvt.s.w             f24, x24
        jal	x25, _j25
_j25:   fcvt.s.w             f25, x25
        jal	x26, _j26
_j26:   fcvt.s.w             f26, x26
        jal	x27, _j27
_j27:   fcvt.s.w             f27, x27
        jal	x28, _j28
_j28:   fcvt.s.w             f28, x28
        jal	x29, _j29
_j29:   fcvt.s.w             f29, x29
        jal	x30, _j30
_j30:   fcvt.s.w             f30, x30
        jal	x31, _j31
_j31:   fcvt.s.w             f31, x31

        // 2
        jal	x0, _jj0
_jj0:   fcvt.s.wu             f0, x0
        jal	x1, _jj1
_jj1:   fcvt.s.wu             f1, x1
        jal	x2, _jj2
_jj2:   fcvt.s.wu             f2, x2
        jal	x3, _jj3
_jj3:   fcvt.s.wu             f3, x3
        jal	x4, _jj4
_jj4:   fcvt.s.wu             f4, x4
        jal	x5, _jj5
_jj5:   fcvt.s.wu             f5, x5
        jal	x6, _jj6
_jj6:   fcvt.s.wu             f6, x6
        jal	x7, _jj7
_jj7:   fcvt.s.wu             f7, x7
        jal	x8, _jj8
_jj8:   fcvt.s.wu             f8, x8
        jal	x9, _jj9
_jj9:   fcvt.s.wu             f9, x9
        jal	x10, _jj10
_jj10:  fcvt.s.wu             f10, x10
        jal	x11, _jj11
_jj11:  fcvt.s.wu             f11, x11
        jal	x12, _jj12
_jj12:  fcvt.s.wu             f12, x12
        jal	x13, _jj13
_jj13:  fcvt.s.wu             f13, x13
        jal	x14, _jj14
_jj14:  fcvt.s.wu             f14, x14
        jal	x15, _jj15
_jj15:  fcvt.s.wu             f15, x15
        jal	x16, _jj16
_jj16:  fcvt.s.wu             f16, x16
        jal	x17, _jj17
_jj17:  fcvt.s.wu             f17, x17
        jal	x18, _jj18
_jj18:  fcvt.s.wu             f18, x18
        jal	x19, _jj19
_jj19:  fcvt.s.wu             f19, x19
        jal	x20, _jj20
_jj20:  fcvt.s.wu             f20, x20
        jal	x21, _jj21
_jj21:  fcvt.s.wu             f21, x21
        jal	x22, _jj22
_jj22:  fcvt.s.wu             f22, x22
        jal	x23, _jj23
_jj23:  fcvt.s.wu             f23, x23
        jal	x24, _jj24
_jj24:  fcvt.s.wu             f24, x24
        jal	x25, _jj25
_jj25:  fcvt.s.wu             f25, x25
        jal	x26, _jj26
_jj26:  fcvt.s.wu             f26, x26
        jal	x27, _jj27
_jj27:  fcvt.s.wu             f27, x27
        jal	x28, _jj28
_jj28:  fcvt.s.wu             f28, x28
        jal	x29, _jj29
_jj29:  fcvt.s.wu             f29, x29
        jal	x30, _jj30
_jj30:  fcvt.s.wu             f30, x30
        jal	x31, _jj31
_jj31:  fcvt.s.wu             f31, x31

        // 3
        la x1, _jr0
        jalr	x0, x1, 0
_jr0:   fcvt.s.w             f0, x0
        la x1, _jr1
        jalr	x1, x1, 0
_jr1:   fcvt.s.w             f1, x1
        la x1, _jr2
        jalr	x2, x1, 0
_jr2:   fcvt.s.w             f2, x2
        la x1, _jr3
        jalr	x3, x1, 0
_jr3:   fcvt.s.w             f3, x3
        la x1, _jr4
        jalr	x4, x1, 0
_jr4:   fcvt.s.w             f4, x4
        la x1, _jr5
        jalr	x5, x1, 0
_jr5:   fcvt.s.w             f5, x5
        la x1, _jr6
        jalr	x6, x1, 0
_jr6:   fcvt.s.w             f6, x6
        la x1, _jr7
        jalr	x7, x1, 0
_jr7:   fcvt.s.w             f7, x7
        la x1, _jr8
        jalr	x8, x1, 0
_jr8:   fcvt.s.w             f8, x8
        la x1, _jr9
        jalr	x9, x1, 0
_jr9:   fcvt.s.w             f9, x9
        la x1, _jr10
        jalr	x10, x1, 0
_jr10:  fcvt.s.w             f10, x10
        la x1, _jr11
        jalr	x11, x1, 0
_jr11:  fcvt.s.w             f11, x11
        la x1, _jr12
        jalr	x12, x1, 0
_jr12:  fcvt.s.w             f12, x12
        la x1, _jr13
        jalr	x13, x1, 0
_jr13:  fcvt.s.w             f13, x13
        la x1, _jr14
        jalr	x14, x1, 0
_jr14:  fcvt.s.w             f14, x14
        la x1, _jr15
        jalr	x15, x1, 0
_jr15:  fcvt.s.w             f15, x15
        la x1, _jr16
        jalr	x16, x1, 0
_jr16:  fcvt.s.w             f16, x16
        la x1, _jr17
        jalr	x17, x1, 0
_jr17:  fcvt.s.w             f17, x17
        la x1, _jr18
        jalr	x18, x1, 0
_jr18:  fcvt.s.w             f18, x18
        la x1, _jr19
        jalr	x19, x1, 0
_jr19:  fcvt.s.w             f19, x19
        la x1, _jr20
        jalr	x20, x1, 0
_jr20:  fcvt.s.w             f20, x20
        la x1, _jr21
        jalr	x21, x1, 0
_jr21:  fcvt.s.w             f21, x21
        la x1, _jr22
        jalr	x22, x1, 0
_jr22:  fcvt.s.w             f22, x22
        la x1, _jr23
        jalr	x23, x1, 0
_jr23:  fcvt.s.w             f23, x23
        la x1, _jr24
        jalr	x24, x1, 0
_jr24:  fcvt.s.w             f24, x24
        la x1, _jr25
        jalr	x25, x1, 0
_jr25:  fcvt.s.w             f25, x25
        la x1, _jr26
        jalr	x26, x1, 0
_jr26:  fcvt.s.w             f26, x26
        la x1, _jr27
        jalr	x27, x1, 0
_jr27:  fcvt.s.w             f27, x27
        la x1, _jr28
        jalr	x28, x1, 0
_jr28:  fcvt.s.w             f28, x28
        la x1, _jr29
        jalr	x29, x1, 0
_jr29:  fcvt.s.w             f29, x29
        la x1, _jr30
        jalr	x30, x1, 0
_jr30:  fcvt.s.w             f30, x30
        la x1, _jr31
        jalr	x31, x1, 0
_jr31:  fcvt.s.w             f31, x31
        la x1, _jr0

        // 4
        la x1, _jjr0
        jalr	x0, x1, 0
_jjr0:  fcvt.s.wu             f0, x0
        la x1, _jjr1
        jalr	x1, x1, 0
_jjr1:  fcvt.s.wu             f1, x1
        la x1, _jjr2
        jalr	x2, x1, 0
_jjr2:  fcvt.s.wu             f2, x2
        la x1, _jjr3
        jalr	x3, x1, 0
_jjr3:  fcvt.s.wu             f3, x3
        la x1, _jjr4
        jalr	x4, x1, 0
_jjr4:  fcvt.s.wu             f4, x4
        la x1, _jjr5
        jalr	x5, x1, 0
_jjr5:  fcvt.s.wu             f5, x5
        la x1, _jjr6
        jalr	x6, x1, 0
_jjr6:  fcvt.s.wu             f6, x6
        la x1, _jjr7
        jalr	x7, x1, 0
_jjr7:  fcvt.s.wu             f7, x7
        la x1, _jjr8
        jalr	x8, x1, 0
_jjr8:  fcvt.s.wu             f8, x8
        la x1, _jjr9
        jalr	x9, x1, 0
_jjr9:  fcvt.s.wu             f9, x9
        la x1, _jjr10
        jalr	x10, x1, 0
_jjr10: fcvt.s.wu             f10, x10
        la x1, _jjr11
        jalr	x11, x1, 0
_jjr11: fcvt.s.wu             f11, x11
        la x1, _jjr12
        jalr	x12, x1, 0
_jjr12: fcvt.s.wu             f12, x12
        la x1, _jjr13
        jalr	x13, x1, 0
_jjr13: fcvt.s.wu             f13, x13
        la x1, _jjr14
        jalr	x14, x1, 0
_jjr14: fcvt.s.wu             f14, x14
        la x1, _jjr15
        jalr	x15, x1, 0
_jjr15: fcvt.s.wu             f15, x15
        la x1, _jjr16
        jalr	x16, x1, 0
_jjr16: fcvt.s.wu             f16, x16
        la x1, _jjr17
        jalr	x17, x1, 0
_jjr17: fcvt.s.wu             f17, x17
        la x1, _jjr18
        jalr	x18, x1, 0
_jjr18: fcvt.s.wu             f18, x18
        la x1, _jjr19
        jalr	x19, x1, 0
_jjr19: fcvt.s.wu             f19, x19
        la x1, _jjr20
        jalr	x20, x1, 0
_jjr20: fcvt.s.wu             f20, x20
        la x1, _jjr21
        jalr	x21, x1, 0
_jjr21: fcvt.s.wu             f21, x21
        la x1, _jjr22
        jalr	x22, x1, 0
_jjr22: fcvt.s.wu             f22, x22
        la x1, _jjr23
        jalr	x23, x1, 0
_jjr23: fcvt.s.wu             f23, x23
        la x1, _jjr24
        jalr	x24, x1, 0
_jjr24: fcvt.s.wu             f24, x24
        la x1, _jjr25
        jalr	x25, x1, 0
_jjr25: fcvt.s.wu             f25, x25
        la x1, _jjr26
        jalr	x26, x1, 0
_jjr26: fcvt.s.wu             f26, x26
        la x1, _jjr27
        jalr	x27, x1, 0
_jjr27: fcvt.s.wu             f27, x27
        la x1, _jjr28
        jalr	x28, x1, 0
_jjr28: fcvt.s.wu             f28, x28
        la x1, _jjr29
        jalr	x29, x1, 0
_jjr29: fcvt.s.wu             f29, x29
        la x1, _jjr30
        jalr	x30, x1, 0
_jjr30: fcvt.s.wu             f30, x30
        la x1, _jjr31
        jalr	x31, x1, 0
_jjr31: fcvt.s.wu             f31, x31
        la x1, _jjr0

        // 5
        jal	x0, _jf0
_jf0:   flw f0, 0(x0)
        jal	x1, _jf1
_jf1:   flw f0, 0(x1)
        jal	x2, _jf2
_jf2:   flw f0, 0(x2)
        jal	x3, _jf3
_jf3:   flw f0, 0(x3) 
        jal	x4, _jf4
_jf4:   flw f0, 0(x4) 
        jal	x5, _jf5
_jf5:   flw f0, 0(x5) 
        jal	x6, _jf6
_jf6:   flw f0, 0(x6) 
        jal	x7, _jf7
_jf7:   flw f0, 0(x7) 
        jal	x8, _jf8
_jf8:   flw f0, 0(x8) 
        jal	x9, _jf9
_jf9:   flw f0, 0(x9) 
        jal	x10, _jf10
_jf10:  flw f0, 0(x10) 
        jal	x11, _jf11
_jf11:  flw f0, 0(x11) 
        jal	x12, _jf12
_jf12:  flw f0, 0(x12) 
        jal	x13, _jf13
_jf13:  flw f0, 0(x13) 
        jal	x14, _jf14
_jf14:  flw f0, 0(x14) 
        jal	x15, _jf15
_jf15:  flw f0, 0(x15) 
        jal	x16, _jf16
_jf16:  flw f0, 0(x16) 
        jal	x17, _jf17
_jf17:  flw f0, 0(x17) 
        jal	x18, _jf18
_jf18:  flw f0, 0(x18) 
        jal	x19, _jf19
_jf19:  flw f0, 0(x19) 
        jal	x20, _jf20
_jf20:  flw f0, 0(x20) 
        jal	x21, _jf21
_jf21:  flw f0, 0(x21) 
        jal	x22, _jf22
_jf22:  flw f0, 0(x22) 
        jal	x23, _jf23
_jf23:  flw f0, 0(x23) 
        jal	x24, _jf24
_jf24:  flw f0, 0(x24) 
        jal	x25, _jf25
_jf25:  flw f0, 0(x25) 
        jal	x26, _jf26
_jf26:  flw f0, 0(x26) 
        jal	x27, _jf27
_jf27:  flw f0, 0(x27) 
        jal	x28, _jf28
_jf28:  flw f0, 0(x28) 
        jal	x29, _jf29
_jf29:  flw f0, 0(x29) 
        jal	x30, _jf30
_jf30:  flw f0, 0(x30) 
        jal	x31, _jf31
_jf31:  flw f0, 0(x31) 

        // 6
        la x1, _jfr0
        jalr	x0, x1, 0
_jfr0:  flw f0, 0(x0)  
        la x1, _jfr1
        jalr	x1, x1, 0
_jfr1:  flw f0, 0(x1) 
        la x1, _jfr2
        jalr	x2, x1, 0
_jfr2:  flw f0, 0(x2) 
        la x1, _jfr3
        jalr	x3, x1, 0
_jfr3:  flw f0, 0(x3) 
        la x1, _jfr4
        jalr	x4, x1, 0
_jfr4:  flw f0, 0(x4) 
        la x1, _jfr5
        jalr	x5, x1, 0
_jfr5:  flw f0, 0(x5) 
        la x1, _jfr6
        jalr	x6, x1, 0
_jfr6:  flw f0, 0(x6) 
        la x1, _jfr7
        jalr	x7, x1, 0
_jfr7:  flw f0, 0(x7) 
        la x1, _jfr8
        jalr	x8, x1, 0
_jfr8:  flw f0, 0(x8) 
        la x1, _jfr9
        jalr	x9, x1, 0
_jfr9:  flw f0, 0(x9) 
        la x1, _jfr10
        jalr	x10, x1, 0
_jfr10: flw f0, 0(x10) 
        la x1, _jfr11
        jalr	x11, x1, 0
_jfr11: flw f0, 0(x11)
        la x1, _jfr12
        jalr	x12, x1, 0
_jfr12: flw f0, 0(x12)
        la x1, _jfr13
        jalr	x13, x1, 0
_jfr13: flw f0, 0(x13)
        la x1, _jfr14
        jalr	x14, x1, 0
_jfr14: flw f0, 0(x14)
        la x1, _jfr15
        jalr	x15, x1, 0
_jfr15: flw f0, 0(x15)
        la x1, _jfr16
        jalr	x16, x1, 0
_jfr16: flw f0, 0(x16)
        la x1, _jfr17
        jalr	x17, x1, 0
_jfr17: flw f0, 0(x17)
        la x1, _jfr18
        jalr	x18, x1, 0
_jfr18: flw f0, 0(x18)
        la x1, _jfr19
        jalr	x19, x1, 0
_jfr19: flw f0, 0(x19)
        la x1, _jfr20
        jalr	x20, x1, 0
_jfr20: flw f0, 0(x20)
        la x1, _jfr21
        jalr	x21, x1, 0
_jfr21: flw f0, 0(x21)
        la x1, _jfr22
        jalr	x22, x1, 0
_jfr22: flw f0, 0(x22)
        la x1, _jfr23
        jalr	x23, x1, 0
_jfr23: flw f0, 0(x23)
        la x1, _jfr24
        jalr	x24, x1, 0
_jfr24: flw f0, 0(x24)
        la x1, _jfr25
        jalr	x25, x1, 0
_jfr25: flw f0, 0(x25)
        la x1, _jfr26
        jalr	x26, x1, 0
_jfr26: flw f0, 0(x26)
        la x1, _jfr27
        jalr	x27, x1, 0
_jfr27: flw f0, 0(x27)
        la x1, _jfr28
        jalr	x28, x1, 0
_jfr28: flw f0, 0(x28)
        la x1, _jfr29
        jalr	x29, x1, 0
_jfr29: flw f0, 0(x29)
        la x1, _jfr30
        jalr	x30, x1, 0
_jfr30: flw f0, 0(x30)
        la x1, _jfr31
        jalr	x31, x1, 0
_jfr31: flw f0, 0(x31)

        # 7
        jal	x0, _jm0
_jm0:   fmv.w.x f0, x0
        jal	x1, _jm1
_jm1:   fmv.w.x f0, x1
        jal	x2, _jm2
_jm2:   fmv.w.x f0, x2
        jal	x3, _jm3
_jm3:   fmv.w.x f0, x3 
        jal	x4, _jm4
_jm4:   fmv.w.x f0, x4
        jal	x5, _jm5
_jm5:   fmv.w.x f0, x5 
        jal	x6, _jm6
_jm6:   fmv.w.x f0, x6 
        jal	x7, _jm7
_jm7:   fmv.w.x f0, x7 
        jal	x8, _jm8
_jm8:   fmv.w.x f0, x8 
        jal	x9, _jm9
_jm9:   fmv.w.x f0, x9 
        jal	x10, _jm10
_jm10:  fmv.w.x f0, x10 
        jal	x11, _jm11
_jm11:  fmv.w.x f0, x11 
        jal	x12, _jm12
_jm12:  fmv.w.x f0, x12 
        jal	x13, _jm13
_jm13:  fmv.w.x f0, x13 
        jal	x14, _jm14
_jm14:  fmv.w.x f0, x14 
        jal	x15, _jm15
_jm15:  fmv.w.x f0, x15 
        jal	x16, _jm16
_jm16:  fmv.w.x f0, x16 
        jal	x17, _jm17
_jm17:  fmv.w.x f0, x17 
        jal	x18, _jm18
_jm18:  fmv.w.x f0, x18 
        jal	x19, _jm19
_jm19:  fmv.w.x f0, x19 
        jal	x20, _jm20
_jm20:  fmv.w.x f0, x20 
        jal	x21, _jm21
_jm21:  fmv.w.x f0, x21 
        jal	x22, _jm22
_jm22:  fmv.w.x f0, x22 
        jal	x23, _jm23
_jm23:  fmv.w.x f0, x23 
        jal	x24, _jm24
_jm24:  fmv.w.x f0, x24 
        jal	x25, _jm25
_jm25:  fmv.w.x f0, x25 
        jal	x26, _jm26
_jm26:  fmv.w.x f0, x26 
        jal	x27, _jm27
_jm27:  fmv.w.x f0, x27 
        jal	x28, _jm28
_jm28:  fmv.w.x f0, x28 
        jal	x29, _jm29
_jm29:  fmv.w.x f0, x29 
        jal	x30, _jm30
_jm30:  fmv.w.x f0, x30 
        jal	x31, _jm31
_jm31:  fmv.w.x f0, x31 

        # 8
        la x1, _jmr0
        jalr	x0, x1, 0
_jmr0:  fmv.w.x f0, x0  
        la x1, _jmr1
        jalr	x1, x1, 0
_jmr1:  fmv.w.x f0, x1 
        la x1, _jmr2
        jalr	x2, x1, 0
_jmr2:  fmv.w.x f0, x2 
        la x1, _jmr3
        jalr	x3, x1, 0
_jmr3:  fmv.w.x f0, x3 
        la x1, _jmr4
        jalr	x4, x1, 0
_jmr4:  fmv.w.x f0, x4 
        la x1, _jmr5
        jalr	x5, x1, 0
_jmr5:  fmv.w.x f0, x5 
        la x1, _jmr6
        jalr	x6, x1, 0
_jmr6:  fmv.w.x f0, x6 
        la x1, _jmr7
        jalr	x7, x1, 0
_jmr7:  fmv.w.x f0, x7 
        la x1, _jmr8
        jalr	x8, x1, 0
_jmr8:  fmv.w.x f0, x8 
        la x1, _jmr9
        jalr	x9, x1, 0
_jmr9:  fmv.w.x f0, x9 
        la x1, _jmr10
        jalr	x10, x1, 0
_jmr10: fmv.w.x f0, x10 
        la x1, _jmr11
        jalr	x11, x1, 0
_jmr11: fmv.w.x f0, x11
        la x1, _jmr12
        jalr	x12, x1, 0
_jmr12: fmv.w.x f0, x12
        la x1, _jmr13
        jalr	x13, x1, 0
_jmr13: fmv.w.x f0, x13
        la x1, _jmr14
        jalr	x14, x1, 0
_jmr14: fmv.w.x f0, x14
        la x1, _jmr15
        jalr	x15, x1, 0
_jmr15: fmv.w.x f0, x15
        la x1, _jmr16
        jalr	x16, x1, 0
_jmr16: fmv.w.x f0, x16
        la x1, _jmr17
        jalr	x17, x1, 0
_jmr17: fmv.w.x f0, x17
        la x1, _jmr18
        jalr	x18, x1, 0
_jmr18: fmv.w.x f0, x18
        la x1, _jmr19
        jalr	x19, x1, 0
_jmr19: fmv.w.x f0, x19
        la x1, _jmr20
        jalr	x20, x1, 0
_jmr20: fmv.w.x f0, x20
        la x1, _jmr21
        jalr	x21, x1, 0
_jmr21: fmv.w.x f0, x21
        la x1, _jmr22
        jalr	x22, x1, 0
_jmr22: fmv.w.x f0, x22
        la x1, _jmr23
        jalr	x23, x1, 0
_jmr23: fmv.w.x f0, x23
        la x1, _jmr24
        jalr	x24, x1, 0
_jmr24: fmv.w.x f0, x24
        la x1, _jmr25
        jalr	x25, x1, 0
_jmr25: fmv.w.x f0, x25
        la x1, _jmr26
        jalr	x26, x1, 0
_jmr26: fmv.w.x f0, x26
        la x1, _jmr27
        jalr	x27, x1, 0
_jmr27: fmv.w.x f0, x27
        la x1, _jmr28
        jalr	x28, x1, 0
_jmr28: fmv.w.x f0, x28
        la x1, _jmr29
        jalr	x29, x1, 0
_jmr29: fmv.w.x f0, x29
        la x1, _jmr30
        jalr	x30, x1, 0
_jmr30: fmv.w.x f0, x30
        la x1, _jmr31
        jalr	x31, x1, 0
_jmr31: fmv.w.x f0, x31


        # 9
        auipc   x0, 0x40000
        fsw     f0, 0(x0)
        auipc   x1, 0x40000
        fsw     f1, 0(x1)
        auipc   x2, 0x40000
        fsw     f2, 0(x2)
        auipc   x3, 0x40000
        fsw     f3, 0(x3)
        auipc   x4, 0x40000
        fsw     f4, 0(x4)
        auipc   x5, 0x40000
        fsw     f5, 0(x5)
        auipc   x6, 0x40000
        fsw     f6, 0(x6)
        auipc   x7, 0x40000
        fsw     f7, 0(x7)
        auipc   x8, 0x40000
        fsw     f8, 0(x8)
        auipc   x9, 0x40000
        fsw     f9, 0(x9)
        auipc   x10, 0x40000
        fsw     f10, 0(x10)
        auipc   x11, 0x40000
        fsw     f11, 0(x11)
        auipc   x12, 0x40000
        fsw     f12, 0(x12)
        auipc   x13, 0x40000
        fsw     f13, 0(x13)
        auipc   x14, 0x40000
        fsw     f14, 0(x14)
        auipc   x15, 0x40000
        fsw     f15, 0(x15)
        auipc   x16, 0x40000
        fsw     f16, 0(x16)
        auipc   x17, 0x40000
        fsw     f17, 0(x17)
        auipc   x18, 0x40000
        fsw     f18, 0(x18)
        auipc   x19, 0x40000
        fsw     f19, 0(x19)
        auipc   x20, 0x40000
        fsw     f20, 0(x20)
        auipc   x21, 0x40000
        fsw     f21, 0(x21)
        auipc   x22, 0x40000
        fsw     f22, 0(x22)
        auipc   x23, 0x40000
        fsw     f23, 0(x23)
        auipc   x24, 0x40000
        fsw     f24, 0(x24)
        auipc   x25, 0x40000
        fsw     f25, 0(x25)
        auipc   x26, 0x40000
        fsw     f26, 0(x26)
        auipc   x27, 0x40000
        fsw     f27, 0(x27)
        auipc   x28, 0x40000
        fsw     f28, 0(x28)
        auipc   x29, 0x40000
        fsw     f29, 0(x29)
        auipc   x30, 0x40000
        fsw     f30, 0(x30)
        auipc   x31, 0x40000
        fsw     f31, 0(x31)

        # 10
        jal	    x0, _jfs0
_jfs0:  fsw     f0, 0(x0)
        jal	    x1, _jfs1
_jfs1:  fsw     f1, -8(x1)
        jal	    x2, _jfs2
_jfs2:  fsw     f2, -8(x2)
        jal	    x3, _jfs3
_jfs3:  fsw     f3, -8(x3)
        jal	    x4, _jfs4
_jfs4:  fsw     f4, -8(x4)
        jal	    x5, _jfs5
_jfs5:  fsw     f5, -8(x5)
        jal	    x6, _jfs6
_jfs6:  fsw     f6, -8(x6)
        jal	    x7, _jfs7
_jfs7:  fsw     f7, -8(x7)
        jal	    x8, _jfs8
_jfs8:  fsw     f8, -8(x8)
        jal	    x9, _jfs9
_jfs9:  fsw     f9, -8(x9)
        jal	    x10, _jfs10
_jfs10: fsw     f10, -8(x10)
        jal	    x11, _jfs11
_jfs11: fsw     f11, -8(x11)
        jal	    x12, _jfs12
_jfs12: fsw     f12, -8(x12)
        jal	    x13, _jfs13
_jfs13: fsw     f13, -8(x13)
        jal	    x14, _jfs14
_jfs14: fsw     f14, -8(x14)
        jal	    x15, _jfs15
_jfs15: fsw     f15, -8(x15)
        jal	    x16, _jfs16
_jfs16: fsw     f16, -8(x16)
        jal	    x17, _jfs17
_jfs17: fsw     f17, -8(x17)
        jal	    x18, _jfs18
_jfs18: fsw     f18, -8(x18)
        jal	    x19, _jfs19
_jfs19: fsw     f19, -8(x19)
        jal	    x20, _jfs20
_jfs20: fsw     f20, -8(x20)
        jal	    x21, _jfs21
_jfs21: fsw     f21, -8(x21)
        jal	    x22, _jfs22
_jfs22: fsw     f22, -8(x22)
        jal	    x23, _jfs23
_jfs23: fsw     f23, -8(x23)
        jal	    x24, _jfs24
_jfs24: fsw     f24, -8(x24)
        jal	    x25, _jfs25
_jfs25: fsw     f25, -8(x25)
        jal	    x26, _jfs26
_jfs26: fsw     f26, -8(x26)
        jal	    x27, _jfs27
_jfs27: fsw     f27, -8(x27)
        jal	    x28, _jfs28
_jfs28: fsw     f28, -8(x28)
        jal	    x29, _jfs29
_jfs29: fsw     f29, -8(x29)
        jal	    x30, _jfs30
_jfs30: fsw     f30, -8(x30)
        jal	    x31, _jfs31
_jfs31: fsw     f31, -8(x31)

        # 11
        la      x1, _jrsw0
        jalr	  x0, x1, 0
_jrsw0: fsw     f0, 0(x0)
        la      x1, _jrsw1
        jalr	  x1, x1, 0
_jrsw1: fsw     f1, -8(x1)
        la      x1, _jrsw2
        jalr	  x2, x1, 0
_jrsw2: fsw     f2, -8(x2)
        la      x1, _jrsw3
        jalr	  x3, x1, 0
_jrsw3: fsw     f3, -8(x3)
        la      x1, _jrsw4
        jalr	  x4, x1, 0
_jrsw4: fsw     f4, -8(x4)
        la      x1, _jrsw5
        jalr	  x5, x1, 0
_jrsw5: fsw     f5, -8(x5)
        la      x1, _jrsw6
        jalr	  x6, x1, 0
_jrsw6: fsw     f6, -8(x6)
        la      x1, _jrsw7
        jalr	  x7, x1, 0
_jrsw7: fsw     f7, -8(x7)
        la      x1, _jrsw8
        jalr	  x8, x1, 0
_jrsw8: fsw     f8, -8(x8)
        la      x1, _jrsw9
        jalr	  x9, x1, 0
_jrsw9: fsw     f9, -8(x9)
        la      x1, _jrsw10
        jalr	  x10, x1, 0
_jrsw10:fsw     f10, -8(x10)
        la      x1, _jrsw11
        jalr	  x11, x1, 0
_jrsw11:fsw     f11, -8(x11) 
        la      x1, _jrsw12
        jalr	  x12, x1, 0
_jrsw12:fsw     f12, -8(x12) 
        la      x1, _jrsw13
        jalr	  x13, x1, 0
_jrsw13:fsw     f13, -8(x13) 
        la      x1, _jrsw14
        jalr	  x14, x1, 0
_jrsw14:fsw     f14, -8(x14) 
        la      x1, _jrsw15
        jalr	  x15, x1, 0
_jrsw15:fsw     f15, -8(x15) 
        la      x1, _jrsw16
        jalr	  x16, x1, 0
_jrsw16:fsw     f16, -8(x16) 
        la      x1, _jrsw17
        jalr	  x17, x1, 0
_jrsw17:fsw     f17, -8(x17) 
        la      x1, _jrsw18
        jalr	  x18, x1, 0
_jrsw18:fsw     f18, -8(x18) 
        la      x1, _jrsw19
        jalr	  x19, x1, 0
_jrsw19:fsw     f19, -8(x19) 
        la      x1, _jrsw20
        jalr	  x20, x1, 0
_jrsw20:fsw     f20, -8(x20) 
        la      x1, _jrsw21
        jalr	  x21, x1, 0
_jrsw21:fsw     f21, -8(x21) 
        la      x1, _jrsw22
        jalr	  x22, x1, 0
_jrsw22:fsw     f22, -8(x22) 
        la      x1, _jrsw23
        jalr	  x23, x1, 0
_jrsw23:fsw     f23, -8(x23) 
        la      x1, _jrsw24
        jalr	  x24, x1, 0
_jrsw24:fsw     f24, -8(x24) 
        la      x1, _jrsw25
        jalr	  x25, x1, 0
_jrsw25:fsw     f25, -8(x25) 
        la      x1, _jrsw26
        jalr	  x26, x1, 0
_jrsw26:fsw     f26, -8(x26) 
        la      x1, _jrsw27
        jalr	  x27, x1, 0
_jrsw27:fsw     f27, -8(x27) 
        la      x1, _jrsw28
        jalr	  x28, x1, 0
_jrsw28:fsw     f28, -8(x28) 
        la      x1, _jrsw29
        jalr	  x29, x1, 0
_jrsw29:fsw     f29, -8(x29) 
        la      x1, _jrsw30
        jalr	  x30, x1, 0
_jrsw30:fsw     f30, -8(x30) 
        la      x1, _jrsw31
        jalr	  x31, x1, 0
_jrsw31:fsw     f31, -8(x31) 

        # 12
        sw      x0, 0(x0)
        lw      x0, 0(x0)
        fsw     f0, 0(x0)
        lw      x1, 0(x0)
        fsw     f1, 0(x1)
        lw      x2, 0(x0)
        fsw     f2, 0(x2)
        lw      x3, 0(x0)
        fsw     f3, 0(x3)
        lw      x4, 0(x0)
        fsw     f4, 0(x4)
        lw      x5, 0(x0)
        fsw     f5, 0(x5)
        lw      x6, 0(x0)
        fsw     f6, 0(x6)
        lw      x7, 0(x0)
        fsw     f7, 0(x7)
        lw      x8, 0(x0)
        fsw     f8, 0(x8)
        lw      x9, 0(x0)
        fsw     f9, 0(x9)
        lw      x10, 0(x0)
        fsw     f10, 0(x10)
        lw      x11, 0(x0)
        fsw     f11, 0(x11)
        lw      x12, 0(x0)
        fsw     f12, 0(x12)
        lw      x13, 0(x0)
        fsw     f13, 0(x13)
        lw      x14, 0(x0)
        fsw     f14, 0(x14)
        lw      x15, 0(x0)
        fsw     f15, 0(x15)
        lw      x16, 0(x0)
        fsw     f16, 0(x16)
        lw      x17, 0(x0)
        fsw     f17, 0(x17)
        lw      x18, 0(x0)
        fsw     f18, 0(x18)
        lw      x19, 0(x0)
        fsw     f19, 0(x19)
        lw      x20, 0(x0)
        fsw     f20, 0(x20)
        lw      x21, 0(x0)
        fsw     f21, 0(x21)
        lw      x22, 0(x0)
        fsw     f22, 0(x22)
        lw      x23, 0(x0)
        fsw     f23, 0(x23)
        lw      x24, 0(x0)
        fsw     f24, 0(x24)
        lw      x25, 0(x0)
        fsw     f25, 0(x25)
        lw      x26, 0(x0)
        fsw     f26, 0(x26)
        lw      x27, 0(x0)
        fsw     f27, 0(x27)
        lw      x28, 0(x0)
        fsw     f28, 0(x28)
        lw      x29, 0(x0)
        fsw     f29, 0(x29)
        lw      x30, 0(x0)
        fsw     f30, 0(x30)
        lw      x31, 0(x0)
        fsw     f31, 0(x31)

        # 13
        lui     x0, 0
        fsw     f0, 0(x0)
        lui     x1, 0
        fsw     f1, 0(x1)
        lui     x2, 0
        fsw     f2, 0(x2)
        lui     x3, 0
        fsw     f3, 0(x3)
        lui     x4, 0
        fsw     f4, 0(x4)
        lui     x5, 0
        fsw     f5, 0(x5)
        lui     x6, 0
        fsw     f6, 0(x6)
        lui     x7, 0
        fsw     f7, 0(x7)
        lui     x8, 0
        fsw     f8, 0(x8)
        lui     x9, 0
        fsw     f9, 0(x9)
        lui     x10, 0
        fsw     f10, 0(x10)
        lui     x11, 0
        fsw     f11, 0(x11)
        lui     x12, 0
        fsw     f12, 0(x12)
        lui     x13, 0
        fsw     f13, 0(x13)
        lui     x14, 0
        fsw     f14, 0(x14)
        lui     x15, 0
        fsw     f15, 0(x15)
        lui     x16, 0
        fsw     f16, 0(x16)
        lui     x17, 0
        fsw     f17, 0(x17)
        lui     x18, 0
        fsw     f18, 0(x18)
        lui     x19, 0
        fsw     f19, 0(x19)
        lui     x20, 0
        fsw     f20, 0(x20)
        lui     x21, 0
        fsw     f21, 0(x21)
        lui     x22, 0
        fsw     f22, 0(x22)
        lui     x23, 0
        fsw     f23, 0(x23)
        lui     x24, 0
        fsw     f24, 0(x24)
        lui     x25, 0
        fsw     f25, 0(x25)
        lui     x26, 0
        fsw     f26, 0(x26)
        lui     x27, 0
        fsw     f27, 0(x27)
        lui     x28, 0
        fsw     f28, 0(x28)
        lui     x29, 0
        fsw     f29, 0(x29)
        lui     x30, 0
        fsw     f30, 0(x30)
        lui     x31, 0
        fsw     f31, 0(x31)

        # 14
        mul     x0,   x0, x0
        fsw     f0, 0(x0)
        mul     x1,   x1, x0
        fsw     f1, 0(x1)
        mul     x2,   x2, x0
        fsw     f2, 0(x2)
        mul     x3,   x3, x0
        fsw     f3, 0(x3)
        mul     x4,   x4, x0
        fsw     f4, 0(x4)
        mul     x5,   x5, x0
        fsw     f5, 0(x5)
        mul     x6,   x6, x0
        fsw     f6, 0(x6)
        mul     x7,   x7, x0
        fsw     f7, 0(x7)
        mul     x8,   x8, x0
        fsw     f8, 0(x8)
        mul     x9,   x9, x0
        fsw     f9, 0(x9)
        mul     x10,   x10, x0
        fsw     f10, 0(x10)
        mul     x11,   x11, x0
        fsw     f11, 0(x11)
        mul     x12,   x12, x0
        fsw     f12, 0(x12)
        mul     x13,   x13, x0
        fsw     f13, 0(x13)
        mul     x14,   x14, x0
        fsw     f14, 0(x14)
        mul     x15,   x15, x0
        fsw     f15, 0(x15)
        mul     x16,   x16, x0
        fsw     f16, 0(x16)
        mul     x17,   x17, x0
        fsw     f17, 0(x17)
        mul     x18,   x18, x0
        fsw     f18, 0(x18)
        mul     x19,   x19, x0
        fsw     f19, 0(x19)
        mul     x20,   x20, x0
        fsw     f20, 0(x20)
        mul     x21,   x21, x0
        fsw     f21, 0(x21)
        mul     x22,   x22, x0
        fsw     f22, 0(x22)
        mul     x23,   x23, x0
        fsw     f23, 0(x23)
        mul     x24,   x24, x0
        fsw     f24, 0(x24)
        mul     x25,   x25, x0
        fsw     f25, 0(x25)
        mul     x26,   x26, x0
        fsw     f26, 0(x26)
        mul     x27,   x27, x0
        fsw     f27, 0(x27)
        mul     x28,   x28, x0
        fsw     f28, 0(x28)
        mul     x29,   x29, x0
        fsw     f29, 0(x29)
        mul     x30,   x30, x0
        fsw     f30, 0(x30)
        mul     x31,   x31, x0
        fsw     f31, 0(x31)

        # 14
        addi    x0,   x0, 100
        fsw     f0, 0(x0)
        addi    x1,   x0, 100
        fsw     f1, 0(x1)
        addi    x2,   x0, 100
        fsw     f2, 0(x2)
        addi    x3,   x0, 100
        fsw     f3, 0(x3)
        addi    x4,   x0, 100
        fsw     f4, 0(x4)
        addi    x5,   x0, 100
        fsw     f5, 0(x5)
        addi    x6,   x0, 100
        fsw     f6, 0(x6)
        addi    x7,   x0, 100
        fsw     f7, 0(x7)
        addi    x8,   x0, 100
        fsw     f8, 0(x8)
        addi    x9,   x0, 100
        fsw     f9, 0(x9)
        addi    x10,   x0, 100
        fsw     f10, 0(x10)
        addi    x11,   x0, 100
        fsw     f11, 0(x11)
        addi    x12,   x0, 100
        fsw     f12, 0(x12)
        addi    x13,   x0, 100
        fsw     f13, 0(x13)
        addi    x14,   x0, 100
        fsw     f14, 0(x14)
        addi    x15,   x0, 100
        fsw     f15, 0(x15)
        addi    x16,   x0, 100
        fsw     f16, 0(x16)
        addi    x17,   x0, 100
        fsw     f17, 0(x17)
        addi    x18,   x0, 100
        fsw     f18, 0(x18)
        addi    x19,   x0, 100
        fsw     f19, 0(x19)
        addi    x20,   x0, 100
        fsw     f20, 0(x20)
        addi    x21,   x0, 100
        fsw     f21, 0(x21)
        addi    x22,   x0, 100
        fsw     f22, 0(x22)
        addi    x23,   x0, 100
        fsw     f23, 0(x23)
        addi    x24,   x0, 100
        fsw     f24, 0(x24)
        addi    x25,   x0, 100
        fsw     f25, 0(x25)
        addi    x26,   x0, 100
        fsw     f26, 0(x26)
        addi    x27,   x0, 100
        fsw     f27, 0(x27)
        addi    x28,   x0, 100
        fsw     f28, 0(x28)
        addi    x29,   x0, 100
        fsw     f29, 0(x29)
        addi    x30,   x0, 100
        fsw     f30, 0(x30)
        addi    x31,   x0, 100
        fsw     f31, 0(x31)

        # 15
        sw      x1, 0(x1)
        cv.lbu  x0, (x1), 4
        fsw     f0, 0(x0)
        cv.lbu  x1, (x1), 4
        fsw     f1, 0(x1)
        cv.lbu  x2, (x1), 4
        fsw     f2, 0(x2)
        cv.lbu  x3, (x1), 4
        fsw     f3, 0(x3)
        cv.lbu  x4, (x1), 4
        fsw     f4, 0(x4)
        cv.lbu  x5, (x1), 4
        fsw     f5, 0(x5)
        cv.lbu  x6, (x1), 4
        fsw     f6, 0(x6)
        cv.lbu  x7, (x1), 4
        fsw     f7, 0(x7)
        cv.lbu  x8, (x1), 4
        fsw     f8, 0(x8)
        cv.lbu  x9, (x1), 4
        fsw     f9, 0(x9)
        cv.lbu  x10, (x1), 4
        fsw     f10, 0(x10)
        cv.lbu  x11, (x1), 4
        fsw     f11, 0(x11)
        cv.lbu  x12, (x1), 4
        fsw     f12, 0(x12)
        cv.lbu  x13, (x1), 4
        fsw     f13, 0(x13)
        cv.lbu  x14, (x1), 4
        fsw     f14, 0(x14)
        cv.lbu  x15, (x1), 4
        fsw     f15, 0(x15)
        cv.lbu  x16, (x1), 4
        fsw     f16, 0(x16)
        cv.lbu  x17, (x1), 4
        fsw     f17, 0(x17)
        cv.lbu  x18, (x1), 4
        fsw     f18, 0(x18)
        cv.lbu  x19, (x1), 4
        fsw     f19, 0(x19)
        cv.lbu  x20, (x1), 4
        fsw     f20, 0(x20)
        cv.lbu  x21, (x1), 4
        fsw     f21, 0(x21)
        cv.lbu  x22, (x1), 4
        fsw     f22, 0(x22)
        cv.lbu  x23, (x1), 4
        fsw     f23, 0(x23)
        cv.lbu  x24, (x1), 4
        fsw     f24, 0(x24)
        cv.lbu  x25, (x1), 4
        fsw     f25, 0(x25)
        cv.lbu  x26, (x1), 4
        fsw     f26, 0(x26)
        cv.lbu  x27, (x1), 4
        fsw     f27, 0(x27)
        cv.lbu  x28, (x1), 4
        fsw     f28, 0(x28)
        cv.lbu  x29, (x1), 4
        fsw     f29, 0(x29)
        cv.lbu  x30, (x1), 4
        fsw     f30, 0(x30)
        cv.lbu  x31, (x1), 4
        fsw     f31, 0(x31)

        # 16
        sw      x1, 0(x1)
        cv.lbu  x0, (x1), x0
        fsw     f0, 0(x0)
        cv.lbu  x1, (x1), x0
        fsw     f1, 0(x1)
        cv.lbu  x2, (x1), x0
        fsw     f2, 0(x2)
        cv.lbu  x3, (x1), x0
        fsw     f3, 0(x3)
        cv.lbu  x4, (x1), x0
        fsw     f4, 0(x4)
        cv.lbu  x5, (x1), x0
        fsw     f5, 0(x5)
        cv.lbu  x6, (x1), x0
        fsw     f6, 0(x6)
        cv.lbu  x7, (x1), x0
        fsw     f7, 0(x7)
        cv.lbu  x8, (x1), x0
        fsw     f8, 0(x8)
        cv.lbu  x9, (x1), x0
        fsw     f9, 0(x9)
        cv.lbu  x10, (x1), x0
        fsw     f10, 0(x10)
        cv.lbu  x11, (x1), x0
        fsw     f11, 0(x11)
        cv.lbu  x12, (x1), x0
        fsw     f12, 0(x12)
        cv.lbu  x13, (x1), x0
        fsw     f13, 0(x13)
        cv.lbu  x14, (x1), x0
        fsw     f14, 0(x14)
        cv.lbu  x15, (x1), x0
        fsw     f15, 0(x15)
        cv.lbu  x16, (x1), x0
        fsw     f16, 0(x16)
        cv.lbu  x17, (x1), x0
        fsw     f17, 0(x17)
        cv.lbu  x18, (x1), x0
        fsw     f18, 0(x18)
        cv.lbu  x19, (x1), x0
        fsw     f19, 0(x19)
        cv.lbu  x20, (x1), x0
        fsw     f20, 0(x20)
        cv.lbu  x21, (x1), x0
        fsw     f21, 0(x21)
        cv.lbu  x22, (x1), x0
        fsw     f22, 0(x22)
        cv.lbu  x23, (x1), x0
        fsw     f23, 0(x23)
        cv.lbu  x24, (x1), x0
        fsw     f24, 0(x24)
        cv.lbu  x25, (x1), x0
        fsw     f25, 0(x25)
        cv.lbu  x26, (x1), x0
        fsw     f26, 0(x26)
        cv.lbu  x27, (x1), x0
        fsw     f27, 0(x27)
        cv.lbu  x28, (x1), x0
        fsw     f28, 0(x28)
        cv.lbu  x29, (x1), x0
        fsw     f29, 0(x29)
        cv.lbu  x30, (x1), x0
        fsw     f30, 0(x30)
        cv.lbu  x31, (x1), x0
        fsw     f31, 0(x31)

        # 17
        cv.addun  x0,   x0, x0, 0
        fsw       f0, 0(x0)
        cv.addun  x1,   x1, x0, 0
        fsw       f1, 0(x1)
        cv.addun  x2,   x2, x0, 0
        fsw       f2, 0(x2)
        cv.addun  x3,   x3, x0, 0
        fsw       f3, 0(x3)
        cv.addun  x4,   x4, x0, 0
        fsw       f4, 0(x4)
        cv.addun  x5,   x5, x0, 0
        fsw       f5, 0(x5)
        cv.addun  x6,   x6, x0, 0
        fsw       f6, 0(x6)
        cv.addun  x7,   x7, x0, 0
        fsw       f7, 0(x7)
        cv.addun  x8,   x8, x0, 0
        fsw       f8, 0(x8)
        cv.addun  x9,   x9, x0, 0
        fsw       f9, 0(x9)
        cv.addun  x10,   x10, x0, 0
        fsw       f10, 0(x10)
        cv.addun  x11,   x11, x0, 0
        fsw       f11, 0(x11)
        cv.addun  x12,   x12, x0, 0
        fsw       f12, 0(x12)
        cv.addun  x13,   x13, x0, 0
        fsw       f13, 0(x13)
        cv.addun  x14,   x14, x0, 0
        fsw       f14, 0(x14)
        cv.addun  x15,   x15, x0, 0
        fsw       f15, 0(x15)
        cv.addun  x16,   x16, x0, 0
        fsw       f16, 0(x16)
        cv.addun  x17,   x17, x0, 0
        fsw       f17, 0(x17)
        cv.addun  x18,   x18, x0, 0
        fsw       f18, 0(x18)
        cv.addun  x19,   x19, x0, 0
        fsw       f19, 0(x19)
        cv.addun  x20,   x20, x0, 0
        fsw       f20, 0(x20)
        cv.addun  x21,   x21, x0, 0
        fsw       f21, 0(x21)
        cv.addun  x22,   x22, x0, 0
        fsw       f22, 0(x22)
        cv.addun  x23,   x23, x0, 0
        fsw       f23, 0(x23)
        cv.addun  x24,   x24, x0, 0
        fsw       f24, 0(x24)
        cv.addun  x25,   x25, x0, 0
        fsw       f25, 0(x25)
        cv.addun  x26,   x26, x0, 0
        fsw       f26, 0(x26)
        cv.addun  x27,   x27, x0, 0
        fsw       f27, 0(x27)
        cv.addun  x28,   x28, x0, 0
        fsw       f28, 0(x28)
        cv.addun  x29,   x29, x0, 0
        fsw       f29, 0(x29)
        cv.addun  x30,   x30, x0, 0
        fsw       f30, 0(x30)
        cv.addun  x31,   x31, x0, 0
        fsw       f31, 0(x31)

        # 18
        cv.add.b  x0,   x0, x0
        fsw       f0, 0(x0)
        cv.add.b  x1,   x1, x0
        fsw       f1, 0(x1)
        cv.add.b  x2,   x2, x0
        fsw       f2, 0(x2)
        cv.add.b  x3,   x3, x0
        fsw       f3, 0(x3)
        cv.add.b  x4,   x4, x0
        fsw       f4, 0(x4)
        cv.add.b  x5,   x5, x0
        fsw       f5, 0(x5)
        cv.add.b  x6,   x6, x0
        fsw       f6, 0(x6)
        cv.add.b  x7,   x7, x0
        fsw       f7, 0(x7)
        cv.add.b  x8,   x8, x0
        fsw       f8, 0(x8)
        cv.add.b  x9,   x9, x0
        fsw       f9, 0(x9)
        cv.add.b  x10,   x10, x0
        fsw       f10, 0(x10)
        cv.add.b  x11,   x11, x0
        fsw       f11, 0(x11)
        cv.add.b  x12,   x12, x0
        fsw       f12, 0(x12)
        cv.add.b  x13,   x13, x0
        fsw       f13, 0(x13)
        cv.add.b  x14,   x14, x0
        fsw       f14, 0(x14)
        cv.add.b  x15,   x15, x0
        fsw       f15, 0(x15)
        cv.add.b  x16,   x16, x0
        fsw       f16, 0(x16)
        cv.add.b  x17,   x17, x0
        fsw       f17, 0(x17)
        cv.add.b  x18,   x18, x0
        fsw       f18, 0(x18)
        cv.add.b  x19,   x19, x0
        fsw       f19, 0(x19)
        cv.add.b  x20,   x20, x0
        fsw       f20, 0(x20)
        cv.add.b  x21,   x21, x0
        fsw       f21, 0(x21)
        cv.add.b  x22,   x22, x0
        fsw       f22, 0(x22)
        cv.add.b  x23,   x23, x0
        fsw       f23, 0(x23)
        cv.add.b  x24,   x24, x0
        fsw       f24, 0(x24)
        cv.add.b  x25,   x25, x0
        fsw       f25, 0(x25)
        cv.add.b  x26,   x26, x0
        fsw       f26, 0(x26)
        cv.add.b  x27,   x27, x0
        fsw       f27, 0(x27)
        cv.add.b  x28,   x28, x0
        fsw       f28, 0(x28)
        cv.add.b  x29,   x29, x0
        fsw       f29, 0(x29)
        cv.add.b  x30,   x30, x0
        fsw       f30, 0(x30)
        cv.add.b  x31,   x31, x0
        fsw       f31, 0(x31)

        # 19
        sw          x1, 0(x1)
        cv.lbu      x0, (x1), 4
        fcvt.s.wu   f0, x0
        cv.lbu      x1, (x1), 4
        fcvt.s.wu   f1, x1
        cv.lbu      x2, (x1), 4
        fcvt.s.wu   f2, x2
        cv.lbu      x3, (x1), 4
        fcvt.s.wu   f3, x3
        cv.lbu      x4, (x1), 4
        fcvt.s.wu   f4, x4
        cv.lbu      x5, (x1), 4
        fcvt.s.wu   f5, x5
        cv.lbu      x6, (x1), 4
        fcvt.s.wu   f6, x6
        cv.lbu      x7, (x1), 4
        fcvt.s.wu   f7, x7
        cv.lbu      x8, (x1), 4
        fcvt.s.wu   f8, x8
        cv.lbu      x9, (x1), 4
        fcvt.s.wu   f9, x9
        cv.lbu      x10, (x1), 4
        fcvt.s.wu   f10, x10
        cv.lbu      x11, (x1), 4
        fcvt.s.wu   f11, x11
        cv.lbu      x12, (x1), 4
        fcvt.s.wu   f12, x12
        cv.lbu      x13, (x1), 4
        fcvt.s.wu   f13, x13
        cv.lbu      x14, (x1), 4
        fcvt.s.wu   f14, x14
        cv.lbu      x15, (x1), 4
        fcvt.s.wu   f15, x15
        cv.lbu      x16, (x1), 4
        fcvt.s.wu   f16, x16
        cv.lbu      x17, (x1), 4
        fcvt.s.wu   f17, x17
        cv.lbu      x18, (x1), 4
        fcvt.s.wu   f18, x18
        cv.lbu      x19, (x1), 4
        fcvt.s.wu   f19, x19
        cv.lbu      x20, (x1), 4
        fcvt.s.wu   f20, x20
        cv.lbu      x21, (x1), 4
        fcvt.s.wu   f21, x21
        cv.lbu      x22, (x1), 4
        fcvt.s.wu   f22, x22
        cv.lbu      x23, (x1), 4
        fcvt.s.wu   f23, x23
        cv.lbu      x24, (x1), 4
        fcvt.s.wu   f24, x24
        cv.lbu      x25, (x1), 4
        fcvt.s.wu   f25, x25
        cv.lbu      x26, (x1), 4
        fcvt.s.wu   f26, x26
        cv.lbu      x27, (x1), 4
        fcvt.s.wu   f27, x27
        cv.lbu      x28, (x1), 4
        fcvt.s.wu   f28, x28
        cv.lbu      x29, (x1), 4
        fcvt.s.wu   f29, x29
        cv.lbu      x30, (x1), 4
        fcvt.s.wu   f30, x30
        cv.lbu      x31, (x1), 4
        fcvt.s.wu   f31, x31

        # 20
        auipc   x0, 0x40000
        flw     f0, 0(x0)
        auipc   x1, 0x40000
        flw     f1, 0(x1)
        auipc   x2, 0x40000
        flw     f2, 0(x2)
        auipc   x3, 0x40000
        flw     f3, 0(x3)
        auipc   x4, 0x40000
        flw     f4, 0(x4)
        auipc   x5, 0x40000
        flw     f5, 0(x5)
        auipc   x6, 0x40000
        flw     f6, 0(x6)
        auipc   x7, 0x40000
        flw     f7, 0(x7)
        auipc   x8, 0x40000
        flw     f8, 0(x8)
        auipc   x9, 0x40000
        flw     f9, 0(x9)
        auipc   x10, 0x40000
        flw     f10, 0(x10)
        auipc   x11, 0x40000
        flw     f11, 0(x11)
        auipc   x12, 0x40000
        flw     f12, 0(x12)
        auipc   x13, 0x40000
        flw     f13, 0(x13)
        auipc   x14, 0x40000
        flw     f14, 0(x14)
        auipc   x15, 0x40000
        flw     f15, 0(x15)
        auipc   x16, 0x40000
        flw     f16, 0(x16)
        auipc   x17, 0x40000
        flw     f17, 0(x17)
        auipc   x18, 0x40000
        flw     f18, 0(x18)
        auipc   x19, 0x40000
        flw     f19, 0(x19)
        auipc   x20, 0x40000
        flw     f20, 0(x20)
        auipc   x21, 0x40000
        flw     f21, 0(x21)
        auipc   x22, 0x40000
        flw     f22, 0(x22)
        auipc   x23, 0x40000
        flw     f23, 0(x23)
        auipc   x24, 0x40000
        flw     f24, 0(x24)
        auipc   x25, 0x40000
        flw     f25, 0(x25)
        auipc   x26, 0x40000
        flw     f26, 0(x26)
        auipc   x27, 0x40000
        flw     f27, 0(x27)
        auipc   x28, 0x40000
        flw     f28, 0(x28)
        auipc   x29, 0x40000
        flw     f29, 0(x29)
        auipc   x30, 0x40000
        flw     f30, 0(x30)
        auipc   x31, 0x40000
        flw     f31, 0(x31)

      # for uvme_cv32e40p_fp_instr_covg/cg_f_inst_reg/cr_non_rv32f_rd_rv32f_rs1 - end
    ######### FOR PULP_FPU CFG - END   #########

    li x18, TEST_PASS

test_end:
    li x17, VIRT_PERIPH_STATUS_FLAG_ADDR
    sw x18,0(x17)
    j _exit

_exit:
    j _exit

