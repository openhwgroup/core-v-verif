#
# Copyright (C) EM Microelectronic US Inc.
# Copyright (C) 2020 OpenHW Group
# Copyright (C) 2024 Dolphin Design
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
# SPDX-License-Identifier: Apache-2.0
#
###############################################################################
# NOT-PRESENT & READ ONLY CSRs: access read-only and not-present CSRs and check for side-effects.
###############################################################################

.globl _start
.globl main
.globl exit
.global debug
.section .text
.global u_sw_irq_handler


#define TEST_PASS                      123456789
#define TEST_FAIL                              1
#define VIRT_PERIPH_STATUS_FLAG_ADDR  0x20000000

#define MSTATUS_FS_INITIAL 0x00003800

#define BASE_EXPECTED_ILLEGAL_INSTRUCTIONS 611
#define FPU_EXPECTED_ILLEGAL_INSTRUCTIONS 21
#define NO_FPU_EXPECTED_ILLEGAL_INSTRUCTIONS 21
#define PULP_EXPECTED_ILLEGAL_INSTRUCTIONS 36
#define NO_PULP_EXPECTED_ILLEGAL_INSTRUCTIONS 42
#define FPU_ZFINX_EXPECTED_ILLEGAL_INSTRUCTIONS 6
#define FPU_NO_ZFINX_EXPECTED_ILLEGAL_INSTRUCTIONS 7
#define PULP_NO_FPU_NO_ZFINX_EXPECTED_ILLEGAL_INSTRUCTIONS 6

#define MISA_32IMC 0x40001104
#define ADD_X(MISA_BASE)     ((MISA_BASE) | (0x1<<23))
#define ADD_F(MISA_BASE)     ((MISA_BASE) | (0x1<<5 ))

#if defined(PULP)
   #if defined(FPU)
      #if defined(ZFINX)
         #define EXPECTED_ILLEGAL_INSTRUCTIONS (BASE_EXPECTED_ILLEGAL_INSTRUCTIONS+PULP_EXPECTED_ILLEGAL_INSTRUCTIONS+FPU_ZFINX_EXPECTED_ILLEGAL_INSTRUCTIONS)
         #define MISA_RESET_VAL ADD_X(MISA_32IMC)
         #define ZFINX_RESET_VALUE 0x1
      #else
         #define EXPECTED_ILLEGAL_INSTRUCTIONS (BASE_EXPECTED_ILLEGAL_INSTRUCTIONS+PULP_EXPECTED_ILLEGAL_INSTRUCTIONS+FPU_EXPECTED_ILLEGAL_INSTRUCTIONS+FPU_NO_ZFINX_EXPECTED_ILLEGAL_INSTRUCTIONS)
         #define MISA_RESET_VAL ADD_X(ADD_F(MISA_32IMC))
         #define ZFINX_RESET_VALUE 0x0
      #endif
   #else
      ### if NO FPU at all, zfinx CSR is still present
      #define EXPECTED_ILLEGAL_INSTRUCTIONS (BASE_EXPECTED_ILLEGAL_INSTRUCTIONS+PULP_EXPECTED_ILLEGAL_INSTRUCTIONS+NO_FPU_EXPECTED_ILLEGAL_INSTRUCTIONS+PULP_NO_FPU_NO_ZFINX_EXPECTED_ILLEGAL_INSTRUCTIONS)
      #define MISA_RESET_VAL ADD_X((MISA_32IMC))
      #define ZFINX_RESET_VALUE 0x0
   #endif
#else
   #define EXPECTED_ILLEGAL_INSTRUCTIONS (BASE_EXPECTED_ILLEGAL_INSTRUCTIONS+NO_PULP_EXPECTED_ILLEGAL_INSTRUCTIONS+NO_FPU_EXPECTED_ILLEGAL_INSTRUCTIONS+NO_ZFINX_EXPECTED_ILLEGAL_INSTRUCTIONS)
   #define MISA_RESET_VAL MISA_32IMC
   #define ZFINX_RESET_VALUE 0x0
#endif


main:
    li        t0, (0x1 << 3)
    csrs      mstatus, t0
    li x5, 0x0
    li x6, 0x6
    li x7, 0x7
    li x8, 0x8
    li x9, 0x9
    li x10, 0xa
    li x11, 0xb
    li x12, 0xc
    li x13, 0xd
    li x14, 0xe
    li x15, 0xf
    li x16, 0x10
    li x17, 0x11
    li x18, 0x12
    li x19, 0x13
    li x20, 0x14
    li x21, 0x15
    li x22, 0x16
    li x23, 0x17
    li x24, 0x18
    li x25, 0x19
    li x28, 0x1c
    li x29, 0x1d
    li x30, 0x1e
    li x31, 0x0

    addi    sp,sp,-84
    sw      x6,80(sp)
    sw      x7,76(sp)
    sw      x8,72(sp)
    sw      x9,68(sp)
    sw      x10,64(sp)
    sw      x11,60(sp)
    sw      x12,56(sp)
    sw      x13,52(sp)
    sw      x14,48(sp)
    sw      x15,44(sp)
    sw      x16,40(sp)
    sw      x17,36(sp)
    sw      x18,32(sp)
    sw      x19,28(sp)
    sw      x20,24(sp)
    sw      x21,20(sp)
    sw      x22,16(sp)
    sw      x23,12(sp)
    sw      x24,8(sp)
    sw      x25,4(sp)


###############################################################################
#
##   USER CSRs
#
###############################################################################

######### N-extension registers
    # ustatus
    csrrc  x5,  0x000, x0   # illegal instruction : register not present
    csrrc  x0,  0x000, x5   # illegal instruction : register not present
    csrrci x0,  0x000, 0x0a # illegal instruction : register not present
    csrrs  x0,  0x000, x5   # illegal instruction : register not present
    csrrsi x0,  0x000, 0x0a # illegal instruction : register not present
    csrrw  x0,  0x000, x0   # illegal instruction : register not present
    csrrwi x0,  0x000, 0x0a # illegal instruction : register not present

    # uie
    csrrc  x5,  0x004, x0   # illegal instruction : register not present
    csrrc  x0,  0x004, x5   # illegal instruction : register not present
    csrrci x0,  0x004, 0x0a # illegal instruction : register not present
    csrrs  x0,  0x004, x5   # illegal instruction : register not present
    csrrsi x0,  0x004, 0x0a # illegal instruction : register not present
    csrrw  x0,  0x004, x0   # illegal instruction : register not present
    csrrwi x0,  0x004, 0x0a # illegal instruction : register not present

   # utvec
    csrrc  x5,  0x005, x0   # illegal instruction : register not present
    csrrc  x0,  0x005, x5   # illegal instruction : register not present
    csrrci x0,  0x005, 0x0a # illegal instruction : register not present
    csrrs  x0,  0x005, x5   # illegal instruction : register not present
    csrrsi x0,  0x005, 0x0a # illegal instruction : register not present
    csrrw  x0,  0x005, x0   # illegal instruction : register not present
    csrrwi x0,  0x005, 0x0a # illegal instruction : register not present

    # uscratch
    csrrc  x5,  0x040, x0   # illegal instruction : register not present
    csrrc  x0,  0x040, x5   # illegal instruction : register not present
    csrrci x0,  0x040, 0x0a # illegal instruction : register not present
    csrrs  x0,  0x040, x5   # illegal instruction : register not present
    csrrsi x0,  0x040, 0x0a # illegal instruction : register not present
    csrrw  x0,  0x040, x0   # illegal instruction : register not present
    csrrwi x0,  0x040, 0x0a # illegal instruction : register not present

    # uepc
    csrrc  x5,  0x041, x0   # illegal instruction : register not present
    csrrc  x0,  0x041, x5   # illegal instruction : register not present
    csrrci x0,  0x041, 0x0a # illegal instruction : register not present
    csrrs  x0,  0x041, x5   # illegal instruction : register not present
    csrrsi x0,  0x041, 0x0a # illegal instruction : register not present
    csrrw  x0,  0x041, x0   # illegal instruction : register not present
    csrrwi x0,  0x041, 0x0a # illegal instruction : register not present

    # ucause
    csrrc  x5,  0x042, x0   # illegal instruction : register not present
    csrrc  x0,  0x042, x5   # illegal instruction : register not present
    csrrci x0,  0x042, 0x0a # illegal instruction : register not present
    csrrs  x0,  0x042, x5   # illegal instruction : register not present
    csrrsi x0,  0x042, 0x0a # illegal instruction : register not present
    csrrw  x0,  0x042, x0   # illegal instruction : register not present
    csrrwi x0,  0x042, 0x0a # illegal instruction : register not present

    # utval
    csrrc  x5,  0x043, x0   # illegal instruction : register not present
    csrrc  x0,  0x043, x5   # illegal instruction : register not present
    csrrci x0,  0x043, 0x0a # illegal instruction : register not present
    csrrs  x0,  0x043, x5   # illegal instruction : register not present
    csrrsi x0,  0x043, 0x0a # illegal instruction : register not present
    csrrw  x0,  0x043, x0   # illegal instruction : register not present
    csrrwi x0,  0x043, 0x0a # illegal instruction : register not present

    # uip
    csrrc  x5,  0x044, x0   # illegal instruction : register not present
    csrrc  x0,  0x044, x5   # illegal instruction : register not present
    csrrci x0,  0x044, 0x0a # illegal instruction : register not present
    csrrs  x0,  0x044, x5   # illegal instruction : register not present
    csrrsi x0,  0x044, 0x0a # illegal instruction : register not present
    csrrw  x0,  0x044, x0   # illegal instruction : register not present
    csrrwi x0,  0x044, 0x0a # illegal instruction : register not present

######### Other User-mode-only registers
    # mcounteren
    csrrc  x5,  0x306, x0   # illegal instruction : register not present
    csrrc  x0,  0x306, x5   # illegal instruction : register not present
    csrrci x0,  0x306, 0x0a # illegal instruction : register not present
    csrrs  x0,  0x306, x5   # illegal instruction : register not present
    csrrsi x0,  0x306, 0x0a # illegal instruction : register not present
    csrrw  x0,  0x306, x0   # illegal instruction : register not present
    csrrwi x0,  0x306, 0x0a # illegal instruction : register not present



######### FPU RELATED
# Start FPU disabled => some CSR access are illegal
# If Zfinx is enabled, FS is hardwired and below instructions should be legal,

#if defined (FPU)

#if !defined (ZFINX)
# start FPU disabled, read access are illegal
# FFLAGS R/W
    csrrc  x5,  0x001, x0   # start FPU disabled, read access are illegal
    csrrc  x0,  0x001, x5   # start FPU disabled, read access are illegal instruction
    csrrci x0,  0x001, 0x0a # start FPU disabled, read access are illegal instruction
    csrrs  x0,  0x001, x5   # start FPU disabled, read access are illegal instruction
    csrrsi x0,  0x001, 0x0a # start FPU disabled, read access are illegal instruction
    csrrw  x0,  0x001, x0   # start FPU disabled, write access are illegal instruction
    csrrwi x0,  0x001, 0x0a # start FPU disabled, write access are illegal instruction

# FRM R/W
    csrrc  x5,  0x002, x0   # start FPU disabled, read access are illegal
    csrrc  x0,  0x002, x5   # start FPU disabled, read access are illegal instruction
    csrrci x0,  0x002, 0x0a # start FPU disabled, read access are illegal instruction
    csrrs  x0,  0x002, x5   # start FPU disabled, read access are illegal instruction
    csrrsi x0,  0x002, 0x0a # start FPU disabled, read access are illegal instruction
    csrrw  x0,  0x002, x0   # start FPU disabled, write access are illegal instruction
    csrrwi x0,  0x002, 0x0a # start FPU disabled, write access are illegal instruction


# FCSR R/W
    csrrc  x5,  0x003, x0   # start FPU disabled, read access are illegal
    csrrc  x0,  0x003, x5   # start FPU disabled, read access are illegal instruction
    csrrci x0,  0x003, 0x0a # start FPU disabled, read access are illegal instruction
    csrrs  x0,  0x003, x5   # start FPU disabled, read access are illegal instruction
    csrrsi x0,  0x003, 0x0a # start FPU disabled, read access are illegal instruction
    csrrw  x0,  0x003, x0   # start FPU disabled, write access are illegal instruction
    csrrwi x0,  0x003, 0x0a # start FPU disabled, write access are illegal instruction


# enable FPU
    li x5, MSTATUS_FS_INITIAL
    csrw 0x300, x5 # MSTATUS FPU enable

#endif

# check reset values & check FPU CSR
    csrrc  x5,  0x001, x0   # FPU is enabled, read access are NOT illegal
    li     x30, 0x00000000
    bne    x5,  x30, fail

    csrrc  x5,  0x002, x0   # FPU is enabled, read access are NOT illegal
    li     x30, 0x00000000
    bne    x5,  x30, fail

    csrrc  x5,  0x003, x0   # FPU is enabled, read access are NOT illegal
    li     x30, 0x00000000
    bne    x5,  x30, fail

# FFLAGS R/W
    csrrc  x0,  0x001, x5   # FPU is enabled, read access are NOT illegal instruction
    csrrci x0,  0x001, 0x0a # FPU is enabled, read access are NOT illegal instruction
    csrrs  x0,  0x001, x5   # FPU is enabled, read access are NOT illegal instruction
    csrrsi x0,  0x001, 0x0a # FPU is enabled, read access are NOT illegal instruction
    csrrw  x0,  0x001, x0   # FPU is enabled, write access are NOT illegal instruction
    csrrwi x0,  0x001, 0x0a # FPU is enabled, write access are NOT illegal instruction

# FRM R/W
   csrrc  x0,  0x002, x5   # FPU is enabled, read access are NOT illegal instruction
   csrrci x0,  0x002, 0x0a # FPU is enabled, read access are NOT illegal instruction
   csrrs  x0,  0x002, x5   # FPU is enabled, read access are NOT illegal instruction
   csrrsi x0,  0x002, 0x0a # FPU is enabled, read access are NOT illegal instruction
   csrrw  x0,  0x002, x0   # FPU is enabled, write access are NOT illegal instruction
   csrrwi x0,  0x002, 0x0a # FPU is enabled, write access are NOT illegal instruction

# FCSR R/W
   csrrc  x0,  0x003, x5   # FPU is enabled, read access are NOT illegal instruction
   csrrci x0,  0x003, 0x0a # FPU is enabled, read access are NOT illegal instruction
   csrrs  x0,  0x003, x5   # FPU is enabled, read access are NOT illegal instruction
   csrrsi x0,  0x003, 0x0a # FPU is enabled, read access are NOT illegal instruction
   csrrw  x0,  0x003, x0   # FPU is enabled, write access are NOT illegal instruction
   csrrwi x0,  0x003, 0x0a # FPU is enabled, write access are NOT illegal instruction

#else
# FFLAGS R/W
   csrrc  x5,  0x001, x0   # illegal instruction : register not present
   csrrc  x0,  0x001, x5   # illegal instruction : register not present
   csrrci x0,  0x001, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x001, x5   # illegal instruction : register not present
   csrrsi x0,  0x001, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x001, x0   # illegal instruction : register not present
   csrrwi x0,  0x001, 0x0a # illegal instruction : register not present

# FRM R/W
   csrrc  x5,  0x002, x0   # illegal instruction : register not present
   csrrc  x0,  0x002, x5   # illegal instruction : register not present
   csrrci x0,  0x002, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x002, x5   # illegal instruction : register not present
   csrrsi x0,  0x002, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x002, x0   # illegal instruction : register not present
   csrrwi x0,  0x002, 0x0a # illegal instruction : register not present

# FCSR R/W
   csrrc  x5,  0x003, x0   # illegal instruction : register not present
   csrrc  x0,  0x003, x5   # illegal instruction : register not present
   csrrci x0,  0x003, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x003, x5   # illegal instruction : register not present
   csrrsi x0,  0x003, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x003, x0   # illegal instruction : register not present
   csrrwi x0,  0x003, 0x0a # illegal instruction : register not present

#endif

# End FPU RELATED


######### Cycle Counter (cycle)
	csrrc  x5,  0xC00, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xC00, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  0xC00, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xC00, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xC00, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xC00, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xC00, 0x0a   # illegal instruction: attempt to write RO CSR

######### Upper Cycle Counter (cycleh)
	csrrc  x5,  0xC80, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xC80, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  0xC80, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xC80, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xC80, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xC80, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xC80, 0x0a   # illegal instruction: attempt to write RO CSR

######### Instruction Retired Counter (instret)
	csrrc  x5,  0xC02, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xC02, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  0xC02, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xC02, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xC02, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xC02, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xC02, 0x0a   # illegal instruction: attempt to write RO CSR

######### Upper Instruction Retired Counter (instreth)
	csrrc  x5,  0xC82, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xC82, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  0xC82, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xC82, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xC82, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xC82, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xC82, 0x0a   # illegal instruction: attempt to write RO CSR


######### HPM Performance Monitoring Counter (3, 31) (hpmcounter[3, 31])
### START
	csrrc  x5,  0xC03, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xC03, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  0xC03, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xC03, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xC03, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xC03, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xC03, 0x0a   # illegal instruction: attempt to write RO CSR

      csrrc  x5,  0xC04, x0
   csrrc  x0,  0xC04, x5
   csrrci x0,  0xC04, 0x0a
   csrrs  x0,  0xC04, x5
   csrrsi x0,  0xC04, 0x0a
   csrrw  x0,  0xC04, x0
   csrrwi x0,  0xC04, 0x0a

   csrrc  x5,  0xC05, x0
   csrrc  x0,  0xC05, x5
   csrrci x0,  0xC05, 0x0a
   csrrs  x0,  0xC05, x5
   csrrsi x0,  0xC05, 0x0a
   csrrw  x0,  0xC05, x0
   csrrwi x0,  0xC05, 0x0a

   csrrc  x5,  0xC06, x0
   csrrc  x0,  0xC06, x5
   csrrci x0,  0xC06, 0x0a
   csrrs  x0,  0xC06, x5
   csrrsi x0,  0xC06, 0x0a
   csrrw  x0,  0xC06, x0
   csrrwi x0,  0xC06, 0x0a

   csrrc  x5,  0xC07, x0
   csrrc  x0,  0xC07, x5
   csrrci x0,  0xC07, 0x0a
   csrrs  x0,  0xC07, x5
   csrrsi x0,  0xC07, 0x0a
   csrrw  x0,  0xC07, x0
   csrrwi x0,  0xC07, 0x0a

   csrrc  x5,  0xC08, x0
   csrrc  x0,  0xC08, x5
   csrrci x0,  0xC08, 0x0a
   csrrs  x0,  0xC08, x5
   csrrsi x0,  0xC08, 0x0a
   csrrw  x0,  0xC08, x0
   csrrwi x0,  0xC08, 0x0a

   csrrc  x5,  0xC09, x0
   csrrc  x0,  0xC09, x5
   csrrci x0,  0xC09, 0x0a
   csrrs  x0,  0xC09, x5
   csrrsi x0,  0xC09, 0x0a
   csrrw  x0,  0xC09, x0
   csrrwi x0,  0xC09, 0x0a

   csrrc  x5,  0xC0A, x0
   csrrc  x0,  0xC0A, x5
   csrrci x0,  0xC0A, 0x0a
   csrrs  x0,  0xC0A, x5
   csrrsi x0,  0xC0A, 0x0a
   csrrw  x0,  0xC0A, x0
   csrrwi x0,  0xC0A, 0x0a

   csrrc  x5,  0xC0B, x0
   csrrc  x0,  0xC0B, x5
   csrrci x0,  0xC0B, 0x0a
   csrrs  x0,  0xC0B, x5
   csrrsi x0,  0xC0B, 0x0a
   csrrw  x0,  0xC0B, x0
   csrrwi x0,  0xC0B, 0x0a

   csrrc  x5,  0xC0C, x0
   csrrc  x0,  0xC0C, x5
   csrrci x0,  0xC0C, 0x0a
   csrrs  x0,  0xC0C, x5
   csrrsi x0,  0xC0C, 0x0a
   csrrw  x0,  0xC0C, x0
   csrrwi x0,  0xC0C, 0x0a

   csrrc  x5,  0xC0D, x0
   csrrc  x0,  0xC0D, x5
   csrrci x0,  0xC0D, 0x0a
   csrrs  x0,  0xC0D, x5
   csrrsi x0,  0xC0D, 0x0a
   csrrw  x0,  0xC0D, x0
   csrrwi x0,  0xC0D, 0x0a

   csrrc  x5,  0xC0E, x0
   csrrc  x0,  0xC0E, x5
   csrrci x0,  0xC0E, 0x0a
   csrrs  x0,  0xC0E, x5
   csrrsi x0,  0xC0E, 0x0a
   csrrw  x0,  0xC0E, x0
   csrrwi x0,  0xC0E, 0x0a

   csrrc  x5,  0xC0F, x0
   csrrc  x0,  0xC0F, x5
   csrrci x0,  0xC0F, 0x0a
   csrrs  x0,  0xC0F, x5
   csrrsi x0,  0xC0F, 0x0a
   csrrw  x0,  0xC0F, x0
   csrrwi x0,  0xC0F, 0x0a

   csrrc  x5,  0xC10, x0
   csrrc  x0,  0xC10, x5
   csrrci x0,  0xC10, 0x0a
   csrrs  x0,  0xC10, x5
   csrrsi x0,  0xC10, 0x0a
   csrrw  x0,  0xC10, x0
   csrrwi x0,  0xC10, 0x0a

   csrrc  x5,  0xC11, x0
   csrrc  x0,  0xC11, x5
   csrrci x0,  0xC11, 0x0a
   csrrs  x0,  0xC11, x5
   csrrsi x0,  0xC11, 0x0a
   csrrw  x0,  0xC11, x0
   csrrwi x0,  0xC11, 0x0a

   csrrc  x5,  0xC12, x0
   csrrc  x0,  0xC12, x5
   csrrci x0,  0xC12, 0x0a
   csrrs  x0,  0xC12, x5
   csrrsi x0,  0xC12, 0x0a
   csrrw  x0,  0xC12, x0
   csrrwi x0,  0xC12, 0x0a

   csrrc  x5,  0xC13, x0
   csrrc  x0,  0xC13, x5
   csrrci x0,  0xC13, 0x0a
   csrrs  x0,  0xC13, x5
   csrrsi x0,  0xC13, 0x0a
   csrrw  x0,  0xC13, x0
   csrrwi x0,  0xC13, 0x0a

   csrrc  x5,  0xC14, x0
   csrrc  x0,  0xC14, x5
   csrrci x0,  0xC14, 0x0a
   csrrs  x0,  0xC14, x5
   csrrsi x0,  0xC14, 0x0a
   csrrw  x0,  0xC14, x0
   csrrwi x0,  0xC14, 0x0a

   csrrc  x5,  0xC15, x0
   csrrc  x0,  0xC15, x5
   csrrci x0,  0xC15, 0x0a
   csrrs  x0,  0xC15, x5
   csrrsi x0,  0xC15, 0x0a
   csrrw  x0,  0xC15, x0
   csrrwi x0,  0xC15, 0x0a

   csrrc  x5,  0xC16, x0
   csrrc  x0,  0xC16, x5
   csrrci x0,  0xC16, 0x0a
   csrrs  x0,  0xC16, x5
   csrrsi x0,  0xC16, 0x0a
   csrrw  x0,  0xC16, x0
   csrrwi x0,  0xC16, 0x0a

   csrrc  x5,  0xC17, x0
   csrrc  x0,  0xC17, x5
   csrrci x0,  0xC17, 0x0a
   csrrs  x0,  0xC17, x5
   csrrsi x0,  0xC17, 0x0a
   csrrw  x0,  0xC17, x0
   csrrwi x0,  0xC17, 0x0a

   csrrc  x5,  0xC18, x0
   csrrc  x0,  0xC18, x5
   csrrci x0,  0xC18, 0x0a
   csrrs  x0,  0xC18, x5
   csrrsi x0,  0xC18, 0x0a
   csrrw  x0,  0xC18, x0
   csrrwi x0,  0xC18, 0x0a

   csrrc  x5,  0xC19, x0
   csrrc  x0,  0xC19, x5
   csrrci x0,  0xC19, 0x0a
   csrrs  x0,  0xC19, x5
   csrrsi x0,  0xC19, 0x0a
   csrrw  x0,  0xC19, x0
   csrrwi x0,  0xC19, 0x0a

   csrrc  x5,  0xC1A, x0
   csrrc  x0,  0xC1A, x5
   csrrci x0,  0xC1A, 0x0a
   csrrs  x0,  0xC1A, x5
   csrrsi x0,  0xC1A, 0x0a
   csrrw  x0,  0xC1A, x0
   csrrwi x0,  0xC1A, 0x0a

   csrrc  x5,  0xC1B, x0
   csrrc  x0,  0xC1B, x5
   csrrci x0,  0xC1B, 0x0a
   csrrs  x0,  0xC1B, x5
   csrrsi x0,  0xC1B, 0x0a
   csrrw  x0,  0xC1B, x0
   csrrwi x0,  0xC1B, 0x0a

   csrrc  x5,  0xC1C, x0
   csrrc  x0,  0xC1C, x5
   csrrci x0,  0xC1C, 0x0a
   csrrs  x0,  0xC1C, x5
   csrrsi x0,  0xC1C, 0x0a
   csrrw  x0,  0xC1C, x0
   csrrwi x0,  0xC1C, 0x0a

   csrrc  x5,  0xC1D, x0
   csrrc  x0,  0xC1D, x5
   csrrci x0,  0xC1D, 0x0a
   csrrs  x0,  0xC1D, x5
   csrrsi x0,  0xC1D, 0x0a
   csrrw  x0,  0xC1D, x0
   csrrwi x0,  0xC1D, 0x0a

   csrrc  x5,  0xC1E, x0
   csrrc  x0,  0xC1E, x5
   csrrci x0,  0xC1E, 0x0a
   csrrs  x0,  0xC1E, x5
   csrrsi x0,  0xC1E, 0x0a
   csrrw  x0,  0xC1E, x0
   csrrwi x0,  0xC1E, 0x0a

   csrrc  x5,  0xC1F, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xC1F, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  0xC1F, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xC1F, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xC1F, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xC1F, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xC1F, 0x0a   # illegal instruction: attempt to write RO CSR

### END HPM Performance Monitoring Counter (3-31)


######### HPM Upper Performance Monitoring Counter (3, 31) (hpmcounterh[3, 31])
### START
	csrrc  x5,  0xC83, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xC83, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  0xC83, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xC83, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xC83, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xC83, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xC83, 0x0a   # illegal instruction: attempt to write RO CSR

   csrrc  x5,  0xC84, x0
   csrrc  x0,  0xC84, x5
   csrrci x0,  0xC84, 0x0a
   csrrs  x0,  0xC84, x5
   csrrsi x0,  0xC84, 0x0a
   csrrw  x0,  0xC84, x0
   csrrwi x0,  0xC84, 0x0a

   csrrc  x5,  0xC85, x0
   csrrc  x0,  0xC85, x5
   csrrci x0,  0xC85, 0x0a
   csrrs  x0,  0xC85, x5
   csrrsi x0,  0xC85, 0x0a
   csrrw  x0,  0xC85, x0
   csrrwi x0,  0xC85, 0x0a

   csrrc  x5,  0xC86, x0
   csrrc  x0,  0xC86, x5
   csrrci x0,  0xC86, 0x0a
   csrrs  x0,  0xC86, x5
   csrrsi x0,  0xC86, 0x0a
   csrrw  x0,  0xC86, x0
   csrrwi x0,  0xC86, 0x0a

   csrrc  x5,  0xC87, x0
   csrrc  x0,  0xC87, x5
   csrrci x0,  0xC87, 0x0a
   csrrs  x0,  0xC87, x5
   csrrsi x0,  0xC87, 0x0a
   csrrw  x0,  0xC87, x0
   csrrwi x0,  0xC87, 0x0a

   csrrc  x5,  0xC88, x0
   csrrc  x0,  0xC88, x5
   csrrci x0,  0xC88, 0x0a
   csrrs  x0,  0xC88, x5
   csrrsi x0,  0xC88, 0x0a
   csrrw  x0,  0xC88, x0
   csrrwi x0,  0xC88, 0x0a

   csrrc  x5,  0xC89, x0
   csrrc  x0,  0xC89, x5
   csrrci x0,  0xC89, 0x0a
   csrrs  x0,  0xC89, x5
   csrrsi x0,  0xC89, 0x0a
   csrrw  x0,  0xC89, x0
   csrrwi x0,  0xC89, 0x0a

   csrrc  x5,  0xC8A, x0
   csrrc  x0,  0xC8A, x5
   csrrci x0,  0xC8A, 0x0a
   csrrs  x0,  0xC8A, x5
   csrrsi x0,  0xC8A, 0x0a
   csrrw  x0,  0xC8A, x0
   csrrwi x0,  0xC8A, 0x0a

   csrrc  x5,  0xC8B, x0
   csrrc  x0,  0xC8B, x5
   csrrci x0,  0xC8B, 0x0a
   csrrs  x0,  0xC8B, x5
   csrrsi x0,  0xC8B, 0x0a
   csrrw  x0,  0xC8B, x0
   csrrwi x0,  0xC8B, 0x0a

   csrrc  x5,  0xC8C, x0
   csrrc  x0,  0xC8C, x5
   csrrci x0,  0xC8C, 0x0a
   csrrs  x0,  0xC8C, x5
   csrrsi x0,  0xC8C, 0x0a
   csrrw  x0,  0xC8C, x0
   csrrwi x0,  0xC8C, 0x0a

   csrrc  x5,  0xC8D, x0
   csrrc  x0,  0xC8D, x5
   csrrci x0,  0xC8D, 0x0a
   csrrs  x0,  0xC8D, x5
   csrrsi x0,  0xC8D, 0x0a
   csrrw  x0,  0xC8D, x0
   csrrwi x0,  0xC8D, 0x0a

   csrrc  x5,  0xC8E, x0
   csrrc  x0,  0xC8E, x5
   csrrci x0,  0xC8E, 0x0a
   csrrs  x0,  0xC8E, x5
   csrrsi x0,  0xC8E, 0x0a
   csrrw  x0,  0xC8E, x0
   csrrwi x0,  0xC8E, 0x0a

   csrrc  x5,  0xC8F, x0
   csrrc  x0,  0xC8F, x5
   csrrci x0,  0xC8F, 0x0a
   csrrs  x0,  0xC8F, x5
   csrrsi x0,  0xC8F, 0x0a
   csrrw  x0,  0xC8F, x0
   csrrwi x0,  0xC8F, 0x0a

   csrrc  x5,  0xC90, x0
   csrrc  x0,  0xC90, x5
   csrrci x0,  0xC90, 0x0a
   csrrs  x0,  0xC90, x5
   csrrsi x0,  0xC90, 0x0a
   csrrw  x0,  0xC90, x0
   csrrwi x0,  0xC90, 0x0a

   csrrc  x5,  0xC91, x0
   csrrc  x0,  0xC91, x5
   csrrci x0,  0xC91, 0x0a
   csrrs  x0,  0xC91, x5
   csrrsi x0,  0xC91, 0x0a
   csrrw  x0,  0xC91, x0
   csrrwi x0,  0xC91, 0x0a

   csrrc  x5,  0xC92, x0
   csrrc  x0,  0xC92, x5
   csrrci x0,  0xC92, 0x0a
   csrrs  x0,  0xC92, x5
   csrrsi x0,  0xC92, 0x0a
   csrrw  x0,  0xC92, x0
   csrrwi x0,  0xC92, 0x0a

   csrrc  x5,  0xC93, x0
   csrrc  x0,  0xC93, x5
   csrrci x0,  0xC93, 0x0a
   csrrs  x0,  0xC93, x5
   csrrsi x0,  0xC93, 0x0a
   csrrw  x0,  0xC93, x0
   csrrwi x0,  0xC93, 0x0a

   csrrc  x5,  0xC94, x0
   csrrc  x0,  0xC94, x5
   csrrci x0,  0xC94, 0x0a
   csrrs  x0,  0xC94, x5
   csrrsi x0,  0xC94, 0x0a
   csrrw  x0,  0xC94, x0
   csrrwi x0,  0xC94, 0x0a

   csrrc  x5,  0xC95, x0
   csrrc  x0,  0xC95, x5
   csrrci x0,  0xC95, 0x0a
   csrrs  x0,  0xC95, x5
   csrrsi x0,  0xC95, 0x0a
   csrrw  x0,  0xC95, x0
   csrrwi x0,  0xC95, 0x0a

   csrrc  x5,  0xC96, x0
   csrrc  x0,  0xC96, x5
   csrrci x0,  0xC96, 0x0a
   csrrs  x0,  0xC96, x5
   csrrsi x0,  0xC96, 0x0a
   csrrw  x0,  0xC96, x0
   csrrwi x0,  0xC96, 0x0a

   csrrc  x5,  0xC97, x0
   csrrc  x0,  0xC97, x5
   csrrci x0,  0xC97, 0x0a
   csrrs  x0,  0xC97, x5
   csrrsi x0,  0xC97, 0x0a
   csrrw  x0,  0xC97, x0
   csrrwi x0,  0xC97, 0x0a

   csrrc  x5,  0xC98, x0
   csrrc  x0,  0xC98, x5
   csrrci x0,  0xC98, 0x0a
   csrrs  x0,  0xC98, x5
   csrrsi x0,  0xC98, 0x0a
   csrrw  x0,  0xC98, x0
   csrrwi x0,  0xC98, 0x0a

   csrrc  x5,  0xC99, x0
   csrrc  x0,  0xC99, x5
   csrrci x0,  0xC99, 0x0a
   csrrs  x0,  0xC99, x5
   csrrsi x0,  0xC99, 0x0a
   csrrw  x0,  0xC99, x0
   csrrwi x0,  0xC99, 0x0a

   csrrc  x5,  0xC9A, x0
   csrrc  x0,  0xC9A, x5
   csrrci x0,  0xC9A, 0x0a
   csrrs  x0,  0xC9A, x5
   csrrsi x0,  0xC9A, 0x0a
   csrrw  x0,  0xC9A, x0
   csrrwi x0,  0xC9A, 0x0a

   csrrc  x5,  0xC9B, x0
   csrrc  x0,  0xC9B, x5
   csrrci x0,  0xC9B, 0x0a
   csrrs  x0,  0xC9B, x5
   csrrsi x0,  0xC9B, 0x0a
   csrrw  x0,  0xC9B, x0
   csrrwi x0,  0xC9B, 0x0a

   csrrc  x5,  0xC9C, x0
   csrrc  x0,  0xC9C, x5
   csrrci x0,  0xC9C, 0x0a
   csrrs  x0,  0xC9C, x5
   csrrsi x0,  0xC9C, 0x0a
   csrrw  x0,  0xC9C, x0
   csrrwi x0,  0xC9C, 0x0a

   csrrc  x5,  0xC9D, x0
   csrrc  x0,  0xC9D, x5
   csrrci x0,  0xC9D, 0x0a
   csrrs  x0,  0xC9D, x5
   csrrsi x0,  0xC9D, 0x0a
   csrrw  x0,  0xC9D, x0
   csrrwi x0,  0xC9D, 0x0a

   csrrc  x5,  0xC9E, x0
   csrrc  x0,  0xC9E, x5
   csrrci x0,  0xC9E, 0x0a
   csrrs  x0,  0xC9E, x5
   csrrsi x0,  0xC9E, 0x0a
   csrrw  x0,  0xC9E, x0
   csrrwi x0,  0xC9E, 0x0a

   csrrc  x5,  0xC9F, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xC9F, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  0xC9F, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xC9F, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xC9F, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xC9F, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xC9F, 0x0a   # illegal instruction: attempt to write RO CSR

### END HPM Upper Performance Monitoring Counter (3-31)








###############################################################################
#
##   USER CUSTOM CSRs
#
###############################################################################

    # uhartid
    csrrc  x5,  0xCD0, x0     # illegal instructions: attempt access "non-existant" CSR
    csrrc  x0,  0xCD0, x5
    csrrci x0,  0xCD0, 0x0a
    csrrs  x0,  0xCD0, x5
    csrrsi x0,  0xCD0, 0x0a
    csrrw  x0,  0xCD0, x0
    csrrwi x0,  0xCD0, 0x0a

    # privlv
    csrrc  x5,  0xCD1, x0     # illegal instructions: attempt access "non-existant" CSR
    csrrc  x0,  0xCD1, x5
    csrrci x0,  0xCD1, 0x0a
    csrrs  x0,  0xCD1, x5
    csrrsi x0,  0xCD1, 0x0a
    csrrw  x0,  0xCD1, x0
    csrrwi x0,  0xCD1, 0x0a

    ##
    ## Access the User Custom CSRs.   These are all illegal instructions when
    ## COREV_PULP = 0 (which is the default for CV32E40P).
    ##

#if defined(PULP)
    # lpstart0
   csrrc  x5,  0xCC0, x0   # not illegal instruction: no attempt to write RO CSR
   csrrc  x0,  0xCC0, x5   # illegal instruction: attempt to write RO CSR
   csrrci x0,  0xCC0, 0x0a # illegal instruction: attempt to write RO CSR
   csrrs  x0,  0xCC0, x5   # illegal instruction: attempt to write RO CSR
   csrrsi x0,  0xCC0, 0x0a # illegal instruction: attempt to write RO CSR
   csrrw  x0,  0xCC0, x0   # illegal instruction: attempt to write RO CSR
   csrrwi x0,  0xCC0, 0x0a # illegal instruction: attempt to write RO CSR

   # check reset value
   csrrc  x5,  0xCC0, x0     # not illegal
	li     x30, 0x00000000
	bne    x5,  x30, fail

   # lpend0
   csrrc  x5,  0xCC1, x0   # not illegal instruction: no attempt to write RO CSR
   csrrc  x0,  0xCC1, x5   # illegal instruction: attempt to write RO CSR
   csrrci x0,  0xCC1, 0x0a # illegal instruction: attempt to write RO CSR
   csrrs  x0,  0xCC1, x5   # illegal instruction: attempt to write RO CSR
   csrrsi x0,  0xCC1, 0x0a # illegal instruction: attempt to write RO CSR
   csrrw  x0,  0xCC1, x0   # illegal instruction: attempt to write RO CSR
   csrrwi x0,  0xCC1, 0x0a # illegal instruction: attempt to write RO CSR

   # check reset value
   csrrc  x5,  0xCC1, x0     # not illegal
	li     x30, 0x00000000
	bne    x5,  x30, fail

   # lpcount0
   csrrc  x5,  0xCC2, x0   # not illegal instruction: no attempt to write RO CSR
   csrrc  x0,  0xCC2, x5   # illegal instruction: attempt to write RO CSR
   csrrci x0,  0xCC2, 0x0a # illegal instruction: attempt to write RO CSR
   csrrs  x0,  0xCC2, x5   # illegal instruction: attempt to write RO CSR
   csrrsi x0,  0xCC2, 0x0a # illegal instruction: attempt to write RO CSR
   csrrw  x0,  0xCC2, x0   # illegal instruction: attempt to write RO CSR
   csrrwi x0,  0xCC2, 0x0a # illegal instruction: attempt to write RO CSR

   # check reset value
   csrrc  x5,  0xCC2, x0     # not illegal
	li     x30, 0x00000000
	bne    x5,  x30, fail


   # lpstart1
   csrrc  x5,  0xCC4, x0   # not illegal instruction: no attempt to write RO CSR
   csrrc  x0,  0xCC4, x5   # illegal instruction: attempt to write RO CSR
   csrrci x0,  0xCC4, 0x0a # illegal instruction: attempt to write RO CSR
   csrrs  x0,  0xCC4, x5   # illegal instruction: attempt to write RO CSR
   csrrsi x0,  0xCC4, 0x0a # illegal instruction: attempt to write RO CSR
   csrrw  x0,  0xCC4, x0   # illegal instruction: attempt to write RO CSR
   csrrwi x0,  0xCC4, 0x0a # illegal instruction: attempt to write RO CSR

   # check reset value
   csrrc  x5,  0xCC4, x0     # not illegal
	li     x30, 0x00000000
	bne    x5,  x30, fail

   # lpend1
   csrrc  x5,  0xCC5, x0   # not illegal instruction: no attempt to write RO CSR
   csrrc  x0,  0xCC5, x5   # illegal instruction: attempt to write RO CSR
   csrrci x0,  0xCC5, 0x0a # illegal instruction: attempt to write RO CSR
   csrrs  x0,  0xCC5, x5   # illegal instruction: attempt to write RO CSR
   csrrsi x0,  0xCC5, 0x0a # illegal instruction: attempt to write RO CSR
   csrrw  x0,  0xCC5, x0   # illegal instruction: attempt to write RO CSR
   csrrwi x0,  0xCC5, 0x0a # illegal instruction: attempt to write RO CSR

   # check reset value
   csrrc  x5,  0xCC5, x0     # not illegal
	li     x30, 0x00000000
	bne    x5,  x30, fail

   # lpcount1
   csrrc  x5,  0xCC6, x0   # not illegal instruction: no attempt to write RO CSR
   csrrc  x0,  0xCC6, x5   # illegal instruction: attempt to write RO CSR
   csrrci x0,  0xCC6, 0x0a # illegal instruction: attempt to write RO CSR
   csrrs  x0,  0xCC6, x5   # illegal instruction: attempt to write RO CSR
   csrrsi x0,  0xCC6, 0x0a # illegal instruction: attempt to write RO CSR
   csrrw  x0,  0xCC6, x0   # illegal instruction: attempt to write RO CSR
   csrrwi x0,  0xCC6, 0x0a # illegal instruction: attempt to write RO CSR

   # check reset value
   csrrc  x5,  0xCC6, x0     # not illegal
	li     x30, 0x00000000
	bne    x5,  x30, fail

#else
    # lpstart0
    csrrc  x5,  0xCC0, x0     # illegal instructions: attempt access "non-existant" CSR
    csrrc  x0,  0xCC0, x5
    csrrci x0,  0xCC0, 0x0a
    csrrs  x0,  0xCC0, x5
    csrrsi x0,  0xCC0, 0x0a
    csrrw  x0,  0xCC0, x0
    csrrwi x0,  0xCC0, 0x0a

    # lpend0
    csrrc  x5,  0xCC1, x0     # illegal instructions: attempt access "non-existant" CSR
    csrrc  x0,  0xCC1, x5
    csrrci x0,  0xCC1, 0x0a
    csrrs  x0,  0xCC1, x5
    csrrsi x0,  0xCC1, 0x0a
    csrrw  x0,  0xCC1, x0
    csrrwi x0,  0xCC1, 0x0a

    # lpcount0
    csrrc  x5,  0xCC2, x0     # illegal instructions: attempt access "non-existant" CSR
    csrrc  x0,  0xCC2, x5
    csrrci x0,  0xCC2, 0x0a
    csrrs  x0,  0xCC2, x5
    csrrsi x0,  0xCC2, 0x0a
    csrrw  x0,  0xCC2, x0
    csrrwi x0,  0xCC2, 0x0a

    # lpstart1
    csrrc  x5,  0xCC4, x0     # illegal instructions: attempt access "non-existant" CSR
    csrrc  x0,  0xCC4, x5
    csrrci x0,  0xCC4, 0x0a
    csrrs  x0,  0xCC4, x5
    csrrsi x0,  0xCC4, 0x0a
    csrrw  x0,  0xCC4, x0
    csrrwi x0,  0xCC4, 0x0a

    # lpend1
    csrrc  x5,  0xCC5, x0     # illegal instructions: attempt access "non-existant" CSR
    csrrc  x0,  0xCC5, x5
    csrrci x0,  0xCC5, 0x0a
    csrrs  x0,  0xCC5, x5
    csrrsi x0,  0xCC5, 0x0a
    csrrw  x0,  0xCC5, x0
    csrrwi x0,  0xCC5, 0x0a

    # lpcount1
    csrrc  x5,  0xCC6, x0     # illegal instructions: attempt access "non-existant" CSR
    csrrc  x0,  0xCC6, x5
    csrrci x0,  0xCC6, 0x0a
    csrrs  x0,  0xCC6, x5
    csrrsi x0,  0xCC6, 0x0a
    csrrw  x0,  0xCC6, x0
    csrrwi x0,  0xCC6, 0x0a

#endif

# Start ZFINX RELATED
#if defined (PULP) && ( !defined (FPU) || (defined (FPU) && defined (ZFINX)))
# check reset value
    csrrc  x5,  0xCD2, x0   # read access are NOT illegal
    li     x30, ZFINX_RESET_VALUE
    bne    x5,  x30, fail

    csrrc  x0,  0xCD2, x5   # write access are illegal instruction
    csrrci x0,  0xCD2, 0x0a # write access are illegal instruction
    csrrs  x0,  0xCD2, x5   # write access are illegal instruction
    csrrsi x0,  0xCD2, 0x0a # write access are illegal instruction
    csrrw  x0,  0xCD2, x0   # write access are illegal instruction
    csrrwi x0,  0xCD2, 0x0a # write access are illegal instruction

#else
# ZFinx CSR not present, every access is illegal
   csrrc  x5,  0xCD2, x0   # illegal instruction : register not present
   csrrc  x0,  0xCD2, x5   # illegal instruction : register not present
   csrrci x0,  0xCD2, 0x0a # illegal instruction : register not present
   csrrs  x0,  0xCD2, x5   # illegal instruction : register not present
   csrrsi x0,  0xCD2, 0x0a # illegal instruction : register not present
   csrrw  x0,  0xCD2, x0   # illegal instruction : register not present
   csrrwi x0,  0xCD2, 0x0a # illegal instruction : register not present

#endif
# END ZFINX RELATED




###############################################################################
#
##   MACHINE CSRs
#
###############################################################################


   # mscratch
   # reset val 0
   csrrc  x5,  0x340, x0     # not illegal instruction: register present & read allowed
	li     x30, 0
	bne    x5,  x30, fail

   # write access
	csrrc  x0,  0x340, x5     # not illegal instruction
	csrrci x5,  0x340, 0x0a   # not illegal instruction
	csrrs  x0,  0x340, x5     # not illegal instruction
 	csrrsi x0,  0x340, 0x0a   # not illegal instruction
 	csrrw  x0,  0x340, x0     # not illegal instruction
	csrrwi x0,  0x340, 0x0a   # not illegal instruction



   # misa
	csrrc  x5,  0x301, x0     # not illegal instruction: no attempt to write RO CSR
	li     x30, MISA_RESET_VAL
	bne    x5,  x30, fail

   # write access
	csrrc  x0,  0x301, x5     # not illegal instruction: write is ignored and not illegal
	csrrci x5,  0x301, 0x0a   # not illegal instruction: write is ignored and not illegal
	csrrs  x0,  0x301, x5     # not illegal instruction: write is ignored and not illegal
 	csrrsi x0,  0x301, 0x0a   # not illegal instruction: write is ignored and not illegal
 	csrrw  x0,  0x301, x0     # not illegal instruction: write is ignored and not illegal
	csrrwi x0,  0x301, 0x0a   # not illegal instruction: write is ignored and not illegal


   # MHPMEVENTx START
   # mhpmevent3
   csrrc  x5,  0x323, x0
   csrrc  x0,  0x323, x5
   csrrci x0,  0x323, 0x0a
   csrrs  x0,  0x323, x5
   csrrsi x0,  0x323, 0x0a
   csrrw  x0,  0x323, x0
   csrrwi x0,  0x323, 0x0a

   csrrc  x5,  0x324, x0
   csrrc  x0,  0x324, x5
   csrrci x0,  0x324, 0x0a
   csrrs  x0,  0x324, x5
   csrrsi x0,  0x324, 0x0a
   csrrw  x0,  0x324, x0
   csrrwi x0,  0x324, 0x0a

   csrrc  x5,  0x325, x0
   csrrc  x0,  0x325, x5
   csrrci x0,  0x325, 0x0a
   csrrs  x0,  0x325, x5
   csrrsi x0,  0x325, 0x0a
   csrrw  x0,  0x325, x0
   csrrwi x0,  0x325, 0x0a

   csrrc  x5,  0x326, x0
   csrrc  x0,  0x326, x5
   csrrci x0,  0x326, 0x0a
   csrrs  x0,  0x326, x5
   csrrsi x0,  0x326, 0x0a
   csrrw  x0,  0x326, x0
   csrrwi x0,  0x326, 0x0a

   csrrc  x5,  0x327, x0
   csrrc  x0,  0x327, x5
   csrrci x0,  0x327, 0x0a
   csrrs  x0,  0x327, x5
   csrrsi x0,  0x327, 0x0a
   csrrw  x0,  0x327, x0
   csrrwi x0,  0x327, 0x0a

   csrrc  x5,  0x328, x0
   csrrc  x0,  0x328, x5
   csrrci x0,  0x328, 0x0a
   csrrs  x0,  0x328, x5
   csrrsi x0,  0x328, 0x0a
   csrrw  x0,  0x328, x0
   csrrwi x0,  0x328, 0x0a

   csrrc  x5,  0x329, x0
   csrrc  x0,  0x329, x5
   csrrci x0,  0x329, 0x0a
   csrrs  x0,  0x329, x5
   csrrsi x0,  0x329, 0x0a
   csrrw  x0,  0x329, x0
   csrrwi x0,  0x329, 0x0a

   csrrc  x5,  0x32A, x0
   csrrc  x0,  0x32A, x5
   csrrci x0,  0x32A, 0x0a
   csrrs  x0,  0x32A, x5
   csrrsi x0,  0x32A, 0x0a
   csrrw  x0,  0x32A, x0
   csrrwi x0,  0x32A, 0x0a

   csrrc  x5,  0x32B, x0
   csrrc  x0,  0x32B, x5
   csrrci x0,  0x32B, 0x0a
   csrrs  x0,  0x32B, x5
   csrrsi x0,  0x32B, 0x0a
   csrrw  x0,  0x32B, x0
   csrrwi x0,  0x32B, 0x0a

   csrrc  x5,  0x32C, x0
   csrrc  x0,  0x32C, x5
   csrrci x0,  0x32C, 0x0a
   csrrs  x0,  0x32C, x5
   csrrsi x0,  0x32C, 0x0a
   csrrw  x0,  0x32C, x0
   csrrwi x0,  0x32C, 0x0a

   csrrc  x5,  0x32D, x0
   csrrc  x0,  0x32D, x5
   csrrci x0,  0x32D, 0x0a
   csrrs  x0,  0x32D, x5
   csrrsi x0,  0x32D, 0x0a
   csrrw  x0,  0x32D, x0
   csrrwi x0,  0x32D, 0x0a

   csrrc  x5,  0x32E, x0
   csrrc  x0,  0x32E, x5
   csrrci x0,  0x32E, 0x0a
   csrrs  x0,  0x32E, x5
   csrrsi x0,  0x32E, 0x0a
   csrrw  x0,  0x32E, x0
   csrrwi x0,  0x32E, 0x0a

   csrrc  x5,  0x32F, x0
   csrrc  x0,  0x32F, x5
   csrrci x0,  0x32F, 0x0a
   csrrs  x0,  0x32F, x5
   csrrsi x0,  0x32F, 0x0a
   csrrw  x0,  0x32F, x0
   csrrwi x0,  0x32F, 0x0a

   csrrc  x5,  0x330, x0
   csrrc  x0,  0x330, x5
   csrrci x0,  0x330, 0x0a
   csrrs  x0,  0x330, x5
   csrrsi x0,  0x330, 0x0a
   csrrw  x0,  0x330, x0
   csrrwi x0,  0x330, 0x0a

   csrrc  x5,  0x331, x0
   csrrc  x0,  0x331, x5
   csrrci x0,  0x331, 0x0a
   csrrs  x0,  0x331, x5
   csrrsi x0,  0x331, 0x0a
   csrrw  x0,  0x331, x0
   csrrwi x0,  0x331, 0x0a

   csrrc  x5,  0x332, x0
   csrrc  x0,  0x332, x5
   csrrci x0,  0x332, 0x0a
   csrrs  x0,  0x332, x5
   csrrsi x0,  0x332, 0x0a
   csrrw  x0,  0x332, x0
   csrrwi x0,  0x332, 0x0a

   csrrc  x5,  0x333, x0
   csrrc  x0,  0x333, x5
   csrrci x0,  0x333, 0x0a
   csrrs  x0,  0x333, x5
   csrrsi x0,  0x333, 0x0a
   csrrw  x0,  0x333, x0
   csrrwi x0,  0x333, 0x0a

   csrrc  x5,  0x334, x0
   csrrc  x0,  0x334, x5
   csrrci x0,  0x334, 0x0a
   csrrs  x0,  0x334, x5
   csrrsi x0,  0x334, 0x0a
   csrrw  x0,  0x334, x0
   csrrwi x0,  0x334, 0x0a

   csrrc  x5,  0x335, x0
   csrrc  x0,  0x335, x5
   csrrci x0,  0x335, 0x0a
   csrrs  x0,  0x335, x5
   csrrsi x0,  0x335, 0x0a
   csrrw  x0,  0x335, x0
   csrrwi x0,  0x335, 0x0a

   csrrc  x5,  0x336, x0
   csrrc  x0,  0x336, x5
   csrrci x0,  0x336, 0x0a
   csrrs  x0,  0x336, x5
   csrrsi x0,  0x336, 0x0a
   csrrw  x0,  0x336, x0
   csrrwi x0,  0x336, 0x0a

   csrrc  x5,  0x337, x0
   csrrc  x0,  0x337, x5
   csrrci x0,  0x337, 0x0a
   csrrs  x0,  0x337, x5
   csrrsi x0,  0x337, 0x0a
   csrrw  x0,  0x337, x0
   csrrwi x0,  0x337, 0x0a

   csrrc  x5,  0x338, x0
   csrrc  x0,  0x338, x5
   csrrci x0,  0x338, 0x0a
   csrrs  x0,  0x338, x5
   csrrsi x0,  0x338, 0x0a
   csrrw  x0,  0x338, x0
   csrrwi x0,  0x338, 0x0a

   csrrc  x5,  0x339, x0
   csrrc  x0,  0x339, x5
   csrrci x0,  0x339, 0x0a
   csrrs  x0,  0x339, x5
   csrrsi x0,  0x339, 0x0a
   csrrw  x0,  0x339, x0
   csrrwi x0,  0x339, 0x0a

   csrrc  x5,  0x33A, x0
   csrrc  x0,  0x33A, x5
   csrrci x0,  0x33A, 0x0a
   csrrs  x0,  0x33A, x5
   csrrsi x0,  0x33A, 0x0a
   csrrw  x0,  0x33A, x0
   csrrwi x0,  0x33A, 0x0a

   csrrc  x5,  0x33B, x0
   csrrc  x0,  0x33B, x5
   csrrci x0,  0x33B, 0x0a
   csrrs  x0,  0x33B, x5
   csrrsi x0,  0x33B, 0x0a
   csrrw  x0,  0x33B, x0
   csrrwi x0,  0x33B, 0x0a

   csrrc  x5,  0x33C, x0
   csrrc  x0,  0x33C, x5
   csrrci x0,  0x33C, 0x0a
   csrrs  x0,  0x33C, x5
   csrrsi x0,  0x33C, 0x0a
   csrrw  x0,  0x33C, x0
   csrrwi x0,  0x33C, 0x0a

   csrrc  x5,  0x33D, x0
   csrrc  x0,  0x33D, x5
   csrrci x0,  0x33D, 0x0a
   csrrs  x0,  0x33D, x5
   csrrsi x0,  0x33D, 0x0a
   csrrw  x0,  0x33D, x0
   csrrwi x0,  0x33D, 0x0a

   csrrc  x5,  0x33E, x0
   csrrc  x0,  0x33E, x5
   csrrci x0,  0x33E, 0x0a
   csrrs  x0,  0x33E, x5
   csrrsi x0,  0x33E, 0x0a
   csrrw  x0,  0x33E, x0
   csrrwi x0,  0x33E, 0x0a

   # mhpmevent31
   csrrc  x5,  0x33F, x0
   csrrc  x0,  0x33F, x5
   csrrci x0,  0x33F, 0x0a
   csrrs  x0,  0x33F, x5
   csrrsi x0,  0x33F, 0x0a
   csrrw  x0,  0x33F, x0
   csrrwi x0,  0x33F, 0x0a
   # MHPMEVENTx END

	# mvendorid
	csrrc  x5,  0xF11, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xF11, x5     # illegal instruction: attempt to write RO CSR
	csrrci x5,  0xF11, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xF11, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xF11, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xF11, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xF11, 0x0a   # illegal instruction: attempt to write RO CSR

	csrrc  x5,  0xF11, x0     # not illegal
	li     x30, 0x00000602
	bne    x5,  x30, fail

	# marchid
	csrrc  x5,  0xF12, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xF12, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  0xF12, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xF12, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xF12, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xF12, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xF12, 0x0a   # illegal instruction: attempt to write RO CSR

	csrrc  x5,  0xF12, x0     # not illegal
	li     x30, 0x00000004
	bne    x5,  x30, fail

	# mimpid
	csrrc  x5,  0xF13, x0     # not illegal instruction: no attempt to write RO CSR
	csrrc  x0,  0xF13, x5     # illegal instruction: attempt to write RO CSR
	csrrci x0,  0xF13, 0x0a   # illegal instruction: attempt to write RO CSR
	csrrs  x0,  0xF13, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xF13, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xF13, x0     # illegal instruction: attempt to write RO CSR
	csrrwi x0,  0xF13, 0x0a   # illegal instruction: attempt to write RO CSR

	csrrc  x5,  0xF13, x0     # not illegal
   #if defined(PULP) || defined(FPU)
	li     x30, 0x00000001
   #else
	li     x30, 0x00000000
   #endif
	bne    x5,  x30, fail

   # mhartid
   csrrc  x5,  0xF14, x0     # not illegal instruction: no attempt to write RO CSR
   csrrc  x0,  0xF14, x5     # illegal instruction: attempt to write RO CSR
   csrrci x0,  0xF14, 0x0a   # illegal instruction: attempt to write RO CSR
   csrrs  x0,  0xF14, x5     # illegal instruction: attempt to write RO CSR
 	csrrsi x0,  0xF14, 0x0a   # illegal instruction: attempt to write RO CSR
 	csrrw  x0,  0xF14, x0     # illegal instruction: attempt to write RO CSR
   csrrwi x0,  0xF14, 0x0a   # illegal instruction: attempt to write RO CSR

	csrrc  x5,  0xF14, x0     # not illegal
	li     x30, 0x00000000
	bne    x5,  x30, fail



# Start PMPCFG RELATED
   # pmpcfg[0-3]
   csrrc  x5,  0x3A0, x0   # illegal instruction : register not present
   csrrc  x0,  0x3A0, x5   # illegal instruction : register not present
   csrrci x0,  0x3A0, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3A0, x5   # illegal instruction : register not present
   csrrsi x0,  0x3A0, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3A0, x0   # illegal instruction : register not present
   csrrwi x0,  0x3A0, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3A1, x0   # illegal instruction : register not present
   csrrc  x0,  0x3A1, x5   # illegal instruction : register not present
   csrrci x0,  0x3A1, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3A1, x5   # illegal instruction : register not present
   csrrsi x0,  0x3A1, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3A1, x0   # illegal instruction : register not present
   csrrwi x0,  0x3A1, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3A2, x0   # illegal instruction : register not present
   csrrc  x0,  0x3A2, x5   # illegal instruction : register not present
   csrrci x0,  0x3A2, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3A2, x5   # illegal instruction : register not present
   csrrsi x0,  0x3A2, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3A2, x0   # illegal instruction : register not present
   csrrwi x0,  0x3A2, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3A3, x0   # illegal instruction : register not present
   csrrc  x0,  0x3A3, x5   # illegal instruction : register not present
   csrrci x0,  0x3A3, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3A3, x5   # illegal instruction : register not present
   csrrsi x0,  0x3A3, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3A3, x0   # illegal instruction : register not present
   csrrwi x0,  0x3A3, 0x0a # illegal instruction : register not present
# END PMPCFG RELATED

# Start PMPADDRESS RELATED
   csrrc  x5,  0x3B0, x0   # illegal instruction : register not present
   csrrc  x0,  0x3B0, x5   # illegal instruction : register not present
   csrrci x0,  0x3B0, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3B0, x5   # illegal instruction : register not present
   csrrsi x0,  0x3B0, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3B0, x0   # illegal instruction : register not present
   csrrwi x0,  0x3B0, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3B1, x0   # illegal instruction : register not present
   csrrc  x0,  0x3B1, x5   # illegal instruction : register not present
   csrrci x0,  0x3B1, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3B1, x5   # illegal instruction : register not present
   csrrsi x0,  0x3B1, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3B1, x0   # illegal instruction : register not present
   csrrwi x0,  0x3B1, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3B2, x0   # illegal instruction : register not present
   csrrc  x0,  0x3B2, x5   # illegal instruction : register not present
   csrrci x0,  0x3B2, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3B2, x5   # illegal instruction : register not present
   csrrsi x0,  0x3B2, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3B2, x0   # illegal instruction : register not present
   csrrwi x0,  0x3B2, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3B3, x0   # illegal instruction : register not present
   csrrc  x0,  0x3B3, x5   # illegal instruction : register not present
   csrrci x0,  0x3B3, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3B3, x5   # illegal instruction : register not present
   csrrsi x0,  0x3B3, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3B3, x0   # illegal instruction : register not present
   csrrwi x0,  0x3B3, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3B4, x0   # illegal instruction : register not present
   csrrc  x0,  0x3B4, x5   # illegal instruction : register not present
   csrrci x0,  0x3B4, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3B4, x5   # illegal instruction : register not present
   csrrsi x0,  0x3B4, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3B4, x0   # illegal instruction : register not present
   csrrwi x0,  0x3B4, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3B5, x0   # illegal instruction : register not present
   csrrc  x0,  0x3B5, x5   # illegal instruction : register not present
   csrrci x0,  0x3B5, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3B5, x5   # illegal instruction : register not present
   csrrsi x0,  0x3B5, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3B5, x0   # illegal instruction : register not present
   csrrwi x0,  0x3B5, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3B6, x0   # illegal instruction : register not present
   csrrc  x0,  0x3B6, x5   # illegal instruction : register not present
   csrrci x0,  0x3B6, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3B6, x5   # illegal instruction : register not present
   csrrsi x0,  0x3B6, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3B6, x0   # illegal instruction : register not present
   csrrwi x0,  0x3B6, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3B7, x0   # illegal instruction : register not present
   csrrc  x0,  0x3B7, x5   # illegal instruction : register not present
   csrrci x0,  0x3B7, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3B7, x5   # illegal instruction : register not present
   csrrsi x0,  0x3B7, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3B7, x0   # illegal instruction : register not present
   csrrwi x0,  0x3B7, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3B8, x0   # illegal instruction : register not present
   csrrc  x0,  0x3B8, x5   # illegal instruction : register not present
   csrrci x0,  0x3B8, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3B8, x5   # illegal instruction : register not present
   csrrsi x0,  0x3B8, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3B8, x0   # illegal instruction : register not present
   csrrwi x0,  0x3B8, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3B9, x0   # illegal instruction : register not present
   csrrc  x0,  0x3B9, x5   # illegal instruction : register not present
   csrrci x0,  0x3B9, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3B9, x5   # illegal instruction : register not present
   csrrsi x0,  0x3B9, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3B9, x0   # illegal instruction : register not present
   csrrwi x0,  0x3B9, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3BA, x0   # illegal instruction : register not present
   csrrc  x0,  0x3BA, x5   # illegal instruction : register not present
   csrrci x0,  0x3BA, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3BA, x5   # illegal instruction : register not present
   csrrsi x0,  0x3BA, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3BA, x0   # illegal instruction : register not present
   csrrwi x0,  0x3BA, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3BB, x0   # illegal instruction : register not present
   csrrc  x0,  0x3BB, x5   # illegal instruction : register not present
   csrrci x0,  0x3BB, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3BB, x5   # illegal instruction : register not present
   csrrsi x0,  0x3BB, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3BB, x0   # illegal instruction : register not present
   csrrwi x0,  0x3BB, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3BC, x0   # illegal instruction : register not present
   csrrc  x0,  0x3BC, x5   # illegal instruction : register not present
   csrrci x0,  0x3BC, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3BC, x5   # illegal instruction : register not present
   csrrsi x0,  0x3BC, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3BC, x0   # illegal instruction : register not present
   csrrwi x0,  0x3BC, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3BD, x0   # illegal instruction : register not present
   csrrc  x0,  0x3BD, x5   # illegal instruction : register not present
   csrrci x0,  0x3BD, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3BD, x5   # illegal instruction : register not present
   csrrsi x0,  0x3BD, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3BD, x0   # illegal instruction : register not present
   csrrwi x0,  0x3BD, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3BE, x0   # illegal instruction : register not present
   csrrc  x0,  0x3BE, x5   # illegal instruction : register not present
   csrrci x0,  0x3BE, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3BE, x5   # illegal instruction : register not present
   csrrsi x0,  0x3BE, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3BE, x0   # illegal instruction : register not present
   csrrwi x0,  0x3BE, 0x0a # illegal instruction : register not present

   csrrc  x5,  0x3BF, x0   # illegal instruction : register not present
   csrrc  x0,  0x3BF, x5   # illegal instruction : register not present
   csrrci x0,  0x3BF, 0x0a # illegal instruction : register not present
   csrrs  x0,  0x3BF, x5   # illegal instruction : register not present
   csrrsi x0,  0x3BF, 0x0a # illegal instruction : register not present
   csrrw  x0,  0x3BF, x0   # illegal instruction : register not present
   csrrwi x0,  0x3BF, 0x0a # illegal instruction : register not present

# END PMPCFG RELATED




###############################################################################
    lw      x5,80(sp)
    bne     x5, x6, fail
    lw      x5,76(sp)
    bne     x5, x7, fail
    lw      x5,72(sp)
    bne     x5, x8, fail
    lw      x5,68(sp)
    bne     x5, x9, fail
    lw      x5,64(sp)
    bne     x5, x10, fail
    lw      x5,60(sp)
    bne     x5, x11, fail
    lw      x5,56(sp)
    bne     x5, x12, fail
    lw      x5,52(sp)
    bne     x5, x13, fail
    lw      x5,48(sp)
    bne     x5, x14, fail
    lw      x5,44(sp)
    bne     x5, x15, fail
    lw      x5,40(sp)
    bne     x5, x16, fail
    lw      x5,36(sp)
    bne     x5, x17, fail
    lw      x5,32(sp)
    bne     x5, x18, fail
    lw      x5,28(sp)
    bne     x5, x19, fail
    lw      x5,24(sp)
    bne     x5, x20, fail
    lw      x5,20(sp)
    bne     x5, x21, fail
    lw      x5,16(sp)
    bne     x5, x22, fail
    lw      x5,12(sp)
    bne     x5, x23, fail
    lw      x5,8(sp)
    bne     x5, x24, fail
    lw      x5,4(sp)
    bne     x5, x25, fail
    addi    sp,sp,84
    li x18, TEST_PASS
    li x16, EXPECTED_ILLEGAL_INSTRUCTIONS
    beq x31, x16, test_end
fail:
    li x18, TEST_FAIL
test_end:
    li x17, VIRT_PERIPH_STATUS_FLAG_ADDR
    sw x18,0(x17)
    j _exit

# The "sw_irq_handler" is entered on each illegal instruction.  Clears
# mepc and increments the illegal instruction count in x31.
u_sw_irq_handler:
    li x30, 0xf
    csrrc x29, mcause, x0
    and x30, x29, x30
    li x28, 2
    bne x30, x28, _exit
    csrrc x27, mepc, x0
    c.addi x27, 4
    csrrw x0, mepc, x27
    c.addi x31, 1
    mret

_exit:
    j _exit

debug:
    j _exit
