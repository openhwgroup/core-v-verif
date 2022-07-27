// Copyright 2022 OpenHW Group
// Copyright 2022 Silicon Labs, Inc.
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

.section .text


.global tor_zero

tor_zero:
// setup stack
  addi sp, sp, -288
  sw ra, 284(sp)
  sw s0, 280(sp)
  addi s0, sp, 288

// designate a range for addr0, base=0x2000
  li a5,0x2000>>2
  // addi a5, a5, 2000
  csrrw x0, 0x3b0, a5

  //set cfg0.torR
  csrrwi x0, 0x3a0, 0xf

  call change_mode

  // load from designated range
  li t0, 0x1fd0
  lw a1, 0(t0)
  // la a0, loadpass_msg
  // jal ra, puts

// pop stack
  lw s0,280(sp)
  lw ra,284(sp)
  addi sp,sp,288
  jr ra

.section .rodata
loadpass_msg:
  .string "\n\t back in M mode \n"


// loadram:
//   addi sp,sp,-288
//   sw ra,284(sp)
//   sw s0,280(sp)
//   addi s0,sp,288
//   addi a5,s0,-276
//   li a4,256
//   mv a2,a4
//   li a1,0
//   mv a0,a5
//   call memset
//   sw zero,-20(s0)
//   j .L2
// .L3:
//   lw a4,-20(s0)
//   li a5,4096
//   addi a5,a5,-2048
//   add a5,a4,a5
//   slli a5,a5,2
//   lw a4, 0(a5)
//   lw a5,-20(s0)
//   slli a5,a5,2
//   addi a5,a5,-16
//   add a5,a5,s0
//   sw a4,-260(a5)
//   lw a5,-20(s0)
//   addi a5,a5,1
//   sw a5,-20(s0)
// .L2:
//   lw a4,-20(s0)
//   li a5,63
//   ble a4,a5,.L3
//   nop
//   nop
//   lw ra,284(sp)
//   lw s0,280(sp)
//   addi sp,sp,288
//   jr ra
