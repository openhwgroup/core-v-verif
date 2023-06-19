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

.global change_mode
.global umode
.global umode_jmp

.global load4addr
.global store2addr

// changes modes
change_mode:
// changes to User mode
umode:
  // set mstatus to U mode
  li t0, 0x1800
  // mstatus = 0x300
  csrrc x0, 0x300, t0
  // assing ra to mepc
  csrrw x0, 0x341, ra
  la a0, umode_msg
  jal ra, puts

  // return to next line in main and complete switch to Umode
  mret

// load4addr(int toread/ output, uint32_t addr)
load4addr:
// setup stack
  addi sp, sp, -8
  sw ra, 4(sp)

  // write to argument a0 from addr a1
  // load content from address a1 to t0
  lw t0, 0(a1)
  // store t0 to address a0 (argument)
  sw t0, 0(a0)

// pop stack
  lw ra,4(sp)
  addi sp,sp,8
  ret

// store2addr(int towrite/ input, uint32_t addr)
store2addr:
// setup stack
  addi sp, sp, -8
  sw ra, 4(sp)

  // write argument to address
  sw a0, 0(a1)

// pop stack
  addi x0, x0, 0 //mret in intr jmps to the next line
  lw ra,4(sp)
  addi sp,sp,8
  ret


// void umode_jmp(uint32_t *addr)
umode_jmp:
  csrrw x0, mepc, a0

  // set mstatus to U mode
  li t0, 0x1800
  // mstatus = 0x300
  csrrc x0, 0x300, t0

  // Put a jump instr in *addr
  la t1, myjal
  lw t1, 0(t1)
  sw t1, 0(a0)

  la t0, myret
  mret

// jumps to myret
myjal:
  jalr x0, t0

myret:
  nop // this line should trap
  ret // return to the C file after the umode_jmp

.section .rodata
umode_msg:
  .string "\tU-mode\n"
