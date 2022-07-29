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

.global xr_test
.global xw_test
.global loadtrap

xr_test:
// xr_test(int toread/ output, uint32_t addr)
// setup stack
  addi sp, sp, -28
  sw ra, 24(sp)
  sw s0, 20(sp)
  addi s0, sp, 28

  // write to argument a0 from addr a1
  // load content from address a1 to t0
  lw t0, 0(a1)
  // store t0 to address a0 (argument)
  sw t0, 0(a0)

// pop stack
  lw s0,20(sp)
  lw ra,24(sp)
  addi sp,sp,28
  jr ra

xw_test:
// xw_test(int towrite/ input, uint32_t addr)
// setup stack
  addi sp, sp, -28
  sw ra, 24(sp)
  sw s0, 20(sp)
  addi s0, sp, 28

  // write argument to address
  sw a0, 0(a1)

// pop stack
  lw s0,20(sp)
  lw ra,24(sp)
  addi sp,sp,28
  jr ra

loadtrap:
  // setup stack
  addi sp, sp, -28
  sw ra, 24(sp)
  sw s0, 20(sp)
  addi s0, sp, 28

  // addiw t0, zero, 0x8888
  li t0, 0x8888
  li t1, 11
  sw t1, 0(t0)

  // pop stack
  lw s0,20(sp)
  lw ra,24(sp)
  addi sp,sp,28
  jr ra

.section .rodata
exe_msg:
  .string "\n\t xr tested, back in M mode \n"

load_msg:
  .string "\n\t load, back in M mode \n"
