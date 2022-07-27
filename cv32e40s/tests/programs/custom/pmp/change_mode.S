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

change_mode:

umode:
  // addi sp, sp, -4
  // sw s0, 0(sp)
  // set mstatus to U mode
  li t0, 0x1800
  csrrc x0, 0x300, t0
  // assing ra to mepc
  csrrw x0, 0x341, ra
  la a0, umode_msg
  jal ra, puts

  // lw s0, 4(sp)
  // add sp, sp, 4
  // return to next line in main and complete switch to Umode
  mret

.section .rodata
umode_msg:
  .string "\n\tSwiting to U mode\n"
