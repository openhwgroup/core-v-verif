/*
**
** Copyright 2020 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
** SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
**/

.globl main
.globl exit
.section .text

#define TEST_PASS 123456789
#define TEST_FAIL 1

main:
  li s0, 0  // bit position counter
.basic_test:

  li t0, 1           // t0 = 0x00000001 -> bit 0 is 1
  sll t0, t0, s0     // t0 = 1 << s0 
  csrw mscratch, t0  // store in CSR
  csrr t1, mscratch  // read from CSR
  bne t1, t0, .fail  // verify written vs read value
  addi s0, s0, 1     // increment
  li t2, 32          // load total test
  blt s0, t2, .basic_test   // if s0 < 32, loop
  /*  
t0 = 0x00000001
t0 = 0x00000001 << 0 = 0x00000001
WRITE: mscratch = 0x00000001
READ: t1 = mscratch
CHECK: Is t1 == 0x00000001?

t0 = 0x00000001
t0 = 0x00000001 << 1 = 0x00000002
WRITE: mscratch = 0x00000002
READ: t1 = mscratch
CHECK: Is t1 == 0x00000002?
*/

  li s0, 0
.complement_test:
  li t0, 0xFFFFFFFF         // load all 1 into t0
  li t2, 1                  // load 1 into t2
  sll t2, t2, s0            // s0: t2 = 1 << bit_pos
  not t2, t2                // ¬(1<< bit pos) set all bits to 1 except n position
  and t0, t0, t2            // t0 = 0xFFFFFFFF &  ~(1 << bit_position)
  csrw mscratch, t0         // write mscratch
  csrr t1, mscratch         // read back
  bne t1, t0, .fail         // compare values
  addi s0, s0, 1            // increment
  li t2, 32                 // load loop limit
  blt s0, t2, .complement_test // loop if s0< 32
/*
t0 = 1111 1111 1111 1111 1111 1111 1111 1111
t2 = 0000 0000 0000 0000 0000 0000 0000 0001

t2 = 0000 0000 0000 0000 0000 0000 0000 0001 << 3
t2 = 0000 0000 0000 0000 0000 0000 0000 1000
t2 = 1111 1111 1111 1111 1111 1111 1111 0111

t0 = 1111 1111 1111 1111 1111 1111 1111 1111
    &
t2 = 1111 1111 1111 1111 1111 1111 1111 0111
    =
t0 = 1111 1111 1111 1111 1111 1111 1111 0111
*/


  li t0, 0x00000000   // load zero
  csrw mscratch, t0   // write to mscratch
  csrr t1, mscratch   // read back
  bne t1, t0, .fail   // verify that it is equal
  
  li t0, 0xFFFFFFFF   // load all bits 1 
  csrw mscratch, t0   // write to mscratch
  csrr t1, mscratch   // read back
  bne t1, t0, .fail   // verify that it is equal
  
 
  li t0, 0x55555555  // every 4 bit group is 0101 
  csrw mscratch, t0  // write to mscratch
  csrr t1, mscratch  // read back
  bne t1, t0, .fail  // verify that it is equal
  
  # All tests passed
  li s1, TEST_PASS
  j _exit

.fail:
  li s1, TEST_FAIL
  j _exit