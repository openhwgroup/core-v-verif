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
// Description : Higlights unecessary Register File multiple writes
// 

#include <stdio.h>

int main()
{
  int error = 0;

  long int a, b;
  long long int mul64;
  long int div32;

  volatile long int *p = 0x2000;
  volatile long int *p_unaligned = 0x2002;
  volatile long int aligned_load, unaligned_load;

  // MULH
  a = 0x12345678;
  b = 0x98765432;

  __asm__ volatile("nop");
  __asm__ volatile("nop");
  __asm__ volatile("mulh %0, %1, %2" : "=r"(mul64) : "r"(a), "r"(b));

  if (mul64 != 0xf8a326fb) {
    error++;
  }

  // DIV
  a = 10;

  __asm__ volatile("nop");
  __asm__ volatile("nop");
  __asm__ volatile("div %0, %1, %2" : "=r"(div32) : "r"(b), "r"(a));

  if (div32 != 0xf5a56ed2) {
    error++;
  }

  // LOAD
  a = 0x55555555;
  b = 0xaaaaaaaa;

  p[0] = a;
  p[1] = b;

  __asm__ volatile("nop");
  __asm__ volatile("nop");
  __asm__ volatile("lw %0, 0(%1)" : "=r"(aligned_load) : "r"(p));

  if (aligned_load != 0x55555555) {
    error++;
  }

  // MISALIGNED LOAD
  a = 0x87654321;
  b = 0x0fedcba9;

  p[0] = a;
  p[1] = b;

  __asm__ volatile("nop");
  __asm__ volatile("nop");
  __asm__ volatile("lw %0, 2(%1)" : "=r"(unaligned_load) : "r"(p));

  if (unaligned_load != 0xcba98765) {
    error++;
  }

#ifdef PULP
  // POST-INC LOAD
  a = 0x55555555;
  b = 0xaaaaaaaa;

  p[0] = a;
  p[1] = b;

  __asm__ volatile("nop");
  __asm__ volatile("nop");
  __asm__ volatile("cv.lw %0, (%1), 4" : "=r"(aligned_load) : "r"(p));

  if (aligned_load != 0x55555555) {
    error++;
  }

  // MISALIGNED POST-INC LOAD
  __asm__ volatile("addi %0, %1, -4" : "=r"(p) : "r"(p));
  a = 0x87654321;
  b = 0x0fedcba9;

  p[0] = a;
  p[1] = b;

  __asm__ volatile("nop");
  __asm__ volatile("nop");
  __asm__ volatile("cv.lw %0, (%1), 4" : "=r"(unaligned_load) : "r"(p_unaligned));

  if (unaligned_load != 0xcba98765) {
    error++;
  }
#endif

  return error;
}
