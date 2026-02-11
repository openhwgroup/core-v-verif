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

  volatile unsigned int pc_save, check_result, pc_save_mem, pc_save_2;


  __asm__ volatile("nop");
  __asm__ volatile("nop");


  pc_save_mem = 0;

// Simple jalr use
  __asm__ volatile("addi %0, x0, 0x0\n\t\
                    auipc %1, 0x0\n\t\
                    jalr x0, %1, 0xC\n\t\
                    addi %1, %1, 0x01\n\t\
                    addi %1, %1, 0x01\n\t\
                    addi %1, %1, 0x01\n\t\
                    addi %1, %1, 0x01\n\t\
                    addi %1, %1, 0x01\n\t\
                    addi %1, %1, 0x01"
                    : "=r"(check_result), "=r"(pc_save), "=r"(check_result)
                    : "r"(check_result) );

// Create dependence between ALU and jalr
  __asm__ volatile("addi %0, x0, 0x0\n\t\
                    auipc %1, 0x0\n\t\
                    addi %1, %1, 0x08\n\t\
                    jalr x0, %1, 0x4\n\t\
                    addi %2, %2, 0x01\n\t\
                    addi %2, %2, 0x01\n\t\
                    addi %2, %2, 0x01\n\t\
                    addi %2, %2, 0x01\n\t\
                    addi %2, %2, 0x01\n\t\
                    addi %2, %2, 0x01"
                    : "=r"(check_result), "=r"(pc_save), "=r"(check_result)
                    : "r"(pc_save), "r"(check_result) );

// Create dependence between load and jalr
  __asm__ volatile("addi %0, x0, 0x0\n\t\
                    auipc %1, 0x0\n\t\
                    sw %1, 0(%2)\n\t\
                    lw %3, 0(%2)\n\t\
                    jalr x0, %3, 0x14\n\t\
                    addi %0, %0, 0x01\n\t\
                    addi %0, %0, 0x01\n\t\
                    addi %0, %0, 0x01\n\t\
                    addi %0, %0, 0x01\n\t\
                    addi %0, %0, 0x01\n\t\
                    addi %0, %0, 0x01"
                    : "=r"(check_result), "=r"(pc_save), "=r"(pc_save_mem), "=r"(pc_save_2)
                    : "r"(check_result), "r"(pc_save), "r"(pc_save_mem), "r"(pc_save_2) );

// Load before jalr without dependency
  __asm__ volatile("addi %0, x0, 0x0\n\t\
                    auipc %1, 0x0\n\t\
                    sw %1, 0(%2)\n\t\
                    lw %3, 0(%2)\n\t\
                    jalr x0, %1, 0x14\n\t\
                    addi %0, %0, 0x01\n\t\
                    addi %0, %0, 0x01\n\t\
                    addi %0, %0, 0x01\n\t\
                    addi %0, %0, 0x01\n\t\
                    addi %0, %0, 0x01\n\t\
                    addi %0, %0, 0x01"
                    : "=r"(check_result), "=r"(pc_save), "=r"(pc_save_mem), "=r"(pc_save_2)
                    : "r"(check_result), "r"(pc_save), "r"(pc_save_mem), "r"(pc_save_2) );


  return error;
}