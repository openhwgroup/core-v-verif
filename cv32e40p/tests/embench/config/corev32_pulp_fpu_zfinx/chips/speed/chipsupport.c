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
** 
*******************************************************************************
*/

#include <support.h>
#include <stdint.h>
#include <stdio.h>
#include "chipsupport.h"

extern void _exit();

static uint32_t start_time, stop_time;

void
initialise_board ()
{
  printf("Initialize board corev32 \n");
  __asm__ volatile ("li a0, 0" : : : "memory");
}

void __attribute__ ((noinline)) __attribute__ ((externally_visible))
start_trigger ()
{
  printf("start of test \n");

  // Enable mcycle counter and read value
  __asm__ volatile("csrci mcountinhibit, 0x1"); // mcountinhibit.cy = 0
  __asm__ volatile("rdcycle %0" : "=r"(start_time));

  __asm__ volatile ("li a0, 0" : : : "memory");
}

void __attribute__ ((noinline)) __attribute__ ((externally_visible))
stop_trigger ()
{
  __asm__ volatile("rdcycle %0" : "=r"(stop_time));
  uint32_t cycle_cnt = stop_time - start_time;
  printf("end of test \n");
  printf("Result is given in CPU cycles \n");
  printf("RES: %d \n", cycle_cnt);

  _exit(0);
}
 
