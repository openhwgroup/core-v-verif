// Copyright 2020 ETH Zurich
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
// Description : Single Precision FPU bugs
// 

#include <stdio.h>

#define MSTATUS_FS_INITIAL 0x00002000

void fp_enable ()
{
  unsigned int fs = MSTATUS_FS_INITIAL;

  asm volatile("csrs mstatus, %0;"
               "csrwi fcsr, 0;"
               "csrs mstatus, %0;"
               : : "r"(fs)
              );
}

const long int INPUT[10] __attribute__ ((aligned (4))) = {
  0x08a5a200, 0xb7370010, 0x00f666d8, 0xcf000000, 0x36146dbd, 0x00000000, 0x3e7fffff, 0x017fffff, 0x00ffffff, 0x40000000
};
const long int EXP_RES[5] __attribute__ ((aligned (4))) = {
  0x00800000, 0x80000000, 0x00000000, 0x00800000, 0x00800000
};
const char EXP_FLAGS[5] __attribute__ ((aligned (4))) = {
  0x03, 0x00, 0x00, 0x03, 0x03
};

long int RES[5] __attribute__ ((aligned (4)));
long unsigned int FLAGS[4] __attribute__ ((aligned (4)));

int main()
{
  unsigned int i = 0, j = 0, error = 0;

  float *P_INPUT = (float *)INPUT;
  float *P_EXP_RES = (float *)EXP_RES;
  float *P_RES = (float *)RES;

  // Floating Point enable
  fp_enable();

  // #726
  __asm__ volatile("csrw frm, 0x4");
  __asm__ volatile("csrw fflags, 0x0");
  
#ifdef ZFINX 
  __asm__ volatile("fmadd.s %0, %1, %2, %3" : "=r"(P_RES[i]) : "r"(P_INPUT[j++]), "r"(P_INPUT[j++]), "r"(P_INPUT[j++]) );
#else
  __asm__ volatile("fmadd.s %0, %1, %2, %3" : "=f"(P_RES[i]) : "f"(P_INPUT[j++]), "f"(P_INPUT[j++]), "f"(P_INPUT[j++]) );
#endif
  __asm__ volatile("csrr %0, fflags" : "=r"(FLAGS[i++]));

  // #727
  __asm__ volatile("csrw frm, 0x2");
  __asm__ volatile("csrw fflags, 0x0");
  
#ifdef ZFINX 
  __asm__ volatile("fcvt.w.s %0, %1" : "=r"(P_RES[i]) : "r"(P_INPUT[j++]) );
#else
  __asm__ volatile("fcvt.w.s %0, %1" : "=r"(P_RES[i]) : "f"(P_INPUT[j++]) );
#endif
  __asm__ volatile("csrr %0, fflags" : "=r"(FLAGS[i++]));

  // #728
  __asm__ volatile("csrw frm, 0x2");
  __asm__ volatile("csrw fflags, 0x0");
  
#ifdef ZFINX 
  __asm__ volatile("fmul.s %0, %1, %2" : "=r"(P_RES[i]) : "r"(P_INPUT[j++]), "r"(P_INPUT[j++]) );
#else
  __asm__ volatile("fmul.s %0, %1, %2" : "=f"(P_RES[i]) : "f"(P_INPUT[j++]), "f"(P_INPUT[j++]) );
#endif
  __asm__ volatile("csrr %0, fflags" : "=r"(FLAGS[i++]));

  // #729
  __asm__ volatile("csrw frm, 0x3");
  __asm__ volatile("csrw fflags, 0x0");
  
#ifdef ZFINX 
  __asm__ volatile("fmul.s %0, %1, %2" : "=r"(P_RES[i]) : "r"(P_INPUT[j++]), "r"(P_INPUT[j++]) );
#else
  __asm__ volatile("fmul.s %0, %1, %2" : "=f"(P_RES[i]) : "f"(P_INPUT[j++]), "f"(P_INPUT[j++]) );
#endif
  __asm__ volatile("csrr %0, fflags" : "=r"(FLAGS[i++]));

  // #94
  __asm__ volatile("csrw frm, 0x0");
  __asm__ volatile("csrw fflags, 0x0");
  
#ifdef ZFINX 
  __asm__ volatile("fdiv.s %0, %1, %2" : "=r"(P_RES[i]) : "r"(P_INPUT[j++]), "r"(P_INPUT[j++]) );
#else
  __asm__ volatile("fdiv.s %0, %1, %2" : "=f"(P_RES[i]) : "f"(P_INPUT[j++]), "f"(P_INPUT[j++]) );
#endif
  __asm__ volatile("csrr %0, fflags" : "=r"(FLAGS[i++]));

  for (j = 0; j < i ; j++) {
    if (RES[j] != EXP_RES[j]) {
      printf ("STDOUT : Test %i, Result 0x%02X differs from expected Result 0x%02X !\n", j, RES[j], EXP_RES[j]);
      error++;
    }
    if ((FLAGS[j] & 0x1F) != EXP_FLAGS[j]) {
      printf ("STDOUT : %Test %i, Flags 0x%02X differ from expected Flags 0x%02X !\n", j, FLAGS[j], EXP_FLAGS[j]);
      error++;
    }
  }

  printf("STDOUT : Number of errors in FPU : %d\n", error);

  return error;
}
