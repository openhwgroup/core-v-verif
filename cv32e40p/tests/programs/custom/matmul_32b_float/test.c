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
// Description : Multiplication of 2 Single Precision Floating Point Matrices
// 

#include <stdio.h>

#define N 16
#define M 16

#define MSTATUS_FS_INITIAL 0x00002000

#include "stimuli.h"

int checkInt (long int *B, long int *A, long int n)
{
  int i;
  int err = 0;
  for (i = 0; i < n; i++) {
//  if(A[i] != B[i]){
//  if(A[i] != B[i] && ((A[i] - B[i]) > 1)){
    if(A[i] != B[i] && ((A[i] - B[i]) > 2)){
        err++;
        printf("STDOUT : Error at %d, expected %08x but result is %08x\n", i, A[i], B[i]);
    }
  }
  return err;
}

#ifdef FPU
void fp_enable ()
{
  unsigned int fs = MSTATUS_FS_INITIAL;

  asm volatile("csrs mstatus, %0;"
               "csrwi fcsr, 0;"
               "csrs mstatus, %0;"
               : : "r"(fs)
              );
}
#endif

void mcycle_counter_enable ()
{
  // Enable mcycle counter
  __asm__ volatile("csrci mcountinhibit, 0x1"); // mcountinhibit.cy = 0

}

int cpu_perf_get_cycle()
{
  unsigned int cycle;
  __asm__ volatile("rdcycle %0" : "=r"(cycle)); // cycle
  return cycle;
}

int main()
{
  int start_time, stop_time;
  static volatile int nb_cycles;
  int error = 0;

  float *A = (float *)A_int;
  float *B = (float *)B_int;
  float *C = (float *)C_int;

  volatile float fdiv;

  unsigned int misa_val;
  __asm__ volatile("csrr %0, 0x301" : "=r"(misa_val)); // Misa CSR
  printf("STDOUT : Misa.F is %d\n", (misa_val & 0x20) >> 5);

  unsigned int zfinx_val;
  __asm__ volatile("csrr %0, 0xCD2" : "=r"(zfinx_val)); // Zfinx CSR

#ifndef PULP
  printf("STDOUT : Should generate an illegal exception as Zfinx CSR is not implemented.\n");
#else
#ifdef FPU
  // Floating Point enable
  fp_enable();

#ifdef ZFINX
  if (zfinx_val != 1) {
    error++;
    printf("STDOUT : Error, Zfinx expected 1 but result is %d\n", zfinx_val);
  } else {
    printf("STDOUT : Zfinx is %d\n", zfinx_val);
  }
#else
  printf("STDOUT : Should generate an illegal exception as Zfinx CSR is not implemented.\n");
#endif
#else
  if (zfinx_val != 0) {
    error++;
    printf("STDOUT : Error, Zfinx expected 0 but result is %d\n", zfinx_val);
  } else {
    printf("STDOUT : Zfinx is %d\n", zfinx_val);
  }
#endif
#endif

  // Enable mcycle counter
  mcycle_counter_enable();

  start_time = cpu_perf_get_cycle();

  for (int i = 0; i < N; i++) {
    for (int j = 0; j < M; j++) {
      C[i*N+j] = 0;
      for (int k = 0; k < N; k+=1) {
        C[i*N+j] += A[i*N+k] * B[k*N+j];
      }
    } // for (int j
  }

  stop_time = cpu_perf_get_cycle();

  nb_cycles = stop_time - start_time;
  printf("STDOUT : Perf Counter cycles : %d\n", nb_cycles);

  // Fdiv example
  fdiv = A[0] / B[1];

  error += checkInt(C_int, exp_C_int, N*M);
  printf("STDOUT : Number of errors in matmul : %d\n", error);

  return error;
}
