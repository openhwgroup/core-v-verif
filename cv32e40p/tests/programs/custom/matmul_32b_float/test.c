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

#define MSTATUS_FS 0x00006000

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

void fp_enable ()
{
  unsigned int fs = MSTATUS_FS & (MSTATUS_FS >> 1);

  __asm__ volatile("csrs mstatus, %0;"
                   "csrwi fcsr, 0;"
                   : : "r"(fs));

}

void mcycle_counter_enable ()
{
  // Enable mcycle counter
  __asm__ volatile("csrci 0x320, 0x1"); // mcountinhibit.cy = 0

}

int cpu_perf_get_cycle()
{
  unsigned int cycle;
  __asm__ volatile("csrr %0, 0xB00" : "=r"(cycle)); // mcycle
  return cycle;
}

int main()
{
  int start_time, stop_time;
  static volatile int nb_cycles;
  int error = 0;

  volatile float fdiv;

  // Floating Point enable
  fp_enable();

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

  error = checkInt((long int *)C, (long int *)exp_C, N*M);
  printf("STDOUT : Number of errors in matmul : %d\n", error);

  return error;
}
