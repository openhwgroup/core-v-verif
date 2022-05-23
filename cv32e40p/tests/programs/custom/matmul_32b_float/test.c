#include <stdio.h>

#define N 16
#define M 16

#define TICKS_ADDR 0x15001004

volatile int * const REG_TIME = (int *) TICKS_ADDR;

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

__attribute__((always_inline)) int cpu_perf_get_cycle()
{
  return *REG_TIME;
//return 0; // to be used when USE_ISS=YES
}

int main()
{
  int start_time, stop_time;
  static volatile int nb_cycles;
  int error = 0, error_div = 0;

  float *A = matA;
  float *B = matB;
  float *C = matC;
  float fdivC;
  long int divC;
  long int exp_divC = 0x6a;

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

  divC = matA[0] / 12345678 ;
  printf("STDOUT : Long Integer Div 0x%08x / 0x%08x = 0x%08x\n", matA[0], 12345678, divC);

  // Fdiv example
  fdivC = A[1] / B[1];
  printf("STDOUT : Float Div 0x%08x / 0x%08x = 0x%08x\n", matA[1], matB[1], fdivC);

  error = checkInt(matC, exp_res, N*M);
  printf("STDOUT : Number of errors in matmul %d\n", error);
  if(divC != exp_divC){
      error_div++;
      printf("STDOUT : Error for Long Integer Div, expected %08x but result is %08x\n", exp_divC, divC);
  }
  printf("STDOUT : Number of errors in div %d\n", error_div);
  error += error_div;

  return error;
}
