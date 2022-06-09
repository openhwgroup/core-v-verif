// See LICENSE for license details.
// Contributed by Zbigniew CHAMSKI <zbigniew.chamski@thalesgroup.com>

// The following is a RISC-V program to test the functionality of the
// basic CVXIF accelerator interface on the CV side.
// Compile using "riscv-none-elf-gcc -O2 cvxif_test.elf cvxif_test.c"
// with -march=/-mabi= settings appropriate for your project.
// Run using "spike --extension=cvxif cvxif_test.elf" after adding
// an --isa= setting appropriate for your project.
// The simulation should end with the message
//
//   terminate called after throwing an instance of 'trap_store_access_fault'
//
// indicating that all tests passed and the exception was correctly raised.

#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

// Values of MCAUSE corresponding to exceptions coming from the coprocessor I/F
#define CAUSE_MISALIGNED_LOAD 0x4
#define CAUSE_LOAD_ACCESS 0x5
#define CAUSE_MISALIGNED_STORE 0x6
#define CAUSE_STORE_ACCESS 0x7
#define CAUSE_LOAD_PAGE_FAULT 0xd
#define CAUSE_STORE_PAGE_FAULT 0xf
#define CAUSE_COPROCESSOR_EXCEPTION 0x20

// Value of TVAL to pass around.
#define COPRO_TVAL_TEST 0x1a

// Macro to read a CSR (from spike's "encoding.h")
#define read_csr(reg) ({ unsigned long __tmp; \
  asm volatile ("csrr %0, " #reg : "=r"(__tmp)); \
  __tmp; })

int main() {
  uint64_t x = 123, y = 456, z = 0, t = 0;
  static uint64_t amem = 111, bmem = 0;
  uint64_t a;

  // Add x + y into z.  Funct7 == 0, funct3 == 0x0.
  asm volatile (".insn r CUSTOM_3, 0, 0, %0, %1, %2" : "=r"(z) : "r"(x), "r"(y));
  if (z != 123 + 456)
  {
    //  printf("FAILURE!!!\n");
    return 1;
  }
  
  // Add three operands in a single R4-type add.
  // Leverage current values of x, y and z (z == x + y).
  asm volatile (".insn r CUSTOM_3, 0, 0x1, %0, %1, %2, %3" : "=r"(t) : "r"(x), "r"(y), "r"(z));
  if (t != x + y + z)
  {
    // printf("FAILURE");
    return 2;
  }
  // Load 'a' from 'amem'. CUSTOM_LD: opcode == CUSTOM_3, insn_type == I, funct3 == 0x1.
  asm volatile (".insn i CUSTOM_3, 0x1, %0, %1" : "=r"(a) : "m"(amem), "I"(0));
  if (a != 111)
  {
    //  printf("FAILURE!!!\n");
    return 3;
  }

  // Store 'a' in 'bmem'. CUSTOM_SD: opcode == CUSTOM_3, insn_type == S, funct3 == 0x2.
  asm volatile (".insn s CUSTOM_3, 0x2, %0, %1" : : "r"(a), "m"(bmem));
  if (bmem != 111)
  {
    //  printf("FAILURE!!!\n");
    return 4;
  }

  // Generate a fake misaligned load exception (mcause == 0x4).
  asm volatile  (".insn r CUSTOM_3, 0x0, 0x40, x0, x4, x0" : : );

  // If we get here, then the exception test failed ==> exit with general failure code.
  exit(1337);
}

// Override default trap handler.  
uintptr_t handle_trap(uintptr_t cause, uintptr_t epc, uintptr_t regs[32])
{
  if (cause == CAUSE_MISALIGNED_LOAD)
    // Successfully terminate.
    exit(0);
  else
    // Fail with explicit retcode.
    exit(5);
}
