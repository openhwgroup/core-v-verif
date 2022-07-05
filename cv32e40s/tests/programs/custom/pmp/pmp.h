
#ifndef PMP_H
#define PMP_H

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
// #include "chg_mode.S"

#define PMP_R 0x01
#define PMP_W 0x02
#define PMP_X 0x04
#define PMP_A 0x18
#define PMP_L 0x80
#define PMP_SHIFT 2

#define PMP_TOR 0x08
#define PMP_NA4 0x10
#define PMP_NAPOT 0x18

void reset_registers();

void default_full();
void default_none();

// void change_mode(int mode);
void change_mode();
void mmode_only();

// typedef struct pmpxcfg_struct{
//   int r;
//   int w;
//   int x;
//   int a;
//   int l;
// } pmpxcfg;

// typedef struct pmpcfg_struct
// {
//   pmpxcfg pmp0cfg
// } pmpcfgx;

typedef struct CSRS_STUCT
{
  // Machine Status (lower 32 bits). 0x300
  uint32_t mstatus;

  // PMP Configuration (pmpcfg0-pmpcfg15)
  // CSR Address: 0x3A0 - 0x3AF, 32bit each
  uint32_t *pmpcfgx;

  // PMP Address (pmpaddr0 - pmpaddr63) 64 in total
  // CSR Address: 0x3B0 - 0x3EF
  uint32_t *pmpaddrx;
  uint32_t mcause;
  uint32_t mepc;
  uint32_t mseccfg;
} CSRS;

#endif

#ifdef __GNUC__

#define read_csr(reg) ({ unsigned long __tmp; \
  asm volatile ("csrr %0, " #reg : "=r"(__tmp)); \
  __tmp; })

#define write_csr(reg, val) ({ asm volatile("csrw " #reg ", %0" ::"rK"(val)); })

#define swap_csr(reg, val) ({ unsigned long __tmp; \
  asm volatile ("csrrw %0, " #reg ", %1" : "=r"(__tmp) : "rK"(val)); \
  __tmp; })

#define set_csr(reg, bit) ({ unsigned long __tmp; \
  asm volatile ("csrrs %0, " #reg ", %1" : "=r"(__tmp) : "rK"(bit)); \
  __tmp; })

#define clear_csr(reg, bit) ({ unsigned long __tmp; \
  asm volatile ("csrrc %0, " #reg ", %1" : "=r"(__tmp) : "rK"(bit)); \
  __tmp; })

#endif