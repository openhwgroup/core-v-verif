
#ifndef PMP_H
#define PMP_H

#include <stdio.h>
#include <stdlib.h>
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
} CSRS;

#endif
