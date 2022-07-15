
#ifndef PMP_H
#define PMP_H

// #define CODE_SECTION ".text"
// #define CODE __attribute__((section(CODE_SECTION)))

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>

// functional functions
// int setbits(int regvalue, char *fieldname);


// test cases
void reset_registers();

void default_full();
void default_none();

// void change_mode(int mode);
void change_mode();
void umode();

void mmode_only();
void napot_matching();
void tor_macthing();

// typedef struct PMPXCFG_STRUCT
// { // bits from lsb to msb  as left to right
//   uint8_t read : 1, write : 1, exe : 1, mode : 2, b65 : 2, lock : 1, b8 : 1;
// } __attribute__((packed)) PMPXCFG;

// typedef struct PMPCFGX_STRUCT
// {
//   PMPXCFG *pmpxcfg;
//   uint32_t cfgx;
// } PMPCFGX;

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
  // low 32bits
  uint32_t mseccfg;
  // high 32bits
  uint32_t mseccfgh;
} CSRS;

// globals
extern CSRS glb_csrs;
// extern PMPXCFG glb_pmpxcfg;
// extern PMPCFGX glb_pmpcfgx;

#endif
