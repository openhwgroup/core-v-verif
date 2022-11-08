// Copyright 2022 OpenHW Group
// Copyright 2022 Silicon Labs, Inc.
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

#ifndef PMP_H
#define PMP_H

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define RANDOM_REG 0x00800040

// vplan tests
void reset_registers();
void default_full();
void default_none();
void mmode_only();
void napot_matching();
void tor_macthing();
void tor_zero();
void tor_nomatch();
void tor_nomatch();

// helper
void change_mode();
void umode();
void load4addr(uint32_t *output_addr, uint32_t *addr);
void store2addr(int input, uint32_t *addr);
uint32_t lcg_parkmiller(uint32_t *state);
void umode_jmp(uint32_t *addr);

typedef struct CSRS_STUCT
{
  // Machine Status (lower 32 bits). 0x300
  volatile uint32_t mstatus;

  // PMP Configuration (pmpcfg0-pmpcfg15)
  // CSR Address: 0x3A0 - 0x3AF, 32bit each
  volatile uint32_t *pmpcfgx;

  // PMP Address (pmpaddr0 - pmpaddr63) 64 in total
  // CSR Address: 0x3B0 - 0x3EF
  volatile uint32_t *pmpaddrx;
  volatile uint32_t mcause;
  volatile uint32_t mepc;
  // low 32bits
  volatile uint32_t mseccfg;
  // high 32bits
  volatile uint32_t mseccfgh;
} CSRS;

// globals
extern volatile CSRS glb_csrs;
// flag to check exception
extern volatile int glb_trap_expected;

#endif
