// Copyright 2022 Silicon Laboratories Inc.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you
// may not use this file except in compliance with the License, or, at your
// option, the Apache License version 2.0.
//
// You may obtain a copy of the License at
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.


enum {
  EXC_CAUSE_INSTR_ACC_FAULT       = 1,
  EXC_CAUSE_ILLEGAL_INSTR         = 2,
  EXC_CAUSE_BREAKPOINT            = 3,
  EXC_CAUSE_LOAD_ACC_FAULT        = 5,
  EXC_CAUSE_STORE_ACC_FAULT       = 7,
  EXC_CAUSE_ENV_CALL_U            = 8,
  EXC_CAUSE_ENV_CALL_M            = 11,
  EXC_CAUSE_INSTR_BUS_FAULT       = 24,
  EXC_CAUSE_INSTR_INTEGRITY_FAULT = 25,
};

typedef union {
  struct {
    volatile uint32_t  load     : 1;
    volatile uint32_t  store    : 1;
    volatile uint32_t  execute  : 1;
    volatile uint32_t  u        : 1;
    volatile uint32_t  s        : 1;
    volatile uint32_t  res_5_5  : 1;
    volatile uint32_t  m        : 1;
    volatile uint32_t  match    : 4;
    volatile uint32_t  chain    : 1;
    volatile uint32_t  action   : 4;
    volatile uint32_t  size     : 4;
    volatile uint32_t  timing   : 1;
    volatile uint32_t  select   : 1;
    volatile uint32_t  hit      : 1;
    volatile uint32_t  vu       : 1;
    volatile uint32_t  vs       : 1;
    volatile uint32_t  res_26_25: 2;
    volatile uint32_t  dmode    : 1;
    volatile uint32_t  type     : 4;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) mcontrol6_t;
