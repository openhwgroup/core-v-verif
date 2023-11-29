// Copyright 2023 Silicon Labs, Inc.
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
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.


#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "bsp.h"
#include "corev_uvmt.h"


volatile uint32_t  g_debug_entered = 0;
volatile uint32_t  g_debug_expected = 0;
volatile uint32_t  g_debug_function_incr_dpc = 0;
volatile uint32_t  g_debug_function_setup_triggers = 0;

volatile uint32_t  g_exception_expected = 0;

volatile uint32_t  g_pushpop_area [32];
volatile uint32_t  g_pushpop_area_index = 0;

void disable_debug_req(void) {
  CV_VP_DEBUG_CONTROL = (
    CV_VP_DEBUG_CONTROL_DBG_REQ(0)             |
    CV_VP_DEBUG_CONTROL_REQ_MODE(0)            |
    CV_VP_DEBUG_CONTROL_RAND_PULSE_DURATION(0) |
    CV_VP_DEBUG_CONTROL_PULSE_DURATION(0)      |
    CV_VP_DEBUG_CONTROL_RAND_START_DELAY(0)    |
    CV_VP_DEBUG_CONTROL_START_DELAY(0)
  );
}

__attribute__((interrupt("machine")))
void  u_sw_irq_handler(void){
  if (! g_exception_expected) {
    printf("error: exception handler entered unexpectedly\n");
    exit(EXIT_FAILURE);
  }

  g_exception_expected = 0;
}

__attribute__((section(".debugger"), naked))
void  debug_start(void) {
  __asm__ volatile (R"(
    # Backup "sp", use debug's own stack
    csrw dscratch0, sp
    la sp, __debugger_stack_start

    # Backup all GPRs
    sw a0, -4(sp)
    sw a1, -8(sp)
    sw a2, -12(sp)
    sw a3, -16(sp)
    sw a4, -20(sp)
    sw a5, -24(sp)
    sw a6, -28(sp)
    sw a7, -32(sp)
    sw t0, -36(sp)
    sw t1, -40(sp)
    sw t2, -44(sp)
    sw t3, -48(sp)
    sw t4, -52(sp)
    sw t5, -56(sp)
    sw t6, -60(sp)
    addi sp, sp, -64
    cm.push {ra, s0-s11}, -64

    # Call the handler actual
    call ra, debug_handler

    # Restore all GPRs
    cm.pop {ra, s0-s11}, 64
    addi sp, sp, 64
    lw a0, -4(sp)
    lw a1, -8(sp)
    lw a2, -12(sp)
    lw a3, -16(sp)
    lw a4, -20(sp)
    lw a5, -24(sp)
    lw a6, -28(sp)
    lw a7, -32(sp)
    lw t0, -36(sp)
    lw t1, -40(sp)
    lw t2, -44(sp)
    lw t3, -48(sp)
    lw t4, -52(sp)
    lw t5, -56(sp)
    lw t6, -60(sp)

    # Restore "sp"
    csrr sp, dscratch0

    # Done
    dret
  )");
}

static void  setup_triggers(int index){
  mcontrol6_t  mcontrol6;
  uint32_t     trigger_addr;

  mcontrol6.raw          = 0x00000000;
  mcontrol6.fields.load  = 1;
  mcontrol6.fields.store = 1;
  mcontrol6.fields.m     = 1;
  mcontrol6.fields.match = 0;  // (match exact address)
  mcontrol6.fields.type  = 6;

  trigger_addr = (uint32_t) &(g_pushpop_area[index]);

  __asm__ volatile(
    R"(
      # Use trigger 0
      csrwi tselect, 0

      # Disable trigger
      csrwi tdata1, 0

      # Set trigger address
      csrw tdata2, %[trigger_addr]

      # Configure trigger
      csrw tdata1, %[mcontrol6]
    )"
    :
    : [mcontrol6] "r" (mcontrol6.raw),
      [trigger_addr] "r" (trigger_addr)
  );
}

static void  incr_dpc(void){
  uint32_t  dpc;
  uint32_t  instr_word;

  __asm__ volatile(
    "csrr %[dpc], dpc"
    : [dpc] "=r" (dpc)
  );

  instr_word = *(uint32_t *)dpc;

  if ((instr_word & 0x3) == 0x3) {
    dpc += 4;
  } else {
    dpc += 2;
  }

  __asm__ volatile(
    "csrw dpc, %[dpc]"
    : : [dpc] "r" (dpc)
  );
}

void  debug_handler(void){
  g_debug_entered = 1;
  disable_debug_req();
  printf("debug handler entered\n");

  if (! g_debug_expected) {
    printf("error: debug entered unexpectedly\n");
    exit(EXIT_FAILURE);
  }
  g_debug_expected = 0;

  if (g_debug_function_setup_triggers) {
    g_debug_function_setup_triggers = 0;
    setup_triggers(g_pushpop_area_index);
    return;
  }
  if (g_debug_function_incr_dpc) {
    g_debug_function_incr_dpc = 0;
    incr_dpc();
    return;
  }

  printf("error: debug handler function not specified\n");
  exit(EXIT_FAILURE);
}

__attribute__((naked))
static void  push_debug_trigger(void){
  __asm__ volatile(
    R"(
      # Save old "sp"
      mv t0, sp

      # Setup temporary "sp"
      la sp, g_pushpop_area
      addi sp, sp, 16

      # Push to temporary "sp"
      cm.push {x1, x8-x9}, -16

      # Restore old "sp"
      mv sp, t0

      ret
    )"
  );
}

__attribute__((naked))
static void  pop_debug_trigger(void){
  __asm__ volatile(
    R"(
      # Save old "sp" and GPRs
      cm.push {x1, x8-x9}, -16
      mv t0, sp

      # Setup temporary "sp"
      la sp, g_pushpop_area

      # Pop from temporary "sp"
      cm.pop {x1, x8-x9}, 16

      # Restore old "sp" and GPRs
      mv sp, t0
      cm.pop {x1, x8-x9}, 16

      ret
    )"
  );
}

static void  let_dmode_setup_triggers(int index){
  printf("setup trigs\n");

  g_debug_expected = 1;
  g_debug_entered  = 0;
  g_debug_function_setup_triggers = 1;
  g_pushpop_area_index = index;

  // Prolonged pulse duration so debug req has a chance to be acked and taken
  CV_VP_DEBUG_CONTROL = (
    CV_VP_DEBUG_CONTROL_DBG_REQ(1)             |
    CV_VP_DEBUG_CONTROL_REQ_MODE(1)            |
    CV_VP_DEBUG_CONTROL_RAND_PULSE_DURATION(0) |
    CV_VP_DEBUG_CONTROL_PULSE_DURATION(0x1fff) |
    CV_VP_DEBUG_CONTROL_RAND_START_DELAY(0)    |
    CV_VP_DEBUG_CONTROL_START_DELAY(200)
  );

  while (! g_debug_entered) {
    ;
  }
}

static void  test_push_debug_trigger(void){
  printf("push trigger\n");

  g_debug_expected          = 1;
  g_debug_function_incr_dpc = 1;
  g_debug_entered           = 0;

  push_debug_trigger();

  if (! g_debug_entered) {
    printf("error: push should trigger debug\n");
    exit(EXIT_FAILURE);
  }
}

static void  test_pop_debug_trigger(void){
  printf("pop trigger\n");

  g_debug_expected          = 1;
  g_debug_function_incr_dpc = 1;
  g_debug_entered           = 0;

  pop_debug_trigger();

  if (! g_debug_entered) {
    printf("error: pop should trigger debug\n");
    exit(EXIT_FAILURE);
  }

  return;
}

int main(int argc, char **argv){
  let_dmode_setup_triggers(2);
  test_push_debug_trigger();
  test_pop_debug_trigger();
  let_dmode_setup_triggers(1); // trigger at last address in actual sequence
  test_push_debug_trigger();
  test_pop_debug_trigger();
  let_dmode_setup_triggers(3); // trigger at first address in actual sequence
  test_push_debug_trigger();
  test_pop_debug_trigger();

  return EXIT_SUCCESS;
}
