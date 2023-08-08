// Copyright (c) 2021 OpenHW Group
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

/* An extremely minimalist syscalls.c for newlib
 * Based on riscv newlib libgloss/riscv/sys_*.c
 *
 * Copyright 2019 Claire Wolf
 * Copyright 2019 ETH Zürich and University of Bologna
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
 * REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
 * INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
 * LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
 * OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
 * PERFORMANCE OF THIS SOFTWARE.
 */
#include "syscalls.h"

void exit(int value) {
  asm inline("   \
        mv a7, %0; \
        mv t0, %0; \
        mv a0, %1; \
        ecall;"
             :
             : "r"(SYS_exit), "r"(value));
}

int execve(const char *name, char *const argv[], char *const env[]) {
  asm inline("   \
        mv a7, %0; \
        mv t0, %0; \
        mv a0, %1; \
        mv a1, %2; \
        mv a2, %3; \
        ecall;"
             :
             : "r"(SYS_execve), "r"(name), "r"(argv), "r"(env));
}
