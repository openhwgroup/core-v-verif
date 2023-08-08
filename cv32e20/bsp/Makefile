# Copyright 2022 OpenHW Group
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

# Makefile for the CV32E20 "Board Support Package".
# The "BSP" is the bare-metal programming environment
# for the CV32E20 in it's UVM testbench.

CV_SW_TOOLCHAIN  ?= /opt/riscv
RISCV            ?= $(CV_SW_TOOLCHAIN)
RISCV_EXE_PREFIX ?= $(RISCV)/bin/riscv32-unknown-elf-
RISCV_GCC = $(RISCV_EXE_PREFIX)gcc
RISCV_AR = $(RISCV_EXE_PREFIX)ar
C_FILES = syscalls_kernel.c csr.c csr.h syscalls.c syscalls.h
SRC = crt0.S handlers.S syscalls.c syscalls_kernel.c vectors.S csr.c
OBJ = crt0.o handlers.o syscalls.o syscalls_kernel.o vectors.o csr.o
LIBCV-VERIF = libcv-verif.a
CFLAGS ?= -Os -g -static -mabi=ilp32 -march=$(CV_SW_MARCH) -Wall -pedantic

all: $(LIBCV-VERIF)

$(LIBCV-VERIF): $(OBJ)
	$(RISCV_AR) rcs $@ $(OBJ)

%.o : %.c
	$(RISCV_GCC) $(CFLAGS) -c $< -o $@

%.o : %.S
	$(RISCV_GCC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJ) $(LIBCV-VERIF)

format:
	clang-format -i --style=llvm $(C_FILES)


vars:
	@echo "make bsp variables:"
	@echo "   CV_SW_TOOLCHAIN  = $(CV_SW_TOOLCHAIN)"
	@echo "   CV_SW_MARCH      = $(CV_SW_MARCH)"
	@echo "   RISCV            = $(RISCV)"
	@echo "   RISCV_EXE_PREFIX = $(RISCV_EXE_PREFIX)"
	@echo "   RISCV_GCC        = $(RISCV_GCC)"

