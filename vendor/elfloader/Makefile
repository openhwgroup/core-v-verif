# Copyright 2023 OpenHW Group
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

# Makefile for the elfloader vendor folder
SO_NAME = elfloader.so

SRC = elfloader.cc
OBJ = elfloader.o

SPIKE_ROOT ?=

EDA_INCLUDES = -I$(VCS_HOME)/include -I/$(QUESTASIM_HOME)/include -I$(XCEL_HOME)/include

CFLAGS ?= -Os -g -I/$(SPIKE_ROOT)/include/ $(EDA_INCLUDES) -std=c++17
CFLAGS_SO ?= -fPIC -DSHARED

LDFLAGS ?= -lstdc++
LDFLAGS_SO ?= -shared

CCX = g++

MIN_GCC_VERSION = "4.9"
GCC_VERSION := $(shell gcc -dumpversion)
IS_GCC_ABOVE_MIN_VERSION := $(shell expr "$(GCC_VERSION)" ">=" "$(MIN_GCC_VERSION)")
ifneq "$(IS_GCC_ABOVE_MIN_VERSION)" "1"
   $(error ERROR: gcc version $(GCC_VERSION) is lower than $(MIN_GCC_VERSION), 'gcc' might fail)
endif


all: $(SO_NAME)


%.o : %.cc
	$(CCX) $(CFLAGS) $(CFLAGS_SO) -c $< -o $@

%.so : $(OBJ)
	$(CCX) $(CFLAGS) $(CFLAGS_SO) $(LDFLAGS) $(LDFLAGS_SO) $< -o $@

%.x :
	$(CCX) $(LDFLAGS) $(CFLAGS) $(SRC) -o $@


clean:
	rm -f $(OBJ) $(SO_NAME)

