# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Zbigniew CHAMSKI (zbigniew.chamski@thalesgroup.fr)

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install the required tools
source ./cva6/regress/install-cva6.sh
source ./cva6/regress/install-riscv-dv.sh
source ./cva6/regress/install-riscv-compliance.sh
source ./cva6/regress/install-riscv-tests.sh

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=veri-testharness
fi

cd cva6/sim/

make -C ../../core-v-cores/cva6 clean
make clean_all

src0=../tests/riscv-tests/benchmarks/dhrystone/dhrystone_main.c
srcA=(
        ../tests/riscv-tests/benchmarks/dhrystone/dhrystone.c
        ../tests/custom/common/syscalls.c
        ../tests/custom/common/crt.S
)
cflags=(
        -fno-tree-loop-distribute-patterns
        -nostdlib
        -nostartfiles
        -lgcc
        -O3 --no-inline
        -I../tests/custom/env
        -I../tests/custom/common
        -I../tests/riscv-tests/benchmarks/dhrystone/
        -DNOPRINT
)

set -x
python3 cva6.py \
        --target hwconfig \
        --hwconfig_opts="--default_config=cv64a6_imafdc_sv39 --isa=rv64imafdc --NrLoadPipeRegs=0" \
        --iss="$DV_SIMULATORS" \
        --iss_yaml=cva6.yaml \
        --c_tests "$src0" \
        --gcc_opts "${srcA[*]} ${cflags[*]}"
