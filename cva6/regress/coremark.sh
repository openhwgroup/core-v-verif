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
  DV_SIMULATORS=veri-testharness,spike
fi

cd cva6/sim/
# python3 cva6.py --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --c_tests ../tests/custom/coremark/core_main.c --gcc_opts '../tests/custom/coremark/core_list_join.c ../tests/custom/coremark/core_matrix.c ../tests/custom/coremark/core_portme.c ../tests/custom/coremark/core_state.c ../tests/custom/coremark/core_util.c -O3 -fno-tree-loop-distribute-patterns -nostdlib -nostartfiles -mcmodel=medany -DFLAGS_STR="-O3_-fno-tree-loop-distribute-patterns" -DITERATIONS=10 -DPERFORMANCE_RUN -g -nostdlib -nostartfiles ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -I../tests/custom/env -I../tests/custom/common -lgcc'
# make -C ../../core-v-cores/cva6 clean
# make clean_all
# python3 cva6.py --target cv32a6_im_sv0 --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --c_tests ../tests/custom/coremark/core_main.c --gcc_opts '../tests/custom/coremark/core_list_join.c ../tests/custom/coremark/core_matrix.S ../tests/custom/coremark/core_portme.c ../tests/custom/coremark/core_state.c ../tests/custom/coremark/core_util.c -O3 -funroll-all-loops -fno-tree-loop-distribute-patterns -nostdlib -nostartfiles -DFLAGS_STR="-O3_-fno-tree-loop-distribute-patterns" -DITERATIONS=5 -DPERFORMANCE_RUN -g -nostdlib -nostartfiles ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -I../tests/custom/env -I../tests/custom/common -lgcc'
python3 cva6.py --target cv32a6_imac_sv0 --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --c_tests ../tests/custom/coremark/core_main.c --gcc_opts '../tests/custom/coremark/core_list_join.c ../tests/custom/coremark/core_matrix.S ../tests/custom/coremark/core_portme.c ../tests/custom/coremark/core_state.c ../tests/custom/coremark/core_util.c -O3 -funroll-all-loops -fno-tree-loop-distribute-patterns -nostdlib -nostartfiles -DFLAGS_STR="-O3_-fno-tree-loop-distribute-patterns" -DITERATIONS=5 -DPERFORMANCE_RUN -g -nostdlib -nostartfiles ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -I../tests/custom/env -I../tests/custom/common -lgcc -ffunction-sections -fdata-sections -Wl,-gc-sections -falign-jumps=4 -falign-functions=16 -misa-spec=2.2'
make -C ../../core-v-cores/cva6 clean
make clean_all

cd -
