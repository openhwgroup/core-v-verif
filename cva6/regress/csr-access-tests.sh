ee Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

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
source ./cva6/regress/install-riscv-isa-sim.sh
source ./cva6/regress/install-riscv-arch-test.sh

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=vcs-testharness,spike
fi

cd cva6/sim/
python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test ../tests/custom/csr_access_tests/riscv_machine_mode_csr_test_0.S $DV_OPTS  --linker=../sim/link.ld
python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test ../tests/custom/csr_access_tests/riscv_supervisor_mode_csr_test_0.S $DV_OPTS  --linker=../sim/link.ld
python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test ../tests/custom/csr_access_tests/riscv_M_S_mode_csr_test_0.S $DV_OPTS  --linker=../sim/link.ld
make -C ../../core-v-cores/cva6 clean
make clean_all

cd -

