# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install the required tools
source ./cva6/regress/install-cva6.sh
source ./cva6/regress/install-riscv-dv.sh
source ./cva6/regress/install-riscv-tests.sh

if ! [ -n "$DV_TARGET" ]; then
  DV_TARGET=cv64a6_imafdc_sv39
fi

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=veri-core,spike
fi

if ! [ -n "$DV_TESTLISTS" ]; then
  DV_TESTLISTS="../tests/testlist_riscv-tests-$DV_TARGET-p.yaml \
                ../tests/testlist_riscv-tests-$DV_TARGET-v.yaml"
fi

cd cva6/sim
for TESTLIST in $DV_TESTLISTS
do
  python3 cva6.py --testlist=$TESTLIST --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml $DV_OPTS
done
cd -
