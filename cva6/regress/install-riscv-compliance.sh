# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)

if ! [ -n "$COMPLIANCE_REPO" ]; then
  COMPLIANCE_REPO="https://github.com/riscv/riscv-compliance.git"
  COMPLIANCE_BRANCH="master"
  COMPLIANCE_HASH="220e78542da4510e40eac31e31fdd4e77cdae437"
  COMPLIANCE_PATCH="../../../cva6/regress/riscv-compliance.patch"
fi
echo $COMPLIANCE_REPO
echo $COMPLIANCE_BRANCH
echo $COMPLIANCE_HASH
echo $COMPLIANCE_PATCH

mkdir -p cva6/tests
if ! [ -d cva6/tests/riscv-compliance ]; then
  git clone $COMPLIANCE_REPO -b $COMPLIANCE_BRANCH cva6/tests/riscv-compliance
  cd cva6/tests/riscv-compliance; git checkout $COMPLIANCE_HASH;
  if [ -f "$COMPLIANCE_PATCH" ]; then
    git apply $COMPLIANCE_PATCH
  fi
  cd -
fi
