#!/bin/bash

#  
# Copyright 2023 Dolphin Design
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
# 
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
#      http://www.apache.org/licenses/LICENSE-2.0
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


# note
# 1) This file was modified on generated file from "python3 cv_regress --file=cv32e40p_fpu.yaml --simulator=xrun --outfile=bmak --sh"
# 2) To use this file, directly source this file in same file location path with 4 input arguments. e.g below
# <FILE LOCATION PATH>%regr.sh <cfg> <simulator> <use_iss> <test_loop>


# --------------------------------------------------------------------------------------
# Variables
# --------------------------------------------------------------------------------------
pass_count=0
fail_count=0
failed=0

# ensure  WORKSPACE is not empty
# WORKSPACE="/net/buffalo/volume1/projects/cv32/users/bsm/core-v-verif_FOR_COMMIT"
WORKSPACE="../../../../.."

# SIMULATOR=xrun
SIMULATOR=vsim
USE_ISS=NO
IS_ZFINX=""
# IS_ZFINX=_zfinx
TEST_CFG=pulp_fpu${IS_ZFINX}
# note: other TEST_CFG options
  # pulp_fpu_[1:4]cyclat
  # pulp_fpu_zfinx_[1:4]cyclat

ITERATION_TEST_LOOPS=1
ITERATION_TEST_OPTIONS=5
TEST_INDEX=0
TEST_SEED=random

# user inputs
if [[ $# -lt 4 ]]
then
  echo "regr.sh is expecting 4 arguments with following orders: <cfg> <simulator> <use_iss> <test_loop>"
  echo "e.g: ./regr.sh pulp_fpu vsim no 2          -> run regression with pulp_fpu config under questasim with 2 loops of iterations for each test (use_iss=no)"
  echo "e.g: ./regr.sh pulp_fpu_zfinx xrun yes 1   -> run regression with pulp_fpu_zfinx config under xcelium with 1 loops of iterations for each test (use_iss=yes)"
  exit 1
else
  TEST_CFG=$1
  SIMULATOR=$2
  USE_ISS=$3
  ITERATION_TEST_LOOPS=$4
fi

if [[ $TEST_CFG =~ _zfinx ]];
then
  IS_ZFINX=_zfinx
else
  IS_ZFINX=""
fi

echo "TEST_CFG              : $TEST_CFG"
echo "IS_ZFINX              : $IS_ZFINX"
echo "SIMULATOR             : $SIMULATOR"
echo "USE_ISS               : $USE_ISS"
echo "ITERATION_TEST_LOOPS  : $ITERATION_TEST_LOOPS"

  # exit 1

# --------------------------------------------------------------------------------------
# Functions
# --------------------------------------------------------------------------------------
check_log () {
    log=$1
    simulation_passed="$2"
    test_name=$3

    if grep -q "${simulation_passed}" ${log}; then
        echo "regr: Test PASSED: ${test_name} Log: ${log}"
    else
        echo "regr: Test FAILED: ${test_name} Log: ${log}"
        failed=1
    fi
}

incr_test_counts () {
    if [[ ${failed} == "0" ]]; then
        ((pass_count+=1))
    else
        ((fail_count+=1))
    fi
}

# --------------------------------------------------------------------------------------
# Builds
# --------------------------------------------------------------------------------------

# Build:corev-dv 
echo "regr: Running build: [cd ${WORKSPACE}/cv32e40p/sim/uvmt && make comp_corev-dv CV_CORE=cv32e40p CFG=$TEST_CFG SIMULATOR=${SIMULATOR} USE_ISS=NO COV=NO  ]"
pushd ${WORKSPACE}/cv32e40p/sim/uvmt > /dev/null
make comp_corev-dv CV_CORE=cv32e40p CFG=$TEST_CFG SIMULATOR=${SIMULATOR} USE_ISS=NO COV=NO  
popd > /dev/null

# Build:uvmt_cv32e40p 
echo "regr: Running build: [cd ${WORKSPACE}/cv32e40p/sim/uvmt && make comp CV_CORE=cv32e40p CFG=$TEST_CFG SIMULATOR=${SIMULATOR} USE_ISS=$USE_ISS COV=NO  ]"
pushd ${WORKSPACE}/cv32e40p/sim/uvmt > /dev/null
make comp CV_CORE=cv32e40p CFG=$TEST_CFG SIMULATOR=${SIMULATOR} USE_ISS=NO COV=NO  
popd > /dev/null

# --------------------------------------------------------------------------------------
# Tests
# --------------------------------------------------------------------------------------
# hack for regression run -- start

for (( m=0; m<$ITERATION_TEST_LOOPS; m++ ))
do
for (( n=0; n<$ITERATION_TEST_OPTIONS; n++ ))
do

((TEST_INDEX=${m}*${ITERATION_TEST_OPTIONS}+${n}))

  # regression tests
pushd ${WORKSPACE}/cv32e40p/sim/uvmt > /dev/null
make gen_corev-dv test TEST=corev_fp${IS_ZFINX}_instr_test_for_regr CFG_PLUSARGS="+test_override_fp${IS_ZFINX}_instr_stream=$n" CV_CORE=cv32e40p CFG=$TEST_CFG COREV=1 RISCVDV_CFG= SIMULATOR=${SIMULATOR} COMP=0 USE_ISS=$USE_ISS COV=NO SEED=$TEST_SEED GEN_START_INDEX=$TEST_INDEX RUN_INDEX=$TEST_INDEX   >& /dev/null;
popd > /dev/null
log=${WORKSPACE}/cv32e40p/sim/uvmt/${SIMULATOR}_results/${TEST_CFG}/corev_fp${IS_ZFINX}_instr_test_for_regr/${TEST_INDEX}/${SIMULATOR}-corev_fp${IS_ZFINX}_instr_test_for_regr.log
failed=0
check_log ${log} "SIMULATION PASSED" corev_fp${IS_ZFINX}_instr_test_for_regr
incr_test_counts

done


pushd ${WORKSPACE}/cv32e40p/sim/uvmt > /dev/null
  # sanity test
make gen_corev-dv test TEST=corev_sanity_fp${IS_ZFINX}_instr_test CV_CORE=cv32e40p CFG=$TEST_CFG COREV=1 RISCVDV_CFG= SIMULATOR=${SIMULATOR} COMP=0 USE_ISS=NO COV=NO SEED=$TEST_SEED GEN_START_INDEX=$m RUN_INDEX=$m   >& /dev/null;
popd > /dev/null
log=${WORKSPACE}/cv32e40p/sim/uvmt/${SIMULATOR}_results/$TEST_CFG/corev_sanity_fp${IS_ZFINX}_instr_test/${m}/${SIMULATOR}-corev_sanity_fp${IS_ZFINX}_instr_test.log
failed=0
check_log ${log} "SIMULATION PASSED" corev_sanity_fp${IS_ZFINX}_instr_test
incr_test_counts

done
# hack for regression run -- end


echo "regr: Passing tests: ${pass_count}"
echo "regr: Failing tests: ${fail_count}"

if [ ${fail_count} -ne 0 ]; then
    exit 1
fi
exit 0
