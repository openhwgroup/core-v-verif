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
source ./cva6/regress/install-riscv-compliance.sh
source ./cva6/regress/install-riscv-tests.sh
source ./cva6/regress/install-riscv-isa-sim.sh
source ./cva6/regress/install-riscv-arch-test.sh

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=vcs-testharness,spike
fi

cd cva6/sim/

  python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/cva6/tests/custom/csr_access_tests/riscv_mstatus_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
##  
##  
##  python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_mscratch_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
##   
##   python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_scounteren_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
##  
##   python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_mie_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
##  
##   python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_sip_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
##    
##  python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_stval_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
##   
##  python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_mcountern_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
##  
##  python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_stvec_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
##  
##  python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_spec_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
##  
##  python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_scause_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
##  
##  python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_mcause_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
##  
##  python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_mtval_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
 
## python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_mepc_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld
 
##python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_stvec_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld

## FAILED TESTS

## python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_mtvec_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld

## python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_mip_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld

## python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_sie_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld

## python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_misa_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld

##python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_pmpcfg0_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld

## python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_sscratch_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld

## python3 cva6.py --target cv32a60x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/chamski/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_mhpmcounter3_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld





##python3 cva6.py --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_test /home/t0268396/Desktop/latest/core-v-verif/cva6/tests/custom/common/csr_access_tests/riscv_mstatus_csr_test_0.S $DV_OPTS  --linker=/home/t0268396/Desktop/latest/core-v-verif/cva6/sim/link.ld

## python3 cva6.py --testlist=../tests/testlist_riscv-tests-cv64a6_imafdc_sv39-v.yaml --test rv64ui-v-add --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS
## python3 cva6.py --testlist=../tests/testlist_riscv-tests-cv64a6_imafdc_sv39-p.yaml --test rv64ui-p-add --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS
## python3 cva6.py --testlist=../tests/testlist_riscv-compliance-cv64a6_imafdc_sv39.yaml --test rv32i-I-ADD-01 --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS
## python3 cva6.py --testlist=../tests/testlist_riscv-arch-test-cv64a6_imafdc_sv39.yaml --test rv64i_m-add-01 --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS  --linker=../tests/riscv-isa-sim/arch_test_target/spike/link.ld
## python3 cva6.py --testlist=../tests/testlist_custom.yaml --test custom_test_template --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS
## python3 cva6.py --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --c_tests ../tests/custom/hello_world/hello_world.c\
##   --gcc_opts "-g ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -I../tests/custom/env -I../tests/custom/common -T ../tests/custom/common/test.ld"
## make -C ../../core-v-cores/cva6 clean
## make clean_all
## python3 cva6.py --testlist=../tests/testlist_riscv-compliance-cv32a60x.yaml --test rv32i-I-ADD-01 --iss_yaml cva6.yaml --target cv32a60x --iss=$DV_SIMULATORS $DV_OPTS
## python3 cva6.py --testlist=../tests/testlist_riscv-tests-cv32a60x-p.yaml --test rv32ui-p-add --iss_yaml cva6.yaml --target cv32a60x --iss=$DV_SIMULATORS $DV_OPTS
## python3 cva6.py --testlist=../tests/testlist_riscv-arch-test-cv32a60x.yaml --test rv32im-cadd-01 --iss_yaml cva6.yaml --target cv32a60x --iss=$DV_SIMULATORS $DV_OPTS  --linker=../tests/riscv-isa-sim/arch_test_target/spike/link.ld
make -C ../../core-v-cores/cva6 clean
make clean_all

cd -
