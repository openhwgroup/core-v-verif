#!/bin/bash

###############################################################################
#
# Copyright 2020 OpenHW Group
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
###############################################################################
# run_compliance: runs all test-programs in a specific ISA.
#
# Usage:
#       run_compliance RISCV_ISA
#
# ENV: this script needs the following shell environment variables -
#       SIM_DIR     : cwd from which to run sims
###############################################################################

cd ${SIM_DIR}

# Script starts here
if [ "$1" == "" ] ; then
    echo "Please specify RISCV_DEVICE (I|M|C|privilege|Zifencei|Bitmanip)"
    exit 1
fi

if [ "$1" == "I" ] || [ "$1" == "M" ] || [ "$1" == "C" ] || [ "$1" == "privilege" ] || [ "$1" == "Zifencei" ] || [ "$1" == "Bitmanip" ] ; then
    echo "Running tests for $1"
else
    echo "Unknown RISCV_DEVICE setting. Please specify one of I|M|C|privilege|Zifencei"
    exit 1
fi

if [ "$1" == "Bitmanip" ]; then
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=andn-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=bclr-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=bclri-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=bext-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=bexti-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=binv-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=binvi-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=bset-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=bseti-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=clmul-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=clmulh-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=clmulr-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=clz-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cpop-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=ctz-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=max-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=maxu-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=min-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=minu-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=orc.b-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=orn-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=rev8-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=rol-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=ror-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=rori-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sext.b-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sext.h-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sh1add-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sh2add-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sh3add-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=xnor-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=zext.h-01
fi

if [ "$1" == "Zifencei" ]; then
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=Fencei
fi

if [ "$1" == "M" ]; then
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=div-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=divu-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=mul-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=mulh-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=mulhsu-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=mulhu-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=rem-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=remu-01
fi

if [ "$1" == "I" ]; then
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=add-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=addi-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=and-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=andi-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=auipc-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=beq-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=bge-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=bgeu-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=blt-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=bltu-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=bne-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=fence-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=jal-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=jalr-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=lb-align-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=lbu-align-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=lh-align-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=lhu-align-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=lui-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=lw-align-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=or-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=ori-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sb-align-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sh-align-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sll-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=slli-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=slt-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=slti-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sltiu-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sltu-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sra-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=srai-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=srl-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=srli-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sub-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=sw-align-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=xor-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=xori-01
fi

if [ "$1" == "C" ]; then
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cadd-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=caddi-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=caddi16sp-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=caddi4spn-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cand-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=candi-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cbeqz-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cbnez-01
    # Waivable - mtvec not fully writable in cv32e40*
    #make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cebreak-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cj-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cjal-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cjalr-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cjr-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cli-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=clui-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=clw-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=clwsp-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cmv-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cnop-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cor-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cslli-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=csrai-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=csrli-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=csub-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=csw-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cswsp-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=cxor-01
fi

if [ "$1" == "privilege" ]; then
    # Waivable - mtvec not fully writable in cv32e40*
    #make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=ebreak
    #make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=ecall
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign1-jalr-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign2-jalr-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign-beq-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign-bge-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign-bgeu-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign-blt-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign-bltu-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign-bne-01
    make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign-jal-01
    # Waiable - below will fail for targets with hardware support for misaligned load/store
    #make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign-lh-01
    #make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign-lhu-01
    #make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign-lw-01
    #make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign-sh-01
    #make compliance RISCV_ISA=rv32i_m COMPLIANCE_PROG=misalign-sw-01
fi

exit 0
