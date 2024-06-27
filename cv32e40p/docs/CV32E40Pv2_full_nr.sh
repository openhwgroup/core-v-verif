#!/bin/bash

###############################################################################
#
# Copyright 2024 Dolphin Design
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
#
# CV32E40Pv2_full_nr: lists the needed commands to reproduce the NR as performed
# by dolphin design team suring CV32E40Pv2 verification, using shell script only
# For the closest reproduction, consider using CV32E40Pv2_full_nr_questa_vrun.sh
#
# Usage:
#       To reproduce the full NR, simply execute:
#           sh CV32E40Pv2_full_nr.sh
#
#       OR
#
#       pick one "./cv_regress ..." line to run it in a terminal inside the
#       bin folder to generate your own sub-regress file if only one
#       config/regress file combo is desired
#
# - CV_VERIF_PATH (core-v-verif root path) should be defined before running this script
# - All needed tools should be sourced before running the script
# (simulator, imperas ISS, etc.)
#
###############################################################################

if [[ -z "${CV_VERIF_PATH-}" ]]; then
    echo "CV_VERIF_PATH does not exist. Set CV_VERIF_PATH environment variable to your core-v-verif root directory and re-run again. Abort."
    exit 1
fi

pushd ${CV_VERIF_PATH}/bin > /dev/null

# CFG pulp | NR File xpulp_instr
./cv_regress --sh --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_xpulp_instr.sh --num=200 --iss yes --cov --cfg pulp --add_test_cfg disable_all_trn_logs
sh pulp_xpulp_instr.sh

# CFG pulp | NR File interrupt_debug_short
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_interrupt_debug_short.sh --num=60 --iss yes --cov --cfg pulp --add_test_cfg disable_all_trn_logs
sh pulp_interrupt_debug_short.sh

# CFG pulp | NR File interrupt_debug_long
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_interrupt_debug_long.sh --num=6 --iss yes --cov --cfg pulp --add_test_cfg disable_all_trn_logs
sh pulp_interrupt_debug_long.sh

# CFG pulp | NR File legacy_v1
./cv_regress --sh --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_legacy_v1.sh --num=1 --iss yes --cov --cfg pulp --add_test_cfg disable_all_trn_logs
sh pulp_legacy_v1.sh

# CFG pulp_fpu | NR File xpulp_instr
./cv_regress --sh --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_fpu_xpulp_instr.sh --num=200 --iss yes --cov --cfg pulp_fpu --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_xpulp_instr.sh

# CFG pulp_fpu | NR File fpu_instr
./cv_regress --sh --file=cv32e40pv2_fpu_instr.yaml --simulator=vsim --outfile=pulp_fpu_fpu_instr.sh --num=300 --iss yes --cov --cfg pulp_fpu --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_fpu_instr.sh

# CFG pulp_fpu | NR File interrupt_debug_short
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_fpu_interrupt_debug_short.sh --num=60 --iss yes --cov --cfg pulp_fpu --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_interrupt_debug_short.sh

# CFG pulp_fpu | NR File interrupt_debug_long
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_fpu_interrupt_debug_long.sh --num=6 --iss yes --cov --cfg pulp_fpu --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_interrupt_debug_long.sh

# CFG pulp_fpu | NR File legacy_v1
./cv_regress --sh --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_fpu_legacy_v1.sh --num=1 --iss yes --cov --cfg pulp_fpu --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_legacy_v1.sh

# CFG pulp_fpu_1cyclat | NR File xpulp_instr
./cv_regress --sh --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_fpu_1cyclat_xpulp_instr.sh --num=200 --iss yes --cov --cfg pulp_fpu_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_1cyclat_xpulp_instr.sh

# CFG pulp_fpu_1cyclat | NR File fpu_instr
./cv_regress --sh --file=cv32e40pv2_fpu_instr.yaml --simulator=vsim --outfile=pulp_fpu_1cyclat_fpu_instr.sh --num=300 --iss yes --cov --cfg pulp_fpu_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_1cyclat_fpu_instr.sh

# CFG pulp_fpu_1cyclat | NR File interrupt_debug_short
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_fpu_1cyclat_interrupt_debug_short.sh --num=60 --iss yes --cov --cfg pulp_fpu_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_1cyclat_interrupt_debug_short.sh

# CFG pulp_fpu_1cyclat | NR File interrupt_debug_long
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_fpu_1cyclat_interrupt_debug_long.sh --num=6 --iss yes --cov --cfg pulp_fpu_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_1cyclat_interrupt_debug_long.sh

# CFG pulp_fpu_1cyclat | NR File legacy_v1
./cv_regress --sh --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_fpu_1cyclat_legacy_v1.sh --num=1 --iss yes --cov --cfg pulp_fpu_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_1cyclat_legacy_v1.sh

# CFG pulp_fpu_2cyclat | NR File xpulp_instr
./cv_regress --sh --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_fpu_2cyclat_xpulp_instr.sh --num=200 --iss yes --cov --cfg pulp_fpu_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_2cyclat_xpulp_instr.sh

# CFG pulp_fpu_2cyclat | NR File fpu_instr
./cv_regress --sh --file=cv32e40pv2_fpu_instr.yaml --simulator=vsim --outfile=pulp_fpu_2cyclat_fpu_instr.sh --num=300 --iss yes --cov --cfg pulp_fpu_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_2cyclat_fpu_instr.sh

# CFG pulp_fpu_2cyclat | NR File interrupt_debug_short
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_fpu_2cyclat_interrupt_debug_short.sh --num=60 --iss yes --cov --cfg pulp_fpu_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_2cyclat_interrupt_debug_short.sh

# CFG pulp_fpu_2cyclat | NR File interrupt_debug_long
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_fpu_2cyclat_interrupt_debug_long.sh --num=6 --iss yes --cov --cfg pulp_fpu_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_2cyclat_interrupt_debug_long.sh

# CFG pulp_fpu_2cyclat | NR File legacy_v1
./cv_regress --sh --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_fpu_2cyclat_legacy_v1.sh --num=1 --iss yes --cov --cfg pulp_fpu_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en
sh pulp_fpu_2cyclat_legacy_v1.sh

# CFG pulp_fpu_zfinx | NR File xpulp_instr
./cv_regress --sh --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_xpulp_instr.sh --num=200 --iss yes --cov --cfg pulp_fpu_zfinx --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_xpulp_instr.sh

# CFG pulp_fpu_zfinx | NR File fpu_instr
./cv_regress --sh --file=cv32e40pv2_fpu_instr.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_fpu_instr.sh --num=300 --iss yes --cov --cfg pulp_fpu_zfinx --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_fpu_instr.sh

# CFG pulp_fpu_zfinx | NR File interrupt_debug_short
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_interrupt_debug_short.sh --num=60 --iss yes --cov --cfg pulp_fpu_zfinx --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_interrupt_debug_short.sh

# CFG pulp_fpu_zfinx | NR File interrupt_debug_long
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_interrupt_debug_long.sh --num=6 --iss yes --cov --cfg pulp_fpu_zfinx --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_interrupt_debug_long.sh

# CFG pulp_fpu_zfinx | NR File legacy_v1
./cv_regress --sh --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_legacy_v1.sh --num=1 --iss yes --cov --cfg pulp_fpu_zfinx --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_legacy_v1.sh

# CFG pulp_fpu_zfinx_1cyclat | NR File xpulp_instr
./cv_regress --sh --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_1cyclat_xpulp_instr.sh --num=200 --iss yes --cov --cfg pulp_fpu_zfinx_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_1cyclat_xpulp_instr.sh

# CFG pulp_fpu_zfinx_1cyclat | NR File fpu_instr
./cv_regress --sh --file=cv32e40pv2_fpu_instr.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_1cyclat_fpu_instr.sh --num=300 --iss yes --cov --cfg pulp_fpu_zfinx_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_1cyclat_fpu_instr.sh

# CFG pulp_fpu_zfinx_1cyclat | NR File interrupt_debug_short
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_1cyclat_interrupt_debug_short.sh --num=60 --iss yes --cov --cfg pulp_fpu_zfinx_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_1cyclat_interrupt_debug_short.sh

# CFG pulp_fpu_zfinx_1cyclat | NR File interrupt_debug_long
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_1cyclat_interrupt_debug_long.sh --num=6 --iss yes --cov --cfg pulp_fpu_zfinx_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_1cyclat_interrupt_debug_long.sh

# CFG pulp_fpu_zfinx_1cyclat | NR File legacy_v1
./cv_regress --sh --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_1cyclat_legacy_v1.sh --num=1 --iss yes --cov --cfg pulp_fpu_zfinx_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_1cyclat_legacy_v1.sh

# CFG pulp_fpu_zfinx_2cyclat | NR File xpulp_instr
./cv_regress --sh --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_2cyclat_xpulp_instr.sh --num=200 --iss yes --cov --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_2cyclat_xpulp_instr.sh

# CFG pulp_fpu_zfinx_2cyclat | NR File fpu_instr
./cv_regress --sh --file=cv32e40pv2_fpu_instr.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_2cyclat_fpu_instr.sh --num=300 --iss yes --cov --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_2cyclat_fpu_instr.sh

# CFG pulp_fpu_zfinx_2cyclat | NR File interrupt_debug_short
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_2cyclat_interrupt_debug_short.sh --num=60 --iss yes --cov --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_2cyclat_interrupt_debug_short.sh

# CFG pulp_fpu_zfinx_2cyclat | NR File interrupt_debug_long
./cv_regress --sh --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_2cyclat_interrupt_debug_long.sh --num=6 --iss yes --cov --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_2cyclat_interrupt_debug_long.sh

# CFG pulp_fpu_zfinx_2cyclat | NR File legacy_v1
./cv_regress --sh --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_2cyclat_legacy_v1.sh --num=1 --iss yes --cov --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en
sh pulp_fpu_zfinx_2cyclat_legacy_v1.sh


popd > /dev/null
