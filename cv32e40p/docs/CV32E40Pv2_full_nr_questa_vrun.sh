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
# CV32E40Pv2_full_nr_questa_vrun: lists the needed commands to reproduce the NR
# as performed by dolphin design team during CV32E40Pv2 verification, by using
# Questa VRUN
#
# Usage:
#       To reproduce the full NR, simply execute:
#           sh CV32E40Pv2_full_nr_questa_vrun.sh
#
#       OR
#
#       pick one "./cv_regress ..." line to run it in a terminal inside the
#       bin folder to generate your own sub-regress file if only one
#       config/regress file combo is desired
#
# Required:
# - CV_VERIF_PATH (core-v-verif root path) should be defined before running this script
# - All needed tools should be sourced before running the script
# (simulator, imperas ISS, etc.)
# - A LSF grid system available, with a queue named "long" (change LSF_QUEUE value if not)
# - You can change the number of parallel jobs to run in questa by updating the value of
#   NB_JOBS below
#
###############################################################################

if [[ -z "${CV_VERIF_PATH-}" ]]; then
    echo "CV_VERIF_PATH does not exist. Set CV_VERIF_PATH environment variable to your core-v-verif root directory and re-run again. Abort."
    exit 1
fi

pushd ${CV_VERIF_PATH}/bin > /dev/null

LSF_QUEUE=long
NB_JOBS=10

# CFG pulp | NR File xpulp_instr
./cv_regress --rmdb --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_xpulp_instr.rmdb --num=200 --iss yes --cov --cfg pulp --add_test_cfg disable_all_trn_logs --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_xpulp_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp | NR File interrupt_debug_short
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_interrupt_debug_short.rmdb --num=60 --iss yes --cov --cfg pulp --add_test_cfg disable_all_trn_logs --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_interrupt_debug_short.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp | NR File interrupt_debug_long
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_interrupt_debug_long.rmdb --num=6 --iss yes --cov --cfg pulp --add_test_cfg disable_all_trn_logs --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_interrupt_debug_long.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp | NR File legacy_v1
./cv_regress --rmdb --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_legacy_v1.rmdb --num=1 --iss yes --cov --cfg pulp --add_test_cfg disable_all_trn_logs --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_legacy_v1.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu | NR File xpulp_instr
./cv_regress --rmdb --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_fpu_xpulp_instr.rmdb --num=200 --iss yes --cov --cfg pulp_fpu --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_xpulp_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu | NR File fpu_instr
./cv_regress --rmdb --file=cv32e40pv2_fpu_instr.yaml --simulator=vsim --outfile=pulp_fpu_fpu_instr.rmdb --num=300 --iss yes --cov --cfg pulp_fpu --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_fpu_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu | NR File interrupt_debug_short
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_fpu_interrupt_debug_short.rmdb --num=60 --iss yes --cov --cfg pulp_fpu --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_interrupt_debug_short.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu | NR File interrupt_debug_long
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_fpu_interrupt_debug_long.rmdb --num=6 --iss yes --cov --cfg pulp_fpu --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_interrupt_debug_long.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu | NR File legacy_v1
./cv_regress --rmdb --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_fpu_legacy_v1.rmdb --num=1 --iss yes --cov --cfg pulp_fpu --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_legacy_v1.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_1cyclat | NR File xpulp_instr
./cv_regress --rmdb --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_fpu_1cyclat_xpulp_instr.rmdb --num=200 --iss yes --cov --cfg pulp_fpu_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_1cyclat_xpulp_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_1cyclat | NR File fpu_instr
./cv_regress --rmdb --file=cv32e40pv2_fpu_instr.yaml --simulator=vsim --outfile=pulp_fpu_1cyclat_fpu_instr.rmdb --num=300 --iss yes --cov --cfg pulp_fpu_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_1cyclat_fpu_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_1cyclat | NR File interrupt_debug_short
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_fpu_1cyclat_interrupt_debug_short.rmdb --num=60 --iss yes --cov --cfg pulp_fpu_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_1cyclat_interrupt_debug_short.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_1cyclat | NR File interrupt_debug_long
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_fpu_1cyclat_interrupt_debug_long.rmdb --num=6 --iss yes --cov --cfg pulp_fpu_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_1cyclat_interrupt_debug_long.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_1cyclat | NR File legacy_v1
./cv_regress --rmdb --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_fpu_1cyclat_legacy_v1.rmdb --num=1 --iss yes --cov --cfg pulp_fpu_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_1cyclat_legacy_v1.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_2cyclat | NR File xpulp_instr
./cv_regress --rmdb --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_fpu_2cyclat_xpulp_instr.rmdb --num=200 --iss yes --cov --cfg pulp_fpu_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_2cyclat_xpulp_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_2cyclat | NR File fpu_instr
./cv_regress --rmdb --file=cv32e40pv2_fpu_instr.yaml --simulator=vsim --outfile=pulp_fpu_2cyclat_fpu_instr.rmdb --num=300 --iss yes --cov --cfg pulp_fpu_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_2cyclat_fpu_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_2cyclat | NR File interrupt_debug_short
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_fpu_2cyclat_interrupt_debug_short.rmdb --num=60 --iss yes --cov --cfg pulp_fpu_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_2cyclat_interrupt_debug_short.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_2cyclat | NR File interrupt_debug_long
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_fpu_2cyclat_interrupt_debug_long.rmdb --num=6 --iss yes --cov --cfg pulp_fpu_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_2cyclat_interrupt_debug_long.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_2cyclat | NR File legacy_v1
./cv_regress --rmdb --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_fpu_2cyclat_legacy_v1.rmdb --num=1 --iss yes --cov --cfg pulp_fpu_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_2cyclat_legacy_v1.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx | NR File xpulp_instr
./cv_regress --rmdb --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_xpulp_instr.rmdb --num=200 --iss yes --cov --cfg pulp_fpu_zfinx --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_xpulp_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx | NR File fpu_instr
./cv_regress --rmdb --file=cv32e40pv2_fpu_instr.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_fpu_instr.rmdb --num=300 --iss yes --cov --cfg pulp_fpu_zfinx --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_fpu_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx | NR File interrupt_debug_short
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_interrupt_debug_short.rmdb --num=60 --iss yes --cov --cfg pulp_fpu_zfinx --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_interrupt_debug_short.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx | NR File interrupt_debug_long
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_interrupt_debug_long.rmdb --num=6 --iss yes --cov --cfg pulp_fpu_zfinx --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_interrupt_debug_long.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx | NR File legacy_v1
./cv_regress --rmdb --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_legacy_v1.rmdb --num=1 --iss yes --cov --cfg pulp_fpu_zfinx --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_legacy_v1.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx_1cyclat | NR File xpulp_instr
./cv_regress --rmdb --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_1cyclat_xpulp_instr.rmdb --num=200 --iss yes --cov --cfg pulp_fpu_zfinx_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_1cyclat_xpulp_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx_1cyclat | NR File fpu_instr
./cv_regress --rmdb --file=cv32e40pv2_fpu_instr.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_1cyclat_fpu_instr.rmdb --num=300 --iss yes --cov --cfg pulp_fpu_zfinx_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_1cyclat_fpu_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx_1cyclat | NR File interrupt_debug_short
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_1cyclat_interrupt_debug_short.rmdb --num=60 --iss yes --cov --cfg pulp_fpu_zfinx_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_1cyclat_interrupt_debug_short.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx_1cyclat | NR File interrupt_debug_long
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_1cyclat_interrupt_debug_long.rmdb --num=6 --iss yes --cov --cfg pulp_fpu_zfinx_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_1cyclat_interrupt_debug_long.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx_1cyclat | NR File legacy_v1
./cv_regress --rmdb --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_1cyclat_legacy_v1.rmdb --num=1 --iss yes --cov --cfg pulp_fpu_zfinx_1cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_1cyclat_legacy_v1.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx_2cyclat | NR File xpulp_instr
./cv_regress --rmdb --file=cv32e40pv2_xpulp_instr.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_2cyclat_xpulp_instr.rmdb --num=200 --iss yes --cov --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_2cyclat_xpulp_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx_2cyclat | NR File fpu_instr
./cv_regress --rmdb --file=cv32e40pv2_fpu_instr.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_2cyclat_fpu_instr.rmdb --num=300 --iss yes --cov --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_2cyclat_fpu_instr.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx_2cyclat | NR File interrupt_debug_short
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_short.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_2cyclat_interrupt_debug_short.rmdb --num=60 --iss yes --cov --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_2cyclat_interrupt_debug_short.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx_2cyclat | NR File interrupt_debug_long
./cv_regress --rmdb --file=cv32e40pv2_interrupt_debug_long.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_2cyclat_interrupt_debug_long.rmdb --num=6 --iss yes --cov --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_2cyclat_interrupt_debug_long.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND

# CFG pulp_fpu_zfinx_2cyclat | NR File legacy_v1
./cv_regress --rmdb --file=cv32e40pv2_legacy_v1.yaml --simulator=vsim --outfile=pulp_fpu_zfinx_2cyclat_legacy_v1.rmdb --num=1 --iss yes --cov --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg disable_all_trn_logs,floating_pt_zfinx_instr_en --lsf "bsub -K -q ${LSF_QUEUE}"
vrun -rmdb pulp_fpu_zfinx_2cyclat_legacy_v1.rmdb -run cv32e40p -j $NB_JOBS -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND


popd > /dev/null
