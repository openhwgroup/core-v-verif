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
# CV32E40Pv2_nr_generator: Execute all the cmds run for CV32E40Pv2 regressions.
# Auto-customisation to change number of rand jobs, simulator, iss use etc.
#
# Usage:
#       CV32E40Pv2_nr_generator.sh
#
###############################################################################

add_sh_cmd_and_check () {
    basename=$1
    output_file=$2


    echo "
sh ${basename}.sh > ${regr}.log 2>&1
fail_count=$(grep -o "Failing tests: [0-9]*" ${regr}.log | grep -o "[0-9]*")
pass_count=$(grep -o "Passing tests: [0-9]*" ${regr}.log | grep -o "[0-9]*")
total=$((fail_count + pass_count))
((tot_fail_count+=fail_count))
((tot_pass_count+=pass_count))
" >> $output_file

}

add_rmdb_cmd_and_check () {
    basename=$1
    output_file=$2
    parallel_jobs=$3
    coverage=$4

    echo "regr=${basename}" >> $output_file
    echo "nb_jobs=${parallel_jobs}" >> $output_file


    echo 'vrun -rmdb ${regr}.rmdb -run cv32e40p -j ${nb_jobs} -notimeout -nogridmsg -noautotriage -noautomerge -GUSE_POST_COMPRESSION=yes -GSEED_MODE=RAND > ${regr}.log 2>&1' >> $output_file

    if [[ $coverage -eq 1 ]]; then
        echo "status_section=\$(sed -n '/Test (valid UCDB) status:/,/RegressionCompleted:/p' \${regr}.log | head -n -1)
ok_count=\$(echo \"\$status_section\" | grep \"Ok\" | sed 's/[^0-9]*//g')
warning_count=\$(echo \"\$status_section\" | grep \"Warning\" | sed 's/[^0-9]*//g')
pass_count=\$((ok_count + warning_count))" >> $output_file
    else
        echo "status_section=\$(sed -n '/Action script pass\/fail status:/,/RegressionCompleted:/p' \${regr}.log | head -n -1)
tmp_pass_count=\$(echo \"\$status_section\" | grep \"Passed\" | sed 's/[^0-9]*//g')
pass_count=\$((tmp_pass_count-3)) " >> $output_file
    fi

echo "
fail_count=\$(echo \"\$status_section\" | grep \"Failed\" | sed 's/[^0-9]*//g')
((tot_fail_count+=fail_count))
((tot_pass_count+=pass_count))
total=\$((fail_count + pass_count))
" >> $output_file

}


if [[ -n "${SIMULATOR+x}" ]]; then
    default_nr_simulator=$SIMULATOR
else
    default_nr_simulator=vsim
fi

default_nr_type=sh
default_nr_vrun_jobs=10
default_nr_vrun_lsf_cmd="bsub -K -q long"
default_nr_vrun_lsf_switch="--lsf \"$default_nr_vrun_lsf_cmd\""
default_nr_cfgs=(pulp pulp_fpu pulp_fpu_1cyclat pulp_fpu_2cyclat pulp_fpu_zfinx pulp_fpu_zfinx_1cyclat pulp_fpu_zfinx_2cyclat)
default_nr_use_iss=yes
default_nr_en_cov=1
default_nr_xpulp_jobs=200
default_nr_fpu_jobs=300
default_nr_dbg_short_jobs=60
default_nr_dbg_long_jobs=6
default_nr_legacy_jobs=1

nr_regr=(xpulp_instr fpu_instr interrupt_debug_short interrupt_debug_long legacy_v1)

echo ""
echo "=================================================================="
echo "| Here are the default parameters for CV32E40Pv2 full regression "
echo -e "| SIMULATOR\t\t  = $default_nr_simulator"
echo -e "| NR_TYPE\t\t  = $default_nr_type"
echo -e "| CFGs\t\t\t  = ${default_nr_cfgs[*]}"
echo -e "| USE_ISS\t\t  = $default_nr_use_iss"
echo -e "| EN_COV\t\t  = $(if [[ $default_nr_en_cov -eq 1 ]]; then echo "yes"; else echo "no"; fi)"
echo -e "| NB_RAND_DBG_SHORT_TESTS = $default_nr_dbg_short_jobs"
echo -e "| NB_RAND_DBG_LONG_TESTS  = $default_nr_dbg_long_jobs"
echo -e "| NB_RAND_PULP_TESTS\t  = $default_nr_xpulp_jobs"
echo -e "| NB_RAND_FPU_TESTS\t  = $default_nr_fpu_jobs"
echo -e "| NB_RAND_LEGACY_V1_TESTS = $default_nr_legacy_jobs"
echo "| "
echo -n "| Do you want to keep default parameters for CV32E40Pv2 regression ? [Y]/N : "
read -r default_or_no

default_or_no=${default_or_no,,}



if [[ -z "$default_or_no" || "$default_or_no" == y* ]]; then
    nr_simulator=$default_nr_simulator
    nr_type=$default_nr_type
    nr_vrun_jobs=$default_nr_vrun_jobs
    nr_vrun_lsf_cmd=$default_nr_vrun_lsf_cmd
    nr_vrun_lsf_switch=$default_nr_vrun_lsf_switch
    nr_cfgs=("${default_nr_cfgs[@]}")
    nr_use_iss=$default_nr_use_iss
    nr_en_cov=$default_nr_en_cov
    nr_xpulp_jobs=$default_nr_xpulp_jobs
    nr_fpu_jobs=$default_nr_fpu_jobs
    nr_dbg_short_jobs=$default_nr_dbg_short_jobs
    nr_dbg_long_jobs=$default_nr_dbg_long_jobs
    nr_legacy_jobs=$default_nr_legacy_jobs
else
    while true; do
        echo "|"

        #############################
        ## GET NR_SIMULATOR
        while true; do
            echo -n "| Which supported simulator do you want to use ? [Default: $default_nr_simulator] vsim / xrun / vcs : "
            read -r choice_simulator
            choice_simulator=${choice_simulator,,}
            if [[ -z "$choice_simulator" || "$choice_simulator" == vsim ]]; then
                nr_simulator=$default_nr_simulator
                break
            elif [[ "$choice_simulator" == xrun || "$choice_simulator" == vcs ]]; then
                nr_simulator=$choice_simulator
                break
            else
                echo "| Unknown simulator $choice_simulator, try again"
            fi
        done

        #############################
        ## GET NR_TYPE
        while true; do
            echo -n "| Which regression type do you want to use ? [Default: $default_nr_type] sh / rmdb (Questa Vrun) : "
            read -r choice_type
            choice_type=${choice_type,,}
            if [[ -z "$choice_type" || "$choice_type" == sh ]]; then
                nr_type=$default_nr_type
                break
            elif [[ "$choice_type" == rmdb ]]; then
                nr_type=rmdb

                #############################
                ## GET NR_VRUN_JOBS
                while true; do
                    echo -n "| RMDB (Questa Vrun) Selected. How many // jobs do you want to run ? [Default: $default_nr_vrun_jobs] / NB : "
                    read -r choice_vrun_jobs
                    if [[ -z "$choice_vrun_jobs" ]]; then
                        nr_vrun_jobs=$default_nr_vrun_jobs
                        break
                    elif [[ "$choice_vrun_jobs" =~ ^[0-9]+$ ]]; then
                        nr_vrun_jobs=$choice_vrun_jobs
                        break
                    else
                        echo "Error : invalid entry, enter a number"
                    fi
                done

                #############################
                ## GET NR_VRUN_LSF_CMD
                while true; do
                    echo -n "| Do you want to use a LSF grid system ? [Default: Yes with $default_nr_vrun_lsf_cmd] / <Yes, just give any LSF CMD> / No : "
                    read -r choice_vrun_lsf_cmd
                    if [[ -z "$choice_vrun_lsf_cmd" ]]; then
                        nr_vrun_lsf_cmd=$default_nr_vrun_lsf_cmd
                        break
                    elif [[ "$choice_vrun_lsf_cmd" =~ bsub ]]; then
                        nr_vrun_lsf_cmd=$choice_vrun_lsf_cmd
                        break
                    fi
                    choice_vrun_lsf_cmd=${choice_vrun_lsf_cmd,,}
                    if [[ "$choice_vrun_lsf_cmd" == n* ]]; then
                        echo "No"
                        nr_vrun_lsf_cmd=""
                        break
                    else
                        echo "| Answer no if LSF not needed, LSF command expected to start with bsub, try again"
                    fi
                done

                break

            else
                echo "| Unknown regrssion type $choice_type, try again"
            fi
        done

        while true; do
            echo -n "| Pick ONE specific configuration to run or left all ? [A]ll / (see_list_above) : "
            read -r choice_cfg
            choice_cfg=${choice_cfg,,}
            if [[ -z "$choice_cfg" || "$choice_cfg" == a* ]]; then
                nr_cfgs=("${default_nr_cfgs[@]}")
                break
            elif [[ ${default_nr_cfgs[@]} =~ $choice_cfg ]]; then
                nr_cfgs=( "$choice_cfg" )
                break
            else
                echo "| Unknown cfg $choice_cfg, try again"
            fi
        done

        echo -n "| Do you want to use Imperas ISS ? [Y]/N : "
        read -r choice_use_iss
        choice_use_iss=${choice_use_iss,,}
        if [[ -z "$choice_use_iss" || "$choice_use_iss" == y* ]]; then
            nr_use_iss=yes
        else
            nr_use_iss=no
        fi

        echo -n "| Do you want to Enable Coverage collection ? [Y]/N : "
        read -r choice_en_cov
        choice_en_cov=${choice_en_cov,,}
        if [[ -z "$choice_en_cov" || "$choice_en_cov" == y* ]]; then
            nr_en_cov=1
        else
            nr_en_cov=0
        fi

        while true; do
            printf "| %-36s %-25s %-39s |  [%3d] / NB : " "How many random tests should run for" "interrupt & debug (short)" "(cv32e40pv2_interrupt_debug_short.yaml)" $default_nr_dbg_short_jobs
            read -r choice_dbg_short_jobs
            if [[ -z "$choice_dbg_short_jobs" ]]; then
                nr_dbg_short_jobs=$default_nr_dbg_short_jobs
                break
            elif [[ "$choice_dbg_short_jobs" =~ ^[0-9]+$ ]]; then
                nr_dbg_short_jobs=$choice_dbg_short_jobs
                break
            else
                echo "Error : invalid entry, enter a number"
            fi
        done

        while true; do
            printf "| %-36s %-25s %-39s |  [%3d] / NB : " " " "interrupt & debug (long)" "(cv32e40pv2_interrupt_debug_long.yaml)" $default_nr_dbg_long_jobs
            read -r choice_dbg_long_jobs
            if [[ -z "$choice_dbg_long_jobs" ]]; then
                nr_dbg_long_jobs=$default_nr_dbg_long_jobs
                break
            elif [[ "$choice_dbg_long_jobs" =~ ^[0-9]+$ ]]; then
                nr_dbg_long_jobs=$choice_dbg_long_jobs
                break
            else
                echo "Error : invalid entry, enter a number"
            fi
        done

        while true; do
            printf "| %-36s %-25s %-39s |  [%3d] / NB : " " " "XPULP instructions" "(cv32e40pv2_xpulp_instr.yaml)" $default_nr_xpulp_jobs
            read -r choice_xpulp_jobs
            if [[ -z "$choice_xpulp_jobs" ]]; then
                nr_xpulp_jobs=$default_nr_xpulp_jobs
                break
            elif [[ "$choice_xpulp_jobs" =~ ^[0-9]+$ ]]; then
                nr_xpulp_jobs=$choice_xpulp_jobs
                break
            else
                echo "Error : invalid entry, enter a number"
            fi
        done

        while true; do
            printf "| %-36s %-25s %-39s |  [%3d] / NB : " " " "FP instructions" "(cv32e40pv2_fpu_instr.yaml)" $default_nr_fpu_jobs
            read -r choice_fpu_jobs
            if [[ -z "$choice_fpu_jobs" ]]; then
                nr_fpu_jobs=$default_nr_fpu_jobs
                break
            elif [[ "$choice_fpu_jobs" =~ ^[0-9]+$ ]]; then
                nr_fpu_jobs=$choice_fpu_jobs
                break
            else
                echo "Error : invalid entry, enter a number"
            fi
        done

        while true; do
            printf "| %-36s %-25s %-39s |  [%3d] / NB : " " " "legacy v1 tests" "(cv32e40pv2_legacy_v1.yaml)" $default_nr_legacy_jobs
            read -r choice_legacy
            if [[ -z "$choice_legacy" ]]; then
                nr_legacy_jobs=$default_nr_legacy_jobs
                break
            elif [[ "$choice_legacy" =~ ^[0-9]+$ ]]; then
                nr_legacy_jobs=$choice_legacy
                break
            else
                echo "Error : invalid entry, enter a number"
            fi
        done

        echo "|"
        echo "|"
        echo "| Here are your selected parameters for CV32E40Pv2 regression "
        echo -e "| SIMULATOR\t\t  = $nr_simulator"
        echo -e "| NR_TYPE\t\t  = $nr_type $(if [[ $nr_type -eq vrun ]]; then echo "$nr_vrun_jobs // jobs | LSF command : $nr_vrun_lsf_cmd"; fi)"
        echo -e "| CFGs\t\t\t  = ${nr_cfgs[*]}"
        echo -e "| USE_ISS\t\t  = $nr_use_iss"
        echo -e "| EN_COV\t\t  = $(if [[ $nr_en_cov -eq 1 ]]; then echo "yes"; else echo "no"; fi)"
        echo -e "| NB_RAND_DBG_SHORT_TESTS = $nr_dbg_short_jobs"
        echo -e "| NB_RAND_DBG_LONG_TESTS  = $nr_dbg_long_jobs"
        echo -e "| NB_RAND_PULP_TESTS\t  = $nr_xpulp_jobs"
        echo -e "| NB_RAND_FPU_TESTS\t  = $nr_fpu_jobs"
        echo -e "| NB_RAND_LEGACY_V1_TESTS = $nr_legacy_jobs"
        echo "| "
        echo -n "| Would you like to generate regressions with these parameters ? [Y]/N/Default : "
        read -r yes_or_no

        yes_or_no=${yes_or_no,,}
        if [[ -z "$yes_or_no" || "$yes_or_no" == y* ]]; then
            break
        fi
        if [[ "$yes_or_no" == d* ]]; then
            nr_simulator=$default_nr_simulator
            nr_type=$default_nr_type
            nr_cfgs=("${default_nr_cfgs[@]}")
            nr_use_iss=$default_nr_use_iss
            nr_en_cov=$default_nr_en_cov
            nr_xpulp_jobs=$default_nr_xpulp_jobs
            nr_fpu_jobs=$default_nr_fpu_jobs
            nr_dbg_short_jobs=$default_nr_dbg_short_jobs
            nr_dbg_long_jobs=$default_nr_dbg_long_jobs
            nr_legacy_jobs=$default_nr_legacy_jobs
            echo "|"
            echo "| Resetting all parameters to default"
            echo "|"
            break
        fi
        echo "|"
    done
fi

echo "|"

nr_jobs=($nr_xpulp_jobs $nr_fpu_jobs $nr_dbg_short_jobs $nr_dbg_long_jobs $nr_legacy_jobs)
nr_tst_cfgs=(
    "disable_all_trn_logs"
    "disable_all_trn_logs,floating_pt_instr_en"
    "disable_all_trn_logs,floating_pt_instr_en"
    "disable_all_trn_logs,floating_pt_instr_en"
    "disable_all_trn_logs,floating_pt_zfinx_instr_en"
    "disable_all_trn_logs,floating_pt_zfinx_instr_en"
    "disable_all_trn_logs,floating_pt_zfinx_instr_en"
)

mkdir -p all_nrs

echo "#!/bin/bash" > start_all_nr.sh
echo "tot_fail_count=0" >> start_all_nr.sh
echo "tot_pass_count=0" >> start_all_nr.sh
echo "cd all_nrs" >> start_all_nr.sh

for idx in "${!default_nr_cfgs[@]}"; do
    if [[ ${nr_cfgs[@]} =~ "${default_nr_cfgs[idx]}" ]]; then
        cfg="${default_nr_cfgs[idx]}"
        echo "| Generating configuration $cfg "
        echo -e "\n" >> start_all_nr.sh
        echo "echo -e \"\n----> Starting configuration $cfg at \$(date \"+%Y-%m-%d %H:%M:%S\")\"" >> start_all_nr.sh
        mkdir -p all_nrs/$cfg
        echo "cd $cfg" >> start_all_nr.sh
        for jdx in "${!nr_regr[@]}"; do
            jobs="${nr_jobs[jdx]}"
            regr="${nr_regr[jdx]}"
            tst_cfg="${nr_tst_cfgs[idx]}"
            if [[ $cfg == pulp && $regr == fpu_instr ]]; then
                continue
            fi
            ./cv_regress --${nr_type} --file=cv32e40pv2_${regr}.yaml --simulator=$nr_simulator --outfile=${regr}.${nr_type} --num=$jobs --iss $nr_use_iss $(if [[ $nr_en_cov -eq 1 ]]; then echo "--cov"; else echo ""; fi) --cfg $cfg --add_test_cfg $tst_cfg $(if [[ -n $nr_vrun_lsf_cmd && $nr_type -eq rmdb ]]; then echo "--lsf $nr_vrun_lsf_cmd"; else echo ""; fi) 1> /dev/null
            mv -f ${regr}.${nr_type} all_nrs/${cfg}/.
            printf "| \t Generated %-21s into : all_nrs/${cfg}/${regr}.${nr_type} \n" "$regr"
            echo "" >> start_all_nr.sh
            echo "echo -e \"--> Starting ${regr} at \$(date \"+%Y-%m-%d %H:%M:%S\")\"" >> start_all_nr.sh

            add_${nr_type}_cmd_and_check ${regr} start_all_nr.sh $nr_vrun_jobs

            echo "echo -n \"--> Finished ${regr} at \$(date \"+%Y-%m-%d %H:%M:%S\")\"" >> start_all_nr.sh
            echo 'echo " : [ $pass_count | $total ]  ( $fail_count Failed, see ${regr}.log ) "' >> start_all_nr.sh
            # echo -e "| \t sh ${cfg}_${regr}.sh >2 /dev/null"
        done
        echo "echo -e \"--> Finished ${cfg} at \$(date \"+%Y-%m-%d %H:%M:%S\")\"" >> start_all_nr.sh

        echo "cd .." >> start_all_nr.sh
    fi
done

echo "echo \"\"" >> start_all_nr.sh
echo "echo \"=======================================================\"" >> start_all_nr.sh
echo "echo \"Total Passing tests: \${tot_pass_count}\"" >> start_all_nr.sh
echo "echo \"Total Failing tests: \${tot_fail_count}\"" >> start_all_nr.sh
echo "echo \"=======================================================\"" >> start_all_nr.sh
echo "echo \"\"" >> start_all_nr.sh

echo "|"
echo "| Generation done."
echo "|"

echo -n "| Do you want to start the whole regression now ? Y/[N] : "
read -r choice_nr
choice_nr=${choice_nr,,}
if [[ -z "$choice_nr" || "$choice_nr" == n* ]]; then
    echo "| You can run the script using this command to execute the whole regression later: sh start_all_nr.sh "
    echo "| Bye !"
    exit 0
else

    echo "|"
    time sh start_all_nr.sh
    echo ""
    echo "|"
fi
