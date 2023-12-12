#!/usr/bin/env python3


# Copyright 2023 Silicon Labs, Inc.
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
# not use this file except in compliance with the License, or, at your option,
# the Apache License version 2.0.
#
# You may obtain a copy of the License at
# https://solderpad.org/licenses/SHL-2.1/
#
# Unless required by applicable law or agreed to in writing, any work
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#
# See the License for the specific language governing permissions and
# limitations under the License.


# Description:
#     This script is for generating the CSR access test:
#     `cv32e40(s|x)/tests/programs/custom/cv32e40x_csr_access_test/`.
#
#     It calls a generation script within `riscv-dv`.
#     A Yaml config as per `--input_yaml_path` is used as its input.
#     See the README in the path mention above for additional usage info.


import sys
import os
import argparse
import subprocess
import yaml
import shlex


if (sys.version_info < (3,5,0)):
    print ('Requires python 3.5')
    exit(1)

supported_cores = ["cv32e40s", "cv32e40x"]

try:
    default_core = os.environ['CV_CORE']
except KeyError:
    default_core = 'None'

topdir = os.path.abspath(os.path.join(os.path.dirname(os.path.realpath(__file__)), '..'))


# Parser arguments

parser = argparse.ArgumentParser()

parser.add_argument("--dry_run",                help="Prints generated yaml to stdout",   action="store_true")
parser.add_argument("--core",                   help="Set the core to generate test for", choices=supported_cores)
parser.add_argument("--output",                 help="Output path",                       type=str)
parser.add_argument("--iterations",             help="Number of generated tests",         type=str, default="1")
parser.add_argument("--m4",                     help="Use 'm4' for all preprocessing, and the m4 yaml file path unless another path is specified",\
action="store_true", default=False)
parser.add_argument("--input_yaml_path",        help="Optional: input yaml file path. If not specified: the m4 yaml or the default yaml file path is used",\
type=str)

parser.add_argument("--pmp_num_regions",        help="Set number of Pmp regions",         type=str, default="0")
parser.add_argument("--mhpmcounter_num",        help="Set number of mhpmcounters",        type=str, default="3")
parser.add_argument("--num_triggers",           help="Set number of trigger registers",   type=str, default="1")
parser.add_argument("--marchid",                help="Set number for marchid",            type=str, default="0")

parser.add_argument("--clic_enable",            help="Enable clic support",               action="store_true", default=False)
parser.add_argument("--clint_enable",           help="Enable Basic Interrupts",           action="store_true", default=False)
parser.add_argument("--debug_enable",           help="Enable Debug Registers",            action="store_true", default=False)
parser.add_argument("--umode_enable",           help="Enable Certain U-mode fields",      action="store_true", default=False)
parser.add_argument("--xsecure_enable",         help="Enable Xsecure Registers",          action="store_true", default=False)
parser.add_argument("--zc_enable",              help="Enable Zc support",                 action="store_true", default=False)
parser.add_argument("--zicntr_enable",          help="Enable Zicntr",                     action="store_true", default=False)

parser.add_argument("--a_ext_enable",           help="Enable A extension",                action="store_true", default=False)
parser.add_argument("--e_base_enable",          help="Enable E base",                     action="store_true", default=False)
parser.add_argument("--e_ext_enable",           help="Enable E base",                     action="store_true", default=False)
parser.add_argument("--f_ext_enable",           help="Enable F extension",                action="store_true", default=False)
parser.add_argument("--i_base_enable",          help="Enable I base",                     action="store_true", default=False)
parser.add_argument("--i_ext_enable",           help="Enable I base",                     action="store_true", default=False)
parser.add_argument("--m_ext_enable",           help="Enable M extension",                action="store_true", default=False)
parser.add_argument("--m_none_enable",          help="Disable M extension",               action="store_true", default=False)
parser.add_argument("--p_ext_enable",           help="Enable P extension",                action="store_true", default=False)
parser.add_argument("--v_ext_enable",           help="Enable V extension",                action="store_true", default=False)
parser.add_argument("--x_ext_enable",           help="Enable X extension",                action="store_true", default=False)

args = parser.parse_args()

if (args.core == None or args.core not in supported_cores):
    parser.print_help()
    print("Error: No supported '--core' specified")
    exit(1)
if (args.output == None):
    parser.print_help()
    print("Error: no '--output' path specified")
    exit(1)
if int(args.pmp_num_regions) not in range(65):
    print("Error: unsupported number of pmp regions")
    exit(1)

if args.dry_run:
    print('{}'.format(args))


script_path      = os.path.join(topdir, '{}/vendor_lib/google/riscv-dv/scripts/gen_csr_test.py'.format(args.core.lower()))
template_path    = os.path.join(topdir, './bin/templates/csr_access_test_template.S')
output_yaml_path = ""

if (args.input_yaml_path != None):
    yaml_file_path   = args.input_yaml_path
elif (args.m4):
    yaml_file_path   = os.path.join(topdir, 'core-v-cores/{}'.format(args.core.lower()) + '/yaml/csr.yaml.m4')
else:
    yaml_file_path   = os.path.join(topdir, '{}'.format(args.core.lower()) + '/env/corev-dv/{}'.format(args.core.lower()) + '_csr_template.yaml')


def run_riscv_dv_gen_csr_script(output_yaml_path):
    try:
        print("riscv-dv script path: {}".format(script_path))
        if (not os.path.isfile(script_path)):
            print("error: script_path, no such file", file=sys.stderr)
            exit(1)

        print("csr description used: {}".format(output_yaml_path))
        if (not os.path.isfile(output_yaml_path)):
            print("error: csr description output_yaml_path doesn't exist", file=sys.stderr)
            exit(1)

        script_args = { "csr_file"   : ' --csr_file {}'.format(output_yaml_path),
                        "xlen"       : ' --xlen 32',
                        "out"        : ' --out ' + args.output,
                        "iterations" : ' --iterations ' + args.iterations}
        subprocess.call(shlex.split("python3 " + script_path + script_args["csr_file"] + script_args["xlen"] + script_args["out"] + script_args["iterations"]))
    except Exception as e:
        print("error: exception in 'run_riscv_dv_gen_csr_script'")
        print(e)

def set_enabled_features(enabled_features_previous, str_args_previous, args):
    enabled_features = enabled_features_previous
    str_args = str_args_previous

    # "VERIF_HEADER"  (Design-workaround for CSR field alternatives.)
    enabled_features["verif_header"] = True

    # CLIC
    if (args.clic_enable):
        str_args = str_args + "_clic"
        enabled_features["clic"] = True

    # CLINT
    if (args.clint_enable or not args.clic_enable):
        str_args = str_args + "_clint"
        enabled_features["clint"] = True if not enabled_features["clic"] else False

    # DEBUG
    if (args.debug_enable):
        str_args = str_args + "_debug"
        enabled_features["debug"] = True

    # I/E
    if (args.i_base_enable or args.i_ext_enable):
        str_args = str_args + "_i"
        enabled_features["i_base"] = True
    elif (args.e_base_enable or args.e_ext_enable):
        str_args = str_args + "_e"
        enabled_features["e_base"] = True
    else:
        print("error: need '--i_base_enable' or '--e_base_enable'", file=sys.stderr)
        exit(1)
    if (args.i_ext_enable or args.e_ext_enable):
        print("warning: i and e are 'base' modules, not extensions", file=sys.stderr)

    # M
    if (args.m_ext_enable):
        str_args = str_args + "_m"
        enabled_features["m_ext"] = True
    elif (args.m_none_enable):
        str_args = str_args + "_mnone"
        enabled_features["m_none"] = True
    else:
        print("error: need '--m_ext_enable' or '--m_none_enable'", file=sys.stderr)
        exit(1)

    # A_EXT
    if (args.a_ext_enable):
        str_args = str_args + "_a"
        enabled_features["a_ext"] = True

    # F_EXT
    if (args.f_ext_enable):
        str_args = str_args + "_f"
        enabled_features["f_ext"] = True

    # P_EXT
    if (args.p_ext_enable):
        str_args = str_args + "_p"
        enabled_features["p_ext"] = True

    # V_EXT
    if (args.v_ext_enable):
        str_args = str_args + "_v"
        enabled_features["v_ext"] = True

    # X_EXT
    if (args.x_ext_enable):
        str_args = str_args + "_x"
        enabled_features["x_ext"] = True

    # XSECURE
    if (args.xsecure_enable):
        str_args = str_args + "_xsecure"
        enabled_features["xsecure"] = True

    # UMODE
    if (args.umode_enable):
        str_args = str_args + "_umode"
        enabled_features["umode"] = True

    # ZC
    if (args.zc_enable):
        str_args = str_args + "_zc"
        enabled_features["zc"] = True

    # ZICNTR
    if (args.zicntr_enable):
        str_args = str_args + "_zicntr"
        enabled_features["zicntr"] = True

    # MARCHID
    if (int(args.marchid) > 0):
        str_args = str_args + "_marchid" + args.marchid
        enabled_features["marchid"] = int(args.marchid)

    # MHPMCOUNTERS
    if (int(args.mhpmcounter_num) > 0):
        str_args = str_args + "_mhpmctr" + args.mhpmcounter_num
        enabled_features["num_mhpmcounters"] = int(args.mhpmcounter_num)

    # PMP
    if (int(args.pmp_num_regions) > 0):
        str_args = str_args + "_pmp" + args.pmp_num_regions
        enabled_features["pmp_num_regions"] = int(args.pmp_num_regions)

    # TRIGGERS
    if (int(args.num_triggers) > 0):
        str_args = str_args + "_triggers" + args.num_triggers
        enabled_features["dbg_num_triggers"] = int(args.num_triggers)

    return (enabled_features, str_args)

def preprocess_yaml():
    input_script_path = yaml_file_path
    w_enable = True
    w_enable_n = w_enable
    str_args = ""
    enabled_features = {
      "clic":             False,
      "clint":            False,
      "debug":            False,
      "e_base":           False,
      "i_base":           False,
      "m_ext":            False,
      "m_none":           False,
      "readonly":         False,
      "umode":            False,
      "a_ext":            False,
      "f_ext":            False,
      "p_ext":            False,
      "v_ext":            False,
      "x_ext":            False,
      "xsecure":          False,
      "zc":               False,
      "zicntr":           False,
      "marchid":          0,
      "num_mhpmcounters": 0,
      "pmp_num_regions":  0,
      "dbg_num_triggers": 0,
      }

    (enabled_features, str_args) = \
        set_enabled_features(enabled_features, str_args, args)

    print("enabled_features: {}".format(enabled_features))

    output_script_path = os.path.join(args.output) + "{}_csr_template.yaml".format(args.core.lower() + str_args)
    if not args.dry_run:
        output_script_handle = open(output_script_path, "w")

    # "m4" - Optionally used for all preprocessing
    if (args.m4):
        preprocess_yaml_m4(enabled_features, input_script_path, output_script_handle)
        return output_script_path

    input_script_handle = open(input_script_path, "r")
    input_script_lines = input_script_handle.readlines()
    for line in input_script_lines:
        input_list = line.split()
        # Cond <true/false>
        if len(input_list) == 3 and input_list[0] == "###" and input_list[1].lower() == "cond":
            if not enabled_features[input_list[2].lower()]:
                w_enable   = False
                w_enable_n = False
        # Cond <key pair>
        elif len(input_list) == 4 and input_list[0] == "###" and input_list[1].lower() == "cond":
            if (int(input_list[3].lower()) > int(enabled_features[input_list[2].lower()])):
                w_enable   = False
                w_enable_n = False
            else:
                w_enable_n = True
                w_enable   = True
        # Endcond
        elif len(input_list) == 2 and input_list[0] == "###" and input_list[1].lower() == "endcond":
            w_enable_n = True
        if w_enable == True:
            if args.dry_run:
                print(line.strip("\n"))
            else:
                output_script_handle.write(line)
        if w_enable == False:
            w_enable = w_enable_n

    if not args.dry_run:
        output_script_handle.close()
    input_script_handle.close()
    return output_script_path

def gen_riscv_dv_gen_csr_file(iteration = 1):
    try:
        template_handle = open(template_path, "r")
        tlines = template_handle.readlines()

        file_handle = open(os.path.join(args.output) + "riscv_csr_test_{}.S".format(iteration), "r")
        lines = file_handle.readlines()
        file_handle.close()

        file_handle = open(os.path.join(args.output) + "riscv_csr_test_{}.S".format(iteration), "w")
        write_next = 0
        twrite_next = 0
        for line in lines:
            if write_next == 1 and line.strip("\n") != "csr_pass:":
                file_handle.write(line)
            elif line.strip("\n") == "_start:":
                for tline in tlines:
                    if tline.strip("\n") != "_start0:":
                        file_handle.write(tline)
                    elif tline.strip("\n") == "_start0:":
                        file_handle.write(tline)
                        break
                write_next = 1;
            elif line.strip("\n") == "csr_pass:":
                write_next = 0;
                for tline in tlines:
                    if tline.strip("\n") == "_start0:" and twrite_next == 0:
                        twrite_next = 1
                    elif twrite_next == 1:
                        file_handle.write(tline)
                break
        file_handle.close()
        template_handle.close()
    except Exception as e:
        print("error: exception in 'gen_riscv_dv_gen_csr_file'")
        print(e)

def preprocess_yaml_m4(enabled_features, input_script_path, output_script_handle):
    args_pre  = ['m4', '-G', '-E']  # Turn off GNU extensions, promote warnings to errors
    args_post = [input_script_path]
    args_mid  = []

    # Set defines for the preprocessing
    for key, val in enabled_features.items():
        dname = str(key).upper()
        dval  = str(int(val))
        args_mid.append('-D')
        args_mid.append(dname + '=' + dval)

    # Run the preprocessing
    args = args_pre + args_mid + args_post
    print('running m4 as: ' + str(args))
    proc_results = subprocess.run(args, stdout=output_script_handle)

    if proc_results.returncode != 0:
        print("error: m4 preproc returned error status", file=sys.stderr)
        exit(1)

if args.dry_run:
    preprocess_yaml()
else:
    run_riscv_dv_gen_csr_script(preprocess_yaml())
    for iteration in range(int(args.iterations)):
        gen_riscv_dv_gen_csr_file(iteration)
