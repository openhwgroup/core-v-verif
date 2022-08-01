import sys
import os
import argparse
import subprocess
import yaml
import shlex

if (sys.version_info < (3,0,0)):
    print ('Requires python 3')
    exit(1)

try:
    default_core = os.environ['CV_CORE']
except KeyError:
    default_core = 'None'

topdir = os.path.abspath(os.path.join(os.path.dirname(os.path.realpath(__file__)), '..'))
parser = argparse.ArgumentParser()
parser.add_argument("--core",            help="Set the core to generate test for", choices=['cv32e40s', 'cv32e40x'])
parser.add_argument("--pmp_num_regions", help="Set number of Pmp regions",         choices=['0', '64'])
parser.add_argument("--clic_enable",     help="Enable clic support",               action="store_true")
parser.add_argument("--output",          help="Output path",                       type=str)
parser.add_argument("--iterations",      help="Number of generated tests",         type=str)

args = parser.parse_args()

# TODO fix
if (args.output == None or args.core == None):
    print("Error: no output path")
    exit(1)

print('{}'.format(args))
script_path   = os.path.join(topdir, '{}/vendor_lib/google/riscv-dv/scripts/gen_csr_test.py'.format(args.core.lower()))
file_path     = os.path.join(topdir, '{}'.format(args.core.lower()) + '/env/corev-dv/{}'.format(args.core.lower()) + '_csr_template.yaml')
template_path = os.path.join(topdir, './bin/templates/csr_access_test_template.S')

def run_riscv_dv_gen_csr_script():
    try:
        print(os.path.join(topdir, '{}/vendor_lib/google/riscv-dv/scripts/gen_csr_test.py'.format(args.core.lower())))
        print("{}".format(script_path))
        print("{}".format(file_path))
        script_args = { "csr_file"   : ' --csr_file {}'.format(file_path),
                        "xlen"       : ' --xlen 32',
                        "out"        : ' --out ' + args.output,
                        "iterations" : ' --iterations ' + args.iterations}
        subprocess.call(shlex.split("python3 " + script_path + script_args["csr_file"] + script_args["xlen"] + script_args["out"] + script_args["iterations"]))
    except Exception as e:
        print(e)

def gen_riscv_dv_gen_csr_file(iteration = 0):
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
        print(e)

run_riscv_dv_gen_csr_script()
for iteration in range(int(args.iterations)):
    gen_riscv_dv_gen_csr_file(iteration)
