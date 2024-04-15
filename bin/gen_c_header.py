#!/usr/bin/env python3

################################################################################
#
# Copyright 2020 OpenHW Group
# Copyright 2020 Silicon Labs, Inc.
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
# SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0
#
################################################################################
#
# gen_c_header.py
#   Script that builds c header files from csr yaml descriptions
#
# Written with Python 3.6.5 on RHEL 7.  Your python mileage may vary.
#
################################################################################
import sys
import yaml
import argparse
import random
import copy
import distutils.util

# YAML reuirements:
# No special characters, e.g. "[" in csr names, filed names or value names

def gen_csr_defines(csr_file, xlen, core_name, args):
    # Print guard
    print("#ifndef %s_H_" % core_name)
    print("#define %s_H_" % core_name)

    rv_string = "rv{}".format(str(xlen))
    csrs = {}
    with open(csr_file, "r") as c:
        csr_description = yaml.safe_load(c)

        if args.headers == 1:
            for csr_dict in csr_description:
                csr_name = csr_dict.get("csr")
                csr_address = csr_dict.get("address")
                csr_desc = csr_dict.get("description")
                csr_priv = csr_dict.get("privilege_mode")
                csr_field_list = csr_dict.get(rv_string)

                print("\n/* %s : %s */" % (csr_name.upper(), csr_desc.strip("\n")))
                csr_reg_mask = 0
                csr_reg_resetval = 0
                csr_reg_resetval_unknown = 0

                for csr_field_detail_dict in csr_field_list:
                    field_type = csr_field_detail_dict.get("type")
                    field_name = csr_field_detail_dict.get("field_name")
                    field_desc = csr_field_detail_dict.get("description")
                    field_resetval = csr_field_detail_dict.get("reset_val")
                    field_msb = csr_field_detail_dict.get("msb")
                    field_lsb = csr_field_detail_dict.get("lsb")
                    field_mask = (2**(field_msb-field_lsb+1)-1) << field_lsb
                    field_width = field_msb-field_lsb+1

                    if(str(field_resetval).upper() == "UNKNOWN"):
                        csr_reg_resetval_unknown = 1

                    # Print defines for bitfield
                    if field_type != "WPRI":
                        csr_reg_mask |= field_mask

                        if (field_width == 1):
                            print("#define CSR_%s_%s (0x1U << %s)" % (csr_name.upper(), field_name.upper(), field_lsb))
                            print("#define _CSR_%s_%s_SHIFT %d" % (csr_name.upper(), field_name.upper(), field_lsb))
                            print("#define _CSR_%s_%s_MASK 0x%XU" % (csr_name.upper(), field_name.upper(), field_mask))
                        if(str(field_resetval).upper() != "UNKNOWN"):
                            print("#define _CSR_%s_%s_DEFAULT 0x%.8XU" % (csr_name.upper(), field_name.upper(), field_resetval))
                            csr_reg_resetval |= field_resetval << field_lsb
                        try:
                            # Check for enums
                            for name,val in csr_field_detail_dict.get("values").items():
                                print("#define _CSR_%s_%s_%s 0x%xU" % (csr_name.upper(), field_name.upper(), name.upper(), val))
                                print("#define CSR_%s_%s_%s (0x%xU << %d)" % (csr_name.upper(), field_name.upper(), name.upper(), val, field_lsb))
                        except:
                            # No enums for this bitfield, do nothing
                            pass
                        print("")

                print("#define CSR_%s 0x%.3XU" % (csr_name.upper(), csr_address))
                print("#define _CSR_%s_MASK 0x%.8XU" % (csr_name.upper(), csr_reg_mask))
                if(csr_reg_resetval_unknown == 0):
                    print("#define _CSR_%s_RESETVALUE 0x%.8XU" % (csr_name.upper(), csr_reg_resetval))

        if args.csr_addr_list == 1:
            print("")
            for csr_dict in csr_description:
                csr_name = csr_dict.get("csr").upper()
                csr_addr = csr_dict.get("address")
                csr_field_list = csr_dict.get(rv_string)
                max_string_length = 16
                output_string = "#define {:<{}} 0x{:03X}".format(csr_name.upper(), max_string_length, csr_addr)
                print(output_string)

        if args.bitfields == 1:
            print("")
            for csr_dict in csr_description:
                csr_name = csr_dict.get("csr").lower()
                if (not csr_name[-1:].isnumeric() and not csr_name[-2:-1].isnumeric()) \
                or (csr_name[-1:] == "0" and not csr_name[-2:-1].isnumeric()) \
                or (csr_name[-2:-1] == "0" and not csr_name[-1:].isnumeric()):
                    csr_name = csr_name.replace('0', '')
                    csr_field_list = csr_dict.get(rv_string)
                    print("")
                    print("typedef union {")
                    max_field_length = 0
                    field_subtype = None
                    field_subtype_old = None
                    has_subtype = False
                    for csr_field_detail_dict in reversed(csr_field_list):
                        field_name = csr_field_detail_dict.get("field_name")
                        field_length = len(field_name)
                        max_field_length = field_length if field_length > max_field_length else max_field_length

                    for i in reversed(range(0, len(csr_field_list))):
                        indent = "    "
                        field_size = (csr_field_list[i].get("msb") - csr_field_list[i].get("lsb") + 1)
                        field_name = csr_field_list[i].get("field_name")
                        field_subtype = csr_field_list[i].get("subtype")

                        if field_subtype != field_subtype_old and field_subtype_old is None and field_subtype is not None:
                            indent = "      "
                            print("  union {")
                            print("    struct {")
                        elif field_subtype != field_subtype_old and field_subtype_old is not None and field_subtype is not None:
                            indent = "      "
                            print("    } __attribute__((packed)) volatile %s;" % field_subtype_old)
                            print("    struct {")
                        elif field_subtype is None and i == len(csr_field_list)-1:
                            print("  struct {")

                        field_subtype_old = field_subtype
                        indent = "      "
                        output_string = "{}volatile uint32_t {:<{}} : {:>};".format(indent, field_name.lower(), max_field_length, field_size)
                        print(output_string)
                        if i == 0 and field_subtype_old is not None:
                            print("    } __attribute__((packed)) volatile %s;" % field_subtype)

                    print("  } __attribute__((packed)) volatile fields;")
                    print("  volatile uint32_t raw;")
                    print("} __attribute__((packed)) volatile %s_t;" % csr_name)
                    print("")

    print("\n#endif // %s_H_" % core_name)

def main():

    # define command line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("--csr_file", type=str,
                        default="yaml/csr_template.yaml",
                        help="The YAML file contating descriptions of all processor supported CSRs")
    parser.add_argument("--core_name", type=str,
                        default="CV32E40X",
                        help="Name of the core. Used to generate guard in header")
    parser.add_argument("--xlen", type=int, default=32,
                        help="Specify the ISA width, e.g. 32 or 64 or 128")
    parser.add_argument("--headers", dest='headers', type=lambda x:bool(distutils.util.strtobool(x)), default=0,
                        help="Generate bitfield masks")
    parser.add_argument("--bitfields", dest='bitfields', type=lambda x:bool(distutils.util.strtobool(x)), default=1,
                        help="Generate bitfield unions")
    parser.add_argument("--csr_addr_list", dest='csr_addr_list', type=lambda x:bool(distutils.util.strtobool(x)), default=1,
                        help="Generate address list defines")
    args = parser.parse_args()

    gen_csr_defines(args.csr_file, args.xlen, args.core_name, args);


if __name__ == "__main__":
    main()

