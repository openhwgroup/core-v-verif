#!/usr/bin/env python3

###############################################################################
#
# Copyright (C) 2024 Dolhin Design
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
# either express or implied.
#
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier: Apache-2.0
#
###############################################################################

import argparse


def auto_int(x):
        return int(x, 0)

def main():
    parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)

    parser.add_argument('start_csr', type=auto_int)
    parser.add_argument('end_csr', type=auto_int)
    parser.add_argument('--check_reset_val', default=None, type=auto_int, nargs="+")

    args = parser.parse_args()

    tot_instr = (args.end_csr + 1 - args.start_csr)
    if args.check_reset_val:
        nb_reset_val = len(args.check_reset_val)
    else:
        nb_reset_val = 0

    for x in range (args.start_csr, args.end_csr + 1):
        if nb_reset_val > 1 and len(args.check_reset_val) > 0:
            print("")
            print("# check reset value")
            print("csrrc  x5,  0x{:03X}, x0".format(x))
            print("li     x30,  0x{:08x}, x0".format(args.check_reset_val.pop(0)))
            print("bne    x5,  x30, fail")
            print("")
        elif nb_reset_val == 1:
            print("")
            print("# check reset value")
            print("csrrc  x5,  0x{:03X}, x0".format(x))
            print("li     x30,  0x{:08x}, x0".format(args.check_reset_val.index(0)))
            print("bne    x5,  x30, fail")
            print("")
        elif nb_reset_val > 0:
            print("Warning: either one reset value for all registers should be entered, or one reset value per register. Required {}, Given {}".format(tot_instr, nb_reset_val))
            print("csrrc  x5,  0x{:03X}, x0  ".format(x))
        else:
            print("csrrc  x5,  0x{:03X}, x0  ".format(x))

        print("csrrc  x0,  0x{:03X}, x5  ".format(x))
        print("csrrci x0,  0x{:03X}, 0x0a".format(x))
        print("csrrs  x0,  0x{:03X}, x5  ".format(x))
        print("csrrsi x0,  0x{:03X}, 0x0a".format(x))
        print("csrrw  x0,  0x{:03X}, x0  ".format(x))
        print("csrrwi x0,  0x{:03X}, 0x0a".format(x))
        print("")

    print("Generated {} read instructions, {} write instructions, {} total instructions".format(tot_instr, 6*tot_instr, 7*tot_instr))

if __name__ == "__main__":
    main()
