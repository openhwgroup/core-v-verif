""" 
** Copyright 2022 OpenHW Group
**
** SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
** Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
** with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
**                                        https://solderpad.org/licenses/SHL-2.1/
** Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
** an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
** specific language governing permissions and limitations under the License.
*******************************************************************************
**
** Script to generate access instructions based on 'reg_str' below. Places them in the 'illegal_mcounteren_test.S' file. 
**
*******************************************************************************
 """

#   Filenames
filename = "mcounteren_priv_gen_test.S" # file which will be written to 
headername = "mcounteren_priv_gen_test.h" # name of the header file


#   Trigger strings
input_string = "// Start of generated code" # start string, this will move the wrie HEAD
header_string = "#define MCOUNTEREN_DEFAULT_VAL 0x0" # start string script looks for


#   Global variables
pointer = 0 # file pointer 
num_lines = 0 # numebr of lines written to file


#   Register list which is used to generate the instructions
#   List fetched manually from the spec (V20211203), contains all S-, R-, and M-mode CSR registers
reg_str = """
0xC00-0xC1F
"""


#   Generator files below. They get the appropriate starting line from the file openers and generate the instructions.

def generator():
    """  
    It splits the 'reg_str' value line by line (also removes empty lines), then converts to base 16 and creates a range from the two numbers.
    It loops through this range and writes the numbers (in hex print format) into the assembly file.  
    After looping through the list it writes some standard lines.
    """
    num_lines = 0 # printed later to help debugging, and assertion checks in C.
    string_split = (reg_str.split("\n"))
    string_split = string_split[1:-1] # removes empty lines after the string_split command
    f.seek(pointer)
    for register in string_split:
        ranges = register.split("-")
        rstart = int(ranges[0], 16) # int(x, 16) converts to hex repr.
        rend = int(ranges[1], 16)
        for i in range(rstart, rend+1):
            num_lines += 1
            h = hex(i)
            f.write("csrrs  t0, " + h + ", x0 " + "\n")
    f.write("j end_handler_ret\n")
    f.write("\n")
    f.write("// end of generated code")
    return num_lines

def header_gen():
    """
    Works the same as the generator function but on a smaller scale. Looks for the 'header_string' and then rewrites the lines below with the update 'num_lines' value
    """
    f.seek(pointer)
    f.write("// Number of illegaly generated lines as reported by the 'illegal_mcounteren_loop_gen.py'\n")
    f.write("#define ILLEGALLY_GENERATED_INSN " + str(num_lines) + "\n")
    f.write("\n")
    f.write("#endif")


#   File openers. They run through the file line by line and looks for the start string. They then update the global pointer value for the write HEAD

with open(filename, "r+") as f:
    while f.readline().strip("\n") != input_string: # place header after input_string
        pass
    pointer = f.tell()
    num_lines = generator()
    f.truncate() # removes all lines after the last generated line




with open(headername, "r+") as f:
    while f.readline().strip("\n") != header_string: # place HEAD after input_string
        pass
    pointer = f.tell()
    header_gen()
    f.truncate() # removes all lines after the last generated line


#   Print user info to terminal 

print(num_lines, "lines written to file '" + filename + "'") # user info
print("Also changed 'ILLEGALLY_GENERATED_INSN' value to " + str(num_lines) + " in the '" + headername + "' file") # user info