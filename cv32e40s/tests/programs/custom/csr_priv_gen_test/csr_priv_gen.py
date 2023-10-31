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
** This script generates four csr-instructions for every csr-register according to the 'reg_str'. This is then written directly to the 'csr_privilege_loop.S' 
**
*******************************************************************************
"""

#   Filenames
headername = "csr_priv_gen_test.h" # name of the header file that will be written to
filename = "csr_priv_loop.S" # file which will be written to 


#   Trigger strings
input_string = "// Start of generated code." # start string. This tells the script what to look for and moves the write HEAD to the right line
header_string = "//start of the function header" # Header start string


#   Global variables
pointer = 0 # file pointer 
num_lines = 0 # number of lines written to file


#   Register list which is used to generate the instructions.
#   List fetched manually from the spec (V20211203), contains all S-, R-, and M-mode CSR registers
reg_str = """
0x100-0x1FF
0x500-0x57F
0x580-0x5BF
0x5C0-0x5FF
0x900-0x97F
0x980-0x9BF
0x9C0-0x9FF
0xD00-0xD7F
0xD80-0xDBF
0xDC0-0xDFF
0x200-0x2FF
0x600-0x67F
0x680-0x6BF
0x6C0-0x6FF
0xA00-0xA7F
0xA80-0xABF
0xAC0-0xAFF
0xE00-0xE7F
0xE80-0xEBF
0xEC0-0xEFF
0x300-0x3FF
0x700-0x77F
0x780-0x79F
0x7A0-0x7AF
0x7B0-0x7BF
0x7C0-0x7FF
0xB00-0xB7F
0xB80-0xBBF
0xBC0-0xBFF
0xF00-0xF7F
0xF80-0xFBF
0xFC0-0xFFF
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
    string_split = string_split[1:-1] # removes empty lines before and after the string_split command
    f.seek(pointer) # set write  HEAD 
    for register in string_split:
        ranges = register.split("-")
        rstart = int(ranges[0], 16) # int(x, 16) converts to hex repr.
        rend = int(ranges[1], 16)
        for i in range(rstart, rend+1):
            num_lines += 4
            h = hex(i)
            f.write("csrrs  t0, " + h + ", x0 " + "\n")
            f.write("csrrw  x0, " + h + ", t0 " + "\n")
            f.write("csrrs  x0, " + h + ", t0 " + "\n")
            f.write("csrrc  x0, " + h + ", t0 " + "\n")
    f.write("j end_handler_ret\n")
    f.write("\n")
    f.write("//end of generated code")
    return num_lines

def header_generator():
    """
    Works the same as the generator function but on a smaller scale. Looks for the 'header_string' and then rewrites the lines below with the update 'num_lines' value
    """
    f.seek(pointer)
    f.write("// Number of illegaly generated lines as reported by the 'csr_privilege_gen.py'\n")
    f.write("#define ILLEGALLY_GENERATED_INSN " + str(num_lines) + "\n")
    f.write("\n")
    f.write("#endif")


#   File openers. They run through the file line by line and looks for the start string. They then update the global pointer value for the write HEAD

with open(filename, "r+") as f:
    while f.readline().strip("\n") != input_string: # place header after input_string
        pass
    pointer = f.tell() # Save pointer location to set proper HEAD position in generator()
    num_lines = generator()
    f.truncate() # removes all lines after the last generated line

with open(headername, "r+") as f:
    while f.readline().strip("\n") != header_string: # place HEAD after input_string
        pass
    pointer = f.tell()
    header_generator()
    f.truncate() # removes all lines after the last generated line


#   Print user info to terminal 

print(num_lines, "lines written to file '" + filename + "'") 
print("Also changed 'ILLEGALLY_GENERATED_INSN' value to " + str(num_lines) + " in the '" + headername + "' file") 

