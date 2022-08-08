"""
**
** Copyright 2022 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
** https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*******************************************************************************
**
** This script generates four csr-instructions for every csr-register according to the 'reg_str'. This is then written directly to the 'csr_privilege_loop.S' 
**
*******************************************************************************
"""


input_string = "// Start of generated code." # start string, this will move the wrie HEAD
header_string = "//start of the function header" # start string which the script looks for
header_val = "ILLEGALLY_GENERATED_INSN" # value which gets changed
pointer = 0 # file pointer 
headername = "csr_priv_gen_test.h" # name of the header file
num_lines = 0 # numebr of lines written to file
filename = "csr_privilege_loop.S" # file which will be written to 


# register list fetched manually from the spec (V20211203), contains all S-, R-, and M-mode CSR registers
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

def generator():
    """  
    This is the function which generates the csr_commands. It attempts to Read, Write, Clear and Set for every CSR in the list above. 
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

def header_gen():
    f.seek(pointer)
    f.write("// Number of illegaly generated lines as reported by the 'csr_privilege_gen.py'\n")
    f.write("#define ILLEGALLY_GENERATED_INSN " + str(num_lines) + "\n")
    f.write("\n")
    f.write("#endif")

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
    header_gen()
    f.truncate() # removes all lines after the last generated line


print(num_lines, "lines written to file '" + filename + "'") # user info
print("Also changed " + header_val + " value to " + str(num_lines) + " in the '" + headername + "' file") # user info

