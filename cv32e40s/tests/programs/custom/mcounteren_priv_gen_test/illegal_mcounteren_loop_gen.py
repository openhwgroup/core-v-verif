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
** Script to generate access instructions based on 'reg_str' below. Places them in the 'illegal_mcounteren_test.S' file. 
**
*******************************************************************************
 """

input_string = "// Start of generated code" # start string, this will move the wrie HEAD
header_string = "#define MCOUNTEREN_DEFAULT_VAL 0x0" # start string script looks for
header_val = "ILLEGALLY_GENERATED_INSN" # value which gets changed
pointer = 0 # file pointer 
filename = "illegal_mcounteren_test.S" # file which will be written to 
headername = "mcounteren_priv_gen_test.h" # name of the header file
num_lines = 0 # numebr of lines written to file
# register list fetched manually from the spec (V20211203), contains all S-, R-, and M-mode CSR registers
reg_str = """
0xC00-0xC1F
"""

def generator():
    """  
    This is the function which generates the commands. It attempts to read cycle, time, instret and all mhpmcounter registers. 
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
    f.seek(pointer)
    f.write("// Number of illegaly generated lines as reported by the 'illegal_mcounteren_loop_gen.py'\n")
    f.write("#define ILLEGALLY_GENERATED_INSN " + str(num_lines) + "\n")
    f.write("\n")
    f.write("#endif")


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


print(num_lines, "lines written to file '" + filename + "'") # user info
print("Also changed " + header_val + " value to " + str(num_lines) + " in the '" + headername + "' file") # user info