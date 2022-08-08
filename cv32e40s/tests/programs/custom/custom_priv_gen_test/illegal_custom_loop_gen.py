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
** Script which generates the usermode custom instructions, to check illegal access. Instructions are written directly to the 'illegal_custom_loop.S' file after the 'input_string' declared below.
**
*******************************************************************************
"""

func6 = {35, 51} # 'funct6' bit-field codes: 100011, 110011
outer_loop = 2048 # 'custom11' bit-field range (2^11)
inner_loop = 32 # 'custom5' bit-field range (2^5)
# ref Figure 3.30: SYSTEM instruction encodings designated for custom use (PRIVSPEC V20211203)

opcode = 115 # SYSTEM OPCODE 1110011

input_string = "// This is the start of the generated code" # start string to move write HEAD.
header_string = "//start of the function header" # start string script looks for
header_val = "ILLEGALLY_GENERATED_INSN" # value which gets changed
pointer = 0 # file pointer 
headername = "custom_priv_gen_test.h" # name of the header file
num_lines = 0 # numebr of lines written to file
filename = "illegal_custom_loop.S" # file which will be written to 

def generator():
    """ 
    This function generates the executions according to the values in the first three lines. It loops and creates the 32-bit custom word by using the logical 'or' function on the four distinct fields (funct3 is always '000'). Writes each line directly to the assembly file listed above. 
    """
    num_lines = 0
    f.seek(pointer)
    for func in func6:
        funcs = func << 26 # bitshift according to position
        for i in range(outer_loop):
            bini = i << 15
            for j in range(inner_loop):
                binj = j << 7
                h = (funcs | bini | binj | opcode)
                num_lines += 1 # inform about num. instructions for easier debugging. 
                f.write(".word(" + hex(h) + ")" + "\n")
                
    # These lines are manually added at the end 
    f.write("j end_handler_ret\n")
    f.write("\n")
    f.write("//end of generated code")
    return num_lines

def header_gen():
    f.seek(pointer)
    f.write("// Number of illegaly generated lines as reported by the 'illegal_mcounteren_loop_gen.py'\n")
    f.write("#define ILLEGALLY_GENERATED_INSN " + str(num_lines) + "\n")
    f.write("\n")
    f.write("#endif")




with open(filename, "r+") as f:
    while f.readline().strip("\n") != input_string:
        pass
    pointer = f.tell() # set file header at line after input_string
    num_lines = generator() # generate code
    f.truncate() # remove all lines after the generated ones.


with open(headername, "r+") as f:
    while f.readline().strip("\n") != header_string: # place HEAD after input_string
        pass
    pointer = f.tell()
    header_gen()
    f.truncate() # removes all lines after the last generated line


print(num_lines, "lines written to file '" + filename + "'") # user info
print("Also changed " + header_val + " value to " + str(num_lines) + " in the '" + headername + "' file") # user info

