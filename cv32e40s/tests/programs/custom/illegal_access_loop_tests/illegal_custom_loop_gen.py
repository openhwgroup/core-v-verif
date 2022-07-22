func6 = {35, 51} # usermode underprivileged function codes
outer_loop = 2048 # 11-bit custom instruction
inner_loop = 32 # 5-bit custom instruction

opcode = 115 # SYSTEM

input_string = "// This is the start of the generated code" # start string to move HEAD.
pointer = 0 # file pointer 
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
    f.write("//end of generated code\n")
    f.write("\n")
    f.write("j end_handler_ret")
    return num_lines


with open(filename, "r+") as f:
    while f.readline().strip("\n") != input_string:
        pass
    pointer = f.tell() # set file header at line after input_string
    num_lines = generator() # generate code
    f.truncate() # remove all lines after the generated ones.

print(num_lines, "lines written to file '" + filename + "'")

