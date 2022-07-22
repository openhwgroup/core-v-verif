"""
script to generate the csr_register_loop

"""

input_string = "// Start of generated code" # start string, this will move the wrie HEAD
pointer = 0 # file pointer 
filename = "illegal_mcounteren_test.S" # file which will be written to 


# register list fetched manually from the spec (V20211203), contains all U-, S-, R-, and M-mode CSR registers
reg_str = """
0xC00-0xC1F
"""

def generator():
    """  
    This is the function which generates the commands. It attempts to read cycle, time, instret and all mhpmcounter registers. 
    """
    num_lines = 0 # printed later to help debugging, and assertion checks in C.
    string_split = (reg_str.split("\n"))
    string_split = string_split[1:-1]
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
    f.write("//end of generated code")
    return num_lines


with open(filename, "r+") as f:
    while f.readline().strip("\n") != input_string: # place header after input_string
        pass
    pointer = f.tell()
    num_lines = generator()
    f.truncate() # removes all lines after the last generated line

print(num_lines, "lines written to file '" + filename + "'") # user info