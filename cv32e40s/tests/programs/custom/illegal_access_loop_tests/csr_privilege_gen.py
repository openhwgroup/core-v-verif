"""
script to generate the csr_register_loop

"""

input_string = "// Start of generated code." # start string, this will move the wrie HEAD
pointer = 0 # file pointer 
filename = "csr_privilege_loop.S" # file which will be written to 


# register list fetched manually from the spec (V20211203), contains all U-, S-, R-, and M-mode CSR registers
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
    string_split = string_split[1:-1]
    f.seek(pointer)
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


with open(filename, "r+") as f:
    while f.readline().strip("\n") != input_string: # place header after input_string
        pass
    pointer = f.tell()
    num_lines = generator()
    f.truncate() # removes all lines after the last generated line

print(num_lines, "lines written to file '" + filename + "'") # user info

