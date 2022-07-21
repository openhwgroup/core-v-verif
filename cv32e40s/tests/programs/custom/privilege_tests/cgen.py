import re as re 

h = "mstatus"
pointer = 0

input_string = "// Start of generated code here"

def generatecode():
    f.seek(pointer)
    for i in range(30):
        h = hex(i)
        f.write("csrrs  t0, " + h + ", x0 " + "\n")
        f.write("csrrw  x0, " + h + ", t0 " + "\n")
        f.write("csrrs  x0, " + h + ", t0 " + "\n")
    f.write("//end of generated code\n")
    f.write("\n")
    f.write("j end_handler_ret")

filename = "dummy.c"

with open(filename, "r+") as f:
    while f.readline().strip("\n") != input_string:
        pass
    pointer = f.tell()
    generatecode()

