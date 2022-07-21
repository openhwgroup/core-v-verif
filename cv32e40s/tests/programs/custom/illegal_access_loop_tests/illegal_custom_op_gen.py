func6 = {35, 51} # usermode underprivileged function code
outer_loop = 2048 # 2^11
inner_loop = 32 #2^5

opcode = 115

input_string = "// This is the start of the generated code" # string to look for to start writing to file
pointer = 0 # file pointer 
filename = "illegal_custom.S" # file which will be written to 

def generator():
    num_lines = 0
    f.seek(pointer)
    for func in func6:
        funcs = func << 26
        for i in range(outer_loop):
            bini = i << 15
            for j in range(inner_loop):
                binj = j << 7
                h = (funcs | bini | binj | opcode)
                num_lines += 1
                f.write(".word(" + hex(h) + ")" + "\n")
    f.write("//end of generated code\n")
    f.write("\n")
    f.write("j end_handler_ret")
    return num_lines


with open(filename, "r+") as f:
    while f.readline().strip("\n") != input_string:
        pass
    pointer = f.tell()
    num_lines = generator()

print(num_lines, "lines written to file '" + filename + "'")

""" 

f = open("Illegal_custom_test.txt", "w")

for func in func6:
    funcs = func << 26
    for i in range(outer_loop):
        bini = i << 15
        for j in range(inner_loop):
            binj = j << 7
            h = (funcs | bini | binj | opcode)
            if i == outer_loop-1 and j == inner_loop-1 and func == 51:

                f.write(".word(" + hex(h) + ")")
            else:
                f.write(".word(" + hex(h) + ")" + "\n")



# check and print the number of generated commands
f = open("Illegal_custom_test.txt", "r")
lines = f.read().split("\n")
instr = 0
for line in lines:
    instr += 1

print(instr, "lines written to file.")
 """