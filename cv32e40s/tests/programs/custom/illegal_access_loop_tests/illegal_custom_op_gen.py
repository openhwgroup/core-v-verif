func6 = {35, 51} # usermode underprivileged function code
outer_loop = 2048 # 2^11
inner_loop = 32 #2^5

opcode = 115

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

f.close()


# check and print the number of generated commands
f = open("Illegal_custom_test.txt", "r")
lines = f.read().split("\n")
instr = 0
for line in lines:
    instr += 1

print(instr, "lines written to file.")