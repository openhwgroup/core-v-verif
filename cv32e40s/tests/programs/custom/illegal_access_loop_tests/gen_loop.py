"""
script to generate the csr_register_loop

"""

"""
practice_dict = {} # might need this ? 

f = open("csr_loop_test.txt", "w")


for i in range(256, 4096):
    h = hex(i)
    f.write("csrrs  t0, " + h + ", x0 " + "\n")
    f.write("csrrw  x0, " + h + ", t0 " + "\n")
    f.write("csrrs  x0, " + h + ", t0 " + "\n")
    f.write("csrrc  x0, " + h + ", t0 " + "\n")
    f.write("\n")

"""

# register list fetched manually, contains all U-, S-, R-, and M-mode CSR registers
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

# generate the register
f = open("csr_loop_test.txt", "w")
string_split = (reg_str.split("\n"))
string_split = string_split[1:-1]

for register in string_split:
    ranges = register.split("-")
    rstart = int(ranges[0], 16)
    rend = int(ranges[1], 16)
    for i in range(rstart, rend+1):
        h = hex(i)
        if i == 4095:
            f.write("csrrs  t0, " + h + ", x0 " + "\n")
            f.write("csrrw  x0, " + h + ", t0 " + "\n")
            f.write("csrrs  x0, " + h + ", t0 " + "\n")
            f.write("csrrc  x0, " + h + ", t0")
        else:
            f.write("csrrs  t0, " + h + ", x0 " + "\n")
            f.write("csrrw  x0, " + h + ", t0 " + "\n")
            f.write("csrrs  x0, " + h + ", t0 " + "\n")
            f.write("csrrc  x0, " + h + ", t0 " + "\n")

f.close()


# check and print the number of generated commands
f = open("csr_loop_test.txt", "r")
lines = f.read().split("\n")
instr = 0
for line in lines:
    instr += 1

print(instr, "lines written to file.")